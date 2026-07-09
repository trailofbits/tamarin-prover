{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- A content-addressed, append-only log for spilled proof state.
--
-- Every value is written once, as one record:
--
--   > [kind : 1B][ref : 64B hex][len : 8B BE][payload]
--
-- The 'Ref' is the SHA-256 of the value's binary encoding (salted with its
-- 'Kind' so two types can't collide). It's stored in the record itself, so
-- rebuilding the index on load is one scan, no re-hashing. Use 'dumpStoreJSON'
-- to get a readable JSON view.
--
-- Writes are write-through: append it, forget it, never keep it in the heap.
-- The only thing we hold onto is the set of refs we've already seen.
--
-- Everything hangs off one global, 'globalStore', because the prover is pure
-- and there's no IO seam to pass a handle through. 'initStore' sets it up
-- once at the CLI layer.
module Theory.Constraint.Solver.Store
  ( Ref
  , refText
  , Kind(..)
  , initStore
  , closeStore
  , writeOnce
  , storeSystem
  , readSystemLiveMaybe
  , dumpStoreJSON
  ) where

import           Theory.Constraint.System
import           Theory.Model
import           Theory.Constraint.Solver.JSON ()   -- ToJSON for the System closure
import           Control.DeepSeq         (NFData (rnf))

import           Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import           Control.Exception       (evaluate)
import           Control.Monad           (unless)
import           Crypto.Hash             (Digest, SHA256, hashlazy)
import           Data.Aeson              (ToJSON, object, (.=))
import qualified Data.Aeson              as A
import qualified Data.Binary             as Bin
import qualified Data.ByteString         as BS
import qualified Data.ByteString.Lazy    as BL
import           Data.IORef              (IORef, newIORef, readIORef, writeIORef)
import           Data.Word               (Word64)
import           GHC.Generics            (Generic)
import qualified Data.Map                as M
import qualified Data.Set                as S
import qualified Data.Text               as T
import qualified Data.Text.Encoding      as TE
import qualified Extension.Data.Label    as L
import           System.Directory        (createDirectoryIfMissing)
import           System.FilePath         ((</>))
import           System.IO               (BufferMode (BlockBuffering), Handle,
                                          IOMode (ReadWriteMode),
                                          SeekMode (AbsoluteSeek), hClose,
                                          hFileSize, hSeek,
                                          hSetBuffering, openFile)
import           System.IO.Unsafe        (unsafePerformIO)

-- | Content address of a stored value: hex SHA-256 of its binary encoding.
newtype Ref = Ref T.Text
  deriving (Eq, Ord, Show)

refText :: Ref -> T.Text
refText (Ref t) = t

instance ToJSON Ref where toJSON (Ref t) = A.toJSON t

-- Refs live inside proof trees (via OnDisk markers), so they need NFData and
-- Binary too. Binary goes via UTF-8 bytes since the binary package has no
-- Text instance.
instance NFData Ref where rnf (Ref t) = rnf t
instance Bin.Binary Ref where
  put (Ref t) = Bin.put (TE.encodeUtf8 t)
  get = do
    bytes <- Bin.get
    pure (Ref (TE.decodeUtf8 bytes))

-- | What kind of thing a record holds, written as the "kind" tag so one log
-- can hold everything.
data Kind
  = KNode          -- ^ one element of '_sNodes' (a rule instance)
  | KGoal          -- ^ one key of '_sGoals'
  | KEdge          -- ^ one element of '_sEdges'
  | KLessAtom      -- ^ one element of '_sLessAtoms'
  | KFormulas      -- ^ a whole formula set ('_sFormulas' etc.)
  | KSubtermStore  -- ^ the whole '_sSubtermStore'
  | KEqStore       -- ^ the whole '_sEqStore'
  | KShell         -- ^ a spilled system (heavy fields as refs)
  deriving (Eq, Ord, Show, Enum, Bounded)

kindTag :: Kind -> T.Text
kindTag KNode         = "node"
kindTag KGoal         = "goal"
kindTag KEdge         = "edge"
kindTag KLessAtom     = "lessAtom"
kindTag KFormulas     = "formulas"
kindTag KSubtermStore = "subtermStore"
kindTag KEqStore      = "eqStore"
kindTag KShell        = "shell"

-- | The open log plus its dedup/index state. The MVar guards both: whoever
-- holds it can append or seek-and-read, so parallel search sparks can't
-- interleave writes or double-claim a ref.
data StoreCtx = StoreCtx
  { scFileHandle :: Handle  -- ^ one ReadWriteMode handle for both roles:
                            --   appends seek to the append offset, reads
                            --   ('readRecord') seek to a ref's offset
  , scState      :: MVar StoreState
  }

-- | One record's location in the log: byte offset and full framed length.
data Position = Position
  { posOffset :: !Word64
  , posLength :: !Word64
  }

-- | Every written ref with its record's position -- the dedup set and the
-- random-access index in one -- plus the append offset.
data StoreState = StoreState
  { ssPositions      :: M.Map Ref Position
  , ssAppendOffset   :: !Word64
  , ssAtAppendOffset :: !Bool  -- ^ file handle already at the append offset?
                               --   Appends only seek after a read moved the
                               --   handle ('hSeek' flushes the write buffer,
                               --   so a seek per append would defeat
                               --   buffering entirely)
  }

-- | Where the log lives on disk. Binary's the only format we store (we hash
-- the binary encoding anyway) -- use 'dumpStoreJSON' if you want JSON.
storePath :: FilePath -> FilePath
storePath dir = dir </> "store.bin"

-- | The process-global store. Nothing until 'initStore' runs. Has to be
-- global since the prover is pure and there's no seam to pass a handle
-- through.
{-# NOINLINE globalStore #-}
globalStore :: IORef (Maybe StoreCtx)
globalStore = unsafePerformIO (newIORef Nothing)

-- | Open the log under DIR and set up the global store. Call this once from
-- the CLI layer when eviction is turned on.
initStore :: FilePath -> IO ()
initStore dir = do
    existing <- readIORef globalStore
    case existing of
      Just _  -> error "initStore: store already initialized"
      Nothing -> do
        createDirectoryIfMissing True dir
        h <- openFile (storePath dir) ReadWriteMode
        hSetBuffering h (BlockBuffering Nothing)
        end <- fromIntegral <$> hFileSize h
        hSeek h AbsoluteSeek (fromIntegral end)
        state <- newMVar (StoreState M.empty end True)
        writeIORef globalStore (Just (StoreCtx h state))

-- | Close the log and drop the global. Fine to call even if the store was
-- never opened.
closeStore :: IO ()
closeStore = do
    existing <- readIORef globalStore
    case existing of
      Nothing  -> pure ()
      Just ctx -> do
        hClose (scFileHandle ctx)
        writeIORef globalStore Nothing

-- | Hash a value into its Ref: SHA-256 of the kind tag plus its binary
-- encoding. We mix in the kind because Binary doesn't tag types -- two
-- different types with the same shape (say Edge vs LessAtom) could otherwise
-- hash identically and alias each other's records.
refOfBytes :: Kind -> BL.ByteString -> Ref
refOfBytes kind bytes = Ref (T.pack (show digest))
  where
    digest = hashlazy (Bin.encode (kindTag kind) <> bytes) :: Digest SHA256

-- | Store a value and get back its Ref. Only appends a record the first time
-- we see this content -- duplicates just cost one hash, no I/O. The binary
-- encoding is computed once and shared by the hash and the on-disk payload.
writeOnce :: Bin.Binary a => Kind -> a -> IO Ref
writeOnce kind x = do
    let payload = Bin.encode x
        ref     = refOfBytes kind payload
    -- force ref (the hash) all the way before we touch the lock below --
    -- otherwise something forced inside the locked section could chase a
    -- lazy thunk into readSystemLive and deadlock on this same MVar
    _ <- evaluate ref
    existing <- readIORef globalStore
    case existing of
      Nothing  -> error "writeOnce: store not initialized (did you pass --evict?)"
      Just ctx -> modifyMVar (scState ctx) (claim ctx payload ref)
  where
    claim ctx payload ref st =
      if M.member ref (ssPositions st)
        then pure (st, ref)
        else do
          let framed   = encodeRecord kind ref payload
              len      = fromIntegral (BL.length framed)
              newState = st { ssPositions      = M.insert ref (Position (ssAppendOffset st) len) (ssPositions st)
                            , ssAppendOffset   = ssAppendOffset st + len
                            , ssAtAppendOffset = True
                            }
          unless (ssAtAppendOffset st) $
            hSeek (scFileHandle ctx) AbsoluteSeek (fromIntegral (ssAppendOffset st))
          BL.hPut (scFileHandle ctx) framed
          pure (newState, ref)

-- | Read one record's payload back by its Ref. Runs under the store lock
readRecord :: Ref -> IO BL.ByteString
readRecord ref = do
    _ <- evaluate ref
    existing <- readIORef globalStore
    case existing of
      Nothing  -> error "readRecord: store not initialized"
      Just ctx -> modifyMVar (scState ctx) (fetch ctx)
  where
    fetch ctx st =
      case M.lookup ref (ssPositions st) of
        Nothing  -> error ("readRecord: no record for ref " ++ T.unpack (refText ref))
        Just pos -> do
          hSeek (scFileHandle ctx) AbsoluteSeek (fromIntegral (posOffset pos))
          bytes <- BS.hGet (scFileHandle ctx) (fromIntegral (posLength pos))
          let newState = st { ssAtAppendOffset = False }
          pure (newState, BL.drop recordHeaderLen (BL.fromStrict bytes))

-- | Same as 'readSystemLive', but Nothing if no store is open 
readSystemLiveMaybe :: Ref -> IO (Maybe System)
readSystemLiveMaybe ref = do
    existing <- readIORef globalStore
    case existing of
      Nothing -> pure Nothing
      Just _  -> Just <$> readSystemLive ref

-- | Rebuild a System from its shell Ref, reading each field back from the
-- log. 
readSystemLive :: Ref -> IO System
readSystemLive shellRef = do
    sh       <- deref shellRef
    nodes    <- traverse deref (shNodes sh)
    goals    <- mapM derefGoal (shGoals sh)
    edges    <- mapM deref (shEdges sh)
    lessAts  <- mapM deref (shLessAtoms sh)
    subterms <- deref (shSubtermStore sh)
    eqStore  <- deref (shEqStore sh)
    formulas <- deref (shFormulas sh)
    solved   <- deref (shSolvedFormulas sh)
    lemmas   <- deref (shLemmas sh)
    pure System
      { _sNodes          = nodes
      , _sEdges          = S.fromList edges
      , _sLessAtoms      = S.fromList lessAts
      , _sLastAtom       = shLastAtom sh
      , _sSubtermStore   = subterms
      , _sEqStore        = eqStore
      , _sFormulas       = formulas
      , _sSolvedFormulas = solved
      , _sLemmas         = lemmas
      , _sGoals          = M.fromList goals
      , _sNextGoalNr     = shNextGoalNr sh
      , _sSourceKind     = shSourceKind sh
      , _sDiffSystem     = shDiffSystem sh
      }
  where
    deref :: Bin.Binary a => Ref -> IO a
    deref ref = do
        payload <- readRecord ref
        case decodePayload ref payload of
          Left err -> error ("readSystemLive: " ++ err)
          Right x  -> pure x

    derefGoal (r, status) = do
        g <- deref r
        pure (g, status)

-- | Bytes before the payload in a binary record: kind (1) + ref (64) + len (8).
recordHeaderLen :: Num a => a
recordHeaderLen = 73

-- | One binary record: @[kind : 1B][ref : 64B hex][len : 8B BE][payload]@.
encodeRecord :: Kind -> Ref -> BL.ByteString -> BL.ByteString
encodeRecord kind ref payload = BL.concat
    [ BL.singleton (fromIntegral (fromEnum kind))
    , BL.fromStrict (TE.encodeUtf8 (refText ref))
    , Bin.encode (fromIntegral (BL.length payload) :: Word64)
    , payload
    ]

-- storing a whole System (write side of the spill)

-- | Strip the display-only fields (ruleColor, ruleProcess) before hashing, so
-- rules that only differ in how they're displayed still dedup. Matches the
-- JSON instance, which drops the same two fields.
canonicalizeRule :: RuleACInst -> RuleACInst
canonicalizeRule rule = L.modify rInfo dropDisplay rule
  where
    dropDisplay (ProtoInfo info) = ProtoInfo (L.modify praciAttributes noDisplay info)
    dropDisplay (IntrInfo info)  = IntrInfo info
    noDisplay attrs = attrs { ruleColor = Nothing, ruleProcess = Nothing }

-- | A System with the heavy fields swapped for refs and the small scalars
-- kept inline -- this is what a spilled system looks like on disk. Same type
-- for Binary and JSON (instances below), so read and write can't drift apart.
data SystemShell = SystemShell
  { shNodes          :: M.Map NodeId Ref
  , shEdges          :: [Ref]
  , shLessAtoms      :: [Ref]
  , shLastAtom       :: Maybe NodeId
  , shSubtermStore   :: Ref
  , shEqStore        :: Ref
  , shFormulas       :: Ref
  , shSolvedFormulas :: Ref
  , shLemmas         :: Ref
  , shGoals          :: [(Ref, GoalStatus)]
  , shNextGoalNr     :: Integer
  , shSourceKind     :: SourceKind
  , shDiffSystem     :: Bool
  }
  deriving (Generic)

instance Bin.Binary SystemShell

-- JSON keys mirror the 'System' field names, so JSONL shells read naturally.
instance ToJSON SystemShell where
  toJSON sh = object
    [ "_sNodes"          .= shNodes sh
    , "_sEdges"          .= shEdges sh
    , "_sLessAtoms"      .= shLessAtoms sh
    , "_sLastAtom"       .= shLastAtom sh
    , "_sSubtermStore"   .= shSubtermStore sh
    , "_sEqStore"        .= shEqStore sh
    , "_sFormulas"       .= shFormulas sh
    , "_sSolvedFormulas" .= shSolvedFormulas sh
    , "_sLemmas"         .= shLemmas sh
    , "_sGoals"          .= shGoals sh
    , "_sNextGoalNr"     .= shNextGoalNr sh
    , "_sSourceKind"     .= shSourceKind sh
    , "_sDiffSystem"     .= shDiffSystem sh
    ]

-- | Store a System and return the Ref of its shell. The shell's own ref is a
-- hash of its encoding, and its parts are all refs too, so it's Merkle-ish.
storeSystem :: System -> IO Ref
storeSystem sys = do
    nodeRefs    <- traverse (writeOnce KNode) (_sNodes canonSys)
    goalRefs    <- mapM storeGoal (M.toList (_sGoals canonSys))
    edgeRefs    <- mapM (writeOnce KEdge)     (S.toList (_sEdges canonSys))
    lessRefs    <- mapM (writeOnce KLessAtom) (S.toList (_sLessAtoms canonSys))
    formulasRef <- writeOnce KFormulas     (_sFormulas canonSys)
    solvedRef   <- writeOnce KFormulas     (_sSolvedFormulas canonSys)
    lemmasRef   <- writeOnce KFormulas     (_sLemmas canonSys)
    subtermRef  <- writeOnce KSubtermStore (_sSubtermStore canonSys)
    eqRef       <- writeOnce KEqStore      (_sEqStore canonSys)
    let shell = SystemShell
          { shNodes          = nodeRefs
          , shEdges          = edgeRefs
          , shLessAtoms      = lessRefs
          , shLastAtom       = _sLastAtom canonSys
          , shSubtermStore   = subtermRef
          , shEqStore        = eqRef
          , shFormulas       = formulasRef
          , shSolvedFormulas = solvedRef
          , shLemmas         = lemmasRef
          , shGoals          = goalRefs
          , shNextGoalNr     = _sNextGoalNr canonSys
          , shSourceKind     = _sSourceKind canonSys
          , shDiffSystem     = _sDiffSystem canonSys
          }
    writeOnce KShell shell
  where
    canonSys = sys { _sNodes = M.map canonicalizeRule (_sNodes sys) }
    storeGoal (goal, status) = do
        goalRef <- writeOnce KGoal goal
        pure (goalRef, status)

-- reading the log back (read side of the spill)

-- | A loaded log: kind + raw payload per Ref. We only decode a payload once
-- something actually asks for it, so loading itself stays cheap.
newtype StoreTables = StoreTables (M.Map Ref (Kind, BL.ByteString))

-- | Read store.bin back into StoreTables by splitting it into records. A torn
-- tail (process got killed mid-write) just gets dropped with a warning;
-- corruption anywhere else is a hard error locating the record.
loadStore :: FilePath -> IO StoreTables
loadStore dir = do
    bytes   <- BL.readFile (storePath dir)
    records <- collect (0 :: Int) bytes
    pure (StoreTables (M.fromList records))
  where
    collect _ rest | BL.null rest = pure []
    collect n rest
      | BL.length header < recordHeaderLen || BL.length payload < fromIntegral len = do
          putStrLn ("loadStore: dropping torn final record (record " ++ show n ++ ")")
          pure []
      | otherwise = do
          restRecords <- collect (n + 1) rest'
          pure ((ref, (kind, payload)) : restRecords)
      where
        (header, body)    = BL.splitAt recordHeaderLen rest
        (kindB, afterK)   = BL.splitAt 1 header
        (refB, lenB)      = BL.splitAt 64 afterK
        len               = Bin.decode lenB :: Word64
        (payload, rest')  = BL.splitAt (fromIntegral len) body
        ref               = Ref (TE.decodeUtf8 (BL.toStrict refB))
        kindByte          = fromIntegral (BL.head kindB)
        kind = if kindByte <= fromEnum (maxBound :: Kind)
                 then toEnum kindByte
                 else error ("loadStore: unknown kind byte " ++ show kindByte
                             ++ " at record " ++ show n)

-- | Decode a payload to a concrete type.
decodePayload :: Bin.Binary a => Ref -> BL.ByteString -> Either String a
decodePayload ref b = case Bin.decodeOrFail b of
    Right (_, _, x)  -> Right x
    Left (_, _, err) -> Left ("binary decode of " ++ T.unpack (refText ref)
                              ++ ": " ++ err)

-- | Write a readable DIR/store.jsonl next to DIR/store.bin, one
-- {"kind","id","content"} line per record. Works any time, even on a crashed
-- run's store. Returns the path.
dumpStoreJSON :: FilePath -> IO FilePath
dumpStoreJSON dir = do
    StoreTables table <- loadStore dir
    let out = dir </> "store.jsonl"
    BL.writeFile out (BL.concat (map jsonLine (M.toList table)))
    pure out
  where
    jsonLine (ref, (kind, payload)) =
        A.encode (object [ "kind"    .= kindTag kind
                         , "id"      .= ref
                         , "content" .= content kind payload ]) <> "\n"
    content kind p = case kind of
      KNode         -> A.toJSON (dec p :: RuleACInst)
      KGoal         -> A.toJSON (dec p :: Goal)
      KEdge         -> A.toJSON (dec p :: Edge)
      KLessAtom     -> A.toJSON (dec p :: LessAtom)
      KFormulas     -> A.toJSON (dec p :: S.Set LNGuarded)
      KSubtermStore -> A.toJSON (dec p :: SubtermStore)
      KEqStore      -> A.toJSON (dec p :: EqStore)
      KShell        -> A.toJSON (dec p :: SystemShell)
    dec :: Bin.Binary a => BL.ByteString -> a
    dec p = Bin.decode p
