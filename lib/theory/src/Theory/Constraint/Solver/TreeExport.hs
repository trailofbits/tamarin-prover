{-# LANGUAGE OverloadedStrings #-}

-- |
-- Writes each lemma's proof tree to a small readable JSON file, one per
-- lemma: DIR/<lemma>.tree.json. 
--
--   { "lemma": ..., "quantifier": "all-traces", "status": "completeProof",
--     "root": {     "method":   "simplify" | {"solveGoal": {"ref": ..., "pretty": ...}} | ...,
--                   "system":   "<shell ref>" | null,
--                   "children": { "<case name>": <node>, ... } } }
module Theory.Constraint.Solver.TreeExport
  ( writeLemmaTrees
  ) where

import           Theory
import           Theory.Constraint.Solver.Store (Kind (KGoal), refText, writeOnce,
                                                 storeSystem)
import           Theory.Text.Pretty             (render)

import           Control.Exception              (evaluate)
import           Control.Parallel.Strategies    (parList, rdeepseq, using)
import           Data.Aeson                     (ToJSON (toJSON), Value, object, (.=))
import qualified Data.Aeson                     as A
import qualified Data.Label                     as L
import           System.Directory               (createDirectoryIfMissing)
import           System.FilePath                ((</>))

-- | Write DIR/<lemma>.tree.json for every lemma. Needs the store open since
-- goal refs get interned into it.
writeLemmaTrees :: FilePath -> ClosedTheory -> IO ()
writeLemmaTrees dir thy = do
    createDirectoryIfMissing True dir
    -- demand every lemma's proof in parallel (one spark each) before we write
    -- anything below. proofs are lazy, so doing this one at a time loses the
    -- overlap between lemmas 
    statuses <- evaluate (map lemmaStatus lems `using` parList rdeepseq)
    mapM_ (\(lem, status) -> writeOne lem status) (zip lems statuses)
  where
    lems = getLemmas thy
    lemmaStatus lem = statusText (foldProof proofStepStatus (L.get lProof lem))
    writeOne lem status = do
        rootNode <- nodeToJSON (L.get lProof lem)
        A.encodeFile (dir </> sanitize (L.get lName lem) ++ ".tree.json") $ object
          [ "lemma"      .= L.get lName lem
          , "quantifier" .= show (L.get lTraceQuantifier lem)
          , "status"     .= status
          , "root"       .= rootNode
          ]

nodeToJSON :: IncrementalProof -> IO Value
nodeToJSON (LNode step kids) = do
    method     <- methodToJSON (psMethod step)
    system     <- traverse systemRefText (psInfo step)
    childNodes <- traverse nodeToJSON kids
    pure $ object
      [ "method"   .= method
      , "system"   .= system
      , "children" .= childNodes
      ]
  where
    -- evicted nodes already have a ref
    systemRefText (OnDisk r)   = pure (refText r)
    systemRefText (InMem sys)  = refText <$> storeSystem sys

-- | Render an applied method as JSON. SolveGoal's payload is heavy, so it
-- becomes a store ref plus a pretty-printed string.
methodToJSON :: ProofMethod -> IO Value
methodToJSON (SolveGoal goal) = do
    ref <- writeOnce KGoal goal
    pure $ object ["solveGoal" .= object ["ref" .= refText ref, "pretty" .= render (prettyGoal goal)]]
methodToJSON Simplify           = pure (toJSON ("simplify" :: String))
methodToJSON Induction          = pure (toJSON ("induction" :: String))
methodToJSON (Sorry reason)     = pure $ object ["sorry" .= reason]
methodToJSON Invalidated        = pure (toJSON ("invalidated" :: String))
methodToJSON (Finished result)  = pure $ object ["finished" .= resultText result]
  where
    resultText Solved             = "solved" :: String
    resultText Unfinishable       = "unfinishable"
    resultText (Contradictory _)  = "contradiction"

statusText :: ProofStatus -> String
statusText CompleteProof      = "completeProof"
statusText TraceFound         = "traceFound"
statusText IncompleteProof    = "incompleteProof"
statusText UnfinishableProof  = "unfinishableProof"
statusText UndeterminedProof  = "undeterminedProof"
statusText InvalidatedProof   = "invalidatedProof"

sanitize :: String -> String
sanitize name = map (\c -> if c == '/' || c == ' ' then '_' else c) name
