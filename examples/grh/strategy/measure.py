"""Measure project-local sources from each reduction entry using the repository's Lean lexer."""
import json
import sys
from pathlib import Path
from leanreducer.source import Corpus

root = Path(sys.argv[1])
corpus = Corpus(root, ["Mathlib", "Lean", "Std", "Init"])
for entry in ["New.Data.DataExist", "RHCutoffData", "RHCutoffCompatibility", "FixedClass",
              "FixedClassSupply", "RHOnly", "RHWindow", "RHNormalized", "RHNormalizedSupply"]:
    sizes = corpus.size(corpus.walk(entry))
    print(entry, json.dumps(sizes))
increment = corpus.walk("RHNormalizedSupply") - corpus.walk("RHNormalized")
print("Additional source in the current normalized proof", json.dumps(corpus.size(increment)))
