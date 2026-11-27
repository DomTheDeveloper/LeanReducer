"""Measure project-local sources from each reduction entry using the repository's Lean lexer."""
import json
import sys
from pathlib import Path
from leanreducer.source import Corpus

root = Path(sys.argv[1])
corpus = Corpus(root, ["Mathlib", "Lean", "Std", "Init"])
for entry in ["New.Data.DataExist", "RHCutoffData", "RHCutoffCompatibility", "FixedClass",
              "FixedClassSupply", "RHOnly", "RHWindow", "RHNormalized", "RHNormalizedSupply", "RHFiniteGain"]:
    sizes = corpus.size(corpus.walk(entry))
    print(entry, json.dumps(sizes))
increment = corpus.walk("RHNormalizedSupply") - corpus.walk("RHNormalized")
print("Additional source in the current normalized proof", json.dumps(corpus.size(increment)))

base = corpus.walk("RHFiniteGain")
for name, modules in {
    "determinant": ["New.Heights.OneDeterminant"],
    "moments": ["New.Filling.Moments"],
    "determinant_and_moments": ["New.Heights.OneDeterminant", "New.Filling.Moments"],
    "short_and_enough": ["New.Endgame.ShortAndEnough"],
    "long_forms": ["New.Endgame.LongForms"],
}.items():
    reached = base.union(*(corpus.walk(module) for module in modules))
    sizes = corpus.size(reached)
    print("Route", name, "total", sizes["code"], "extra", corpus.size(reached - base)["code"],
          "strict budget", 49999 - sizes["code"])
