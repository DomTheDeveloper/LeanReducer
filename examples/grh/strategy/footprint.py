"""Compare local proof-term references with the source closure of ordinary RH."""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from leanreducer.source import Corpus, lexical_lines

source, report, verification = map(Path, sys.argv[1:])
corpus = Corpus(source, ["Mathlib", "Lean", "Std", "Init"])
imports = corpus.walk("RHOnly")
changed = set(json.loads(verification.read_text())["cases"]["combined"]["kernel_replay"])
used, spans = Counter(), defaultdict(set)
missing_range = Counter()
flags = Counter()
names = set()
for line in report.read_text().splitlines():
    module, name, kind, start, stop = line.split("\t")
    if module not in imports:
        raise ValueError(f"unexpected project module {module}")
    used[module] += 1
    flags[kind] += 1
    names.add(name)
    start, stop = int(start), int(stop)
    if start and module not in changed:
        spans[module].update(range(start, stop + 1))
    elif not start:
        missing_range[module] += 1

if not {"FixedClassRH.ordinaryRH", "eventually_primeError_le_rpow", "star_inequality"} <= names:
    raise ValueError("The imported kernel environment did not expose the proof bodies")
if flags["missing"] or flags["axiom"]:
    raise ValueError(f"Missing declaration or project axiom on the path: {flags}")
untouched = imports - used.keys()
print("Project kernel declarations reached:", sum(used.values()))
print("Source modules with reachable declarations:", len(used), "of", len(imports))
print("Whole modules without a reachable declaration:", corpus.size(untouched))
print("Largest such modules:", sorted(((corpus.sizes[m]["code"], m) for m in untouched), reverse=True)[:12])
covered = 0
for module, lines in spans.items():
    code = lexical_lines(corpus.paths[module].read_text())
    covered += sum(bool(text.strip()) for n, (text, _) in enumerate(code, 1) if n in lines)
print("Code lines inside mapped reachable declaration spans, overlapping ranges counted once:", covered)
print("Reached declarations without a reported source range:", sum(missing_range.values()))
print("Upstream ranges omitted for changed modules:", len(changed & used.keys()))
