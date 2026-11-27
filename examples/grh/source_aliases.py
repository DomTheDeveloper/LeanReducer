"""Find public source theorems sharing an exported type with an earlier visible project theorem."""
import argparse
import json
from pathlib import Path
import re

from leanreducer.source import Corpus, DECL, IDENT, lexical_lines

EXPORT_SHA256 = "ab7b4223b9bd748a1aa68bdb63afb6d6264121fc834aadba7ba3d3796c32115b"
SCOPE = re.compile(r"(?:(?:noncomputable|public|private|meta)\s+)*(namespace|section)(?:\s+(" + IDENT + r"))?")
END = re.compile(r"end(?:\s+" + IDENT + r")?")


def public_theorems(corpus):
    """Recognize explicit top-level theorem names and ordinary namespace and section commands."""
    locations = {}
    for module, path in corpus.paths.items():
        scopes = []
        for line_number, (_, structure) in enumerate(lexical_lines(path.read_text()), 1):
            if not structure or structure[0].isspace():
                continue
            command = structure.strip()
            scope = SCOPE.fullmatch(command)
            if scope:
                scopes.append(scope[2] if scope[1] == "namespace" else None)
            elif END.fullmatch(command):
                if scopes:
                    scopes.pop()
            elif declaration := DECL.match(command):
                name = declaration[1]
                if re.search(r"\bprivate\b", command[:declaration.start(1)]):
                    continue
                if name.startswith("_root_."):
                    name = name.removeprefix("_root_.")
                else:
                    name = ".".join(filter(None, [*scopes, name]))
                if name in locations:
                    raise ValueError(f"ambiguous source name {name}")
                locations[name] = (module, line_number)
    return locations


def candidates(corpus, export):
    if export["sha256"] != EXPORT_SHA256:
        raise ValueError("expected the pinned compact kernel export")
    loc = public_theorems(corpus)
    matched, pairs = set(), []
    for group in export["pairs"]:
        names = [name for name in group if name in loc]
        matched.update(names)
        for name in names:
            module, line = loc[name]
            imports = corpus.walk(module)
            for alternative in names:
                alt_module, alt_line = loc[alternative]
                if alt_module in imports and (alt_module != module or alt_line < line):
                    pairs.append({"name": name, "module": module, "line": line, "alternative": alternative})
    return {"recognized_public_names": len(loc), "names_in_duplicate_type_groups": len(matched),
            "earlier_project_theorems_of_identical_exported_type": sorted(pairs, key=lambda p: p["name"])}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="the compact upstream src directory")
    parser.add_argument("type_groups", type=Path, help="JSON produced by kernel_types.py")
    args = parser.parse_args()
    print(json.dumps(candidates(Corpus(args.source, ["Mathlib"]), json.loads(args.type_groups.read_text())),
                     indent=2, ensure_ascii=False))
