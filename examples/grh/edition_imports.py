"""Trace project import reachability from Main in the original verified archive."""
import argparse
from collections import Counter
import json

from edition_census import original_files
from leanreducer.source import imports
from pathlib import Path


def measure(files, entry):
    ids = {}
    modules = {}

    def number(name):
        if name not in ids:
            ids[name] = len(ids)
        return ids[name]

    for name, raw in files:
        module = name[:-len(".lean")].replace("/", ".")
        idx = number(module)
        if idx in modules:
            raise ValueError(f"duplicate module {module}")
        try:
            deps = tuple(dict.fromkeys(number(d) for d in imports(raw.decode("utf-8"))))
        except ValueError as error:
            raise ValueError(f"{name}: {error}") from error
        lines = raw.count(b"\n") + int(bool(raw) and not raw.endswith(b"\n"))
        modules[idx] = (deps, lines)
    present = set(modules)
    if entry not in ids or ids[entry] not in present:
        raise ValueError("missing entry module")
    reachable = set()
    todo = [ids[entry]]
    while todo:
        idx = todo.pop()
        if idx in reachable or idx not in present:
            continue
        reachable.add(idx)
        todo.extend(modules[idx][0])
    by_folder = Counter()
    for name, idx in ids.items():
        if idx in present and idx not in reachable:
            by_folder[name.partition(".")[0]] += 1
    def stats(nodes):
        return {"modules":len(nodes), "physical":sum(modules[i][1] for i in nodes),
                "distinct_direct_project_edges":sum(sum(j in present for j in modules[i][0]) for i in nodes)}
    external = Counter(n.partition(".")[0] for n,i in ids.items() if i not in present)
    return {"entry":entry, "tree":stats(present), "closure":stats(reachable),
            "outside_closure":stats(present-reachable), "outside_by_top_level":by_folder,
            "external_import_module_counts_by_namespace":external}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--original-archive",type=Path)
    group.add_argument("--source",type=Path)
    parser.add_argument("--entry",default="Main")
    args=parser.parse_args()
    if args.original_archive:
        files=original_files(args.original_archive)
    else:
        files=((str(p.relative_to(args.source)),p.read_bytes()) for p in sorted(args.source.rglob("*.lean")))
    print(json.dumps(measure(files,args.entry),indent=2))
