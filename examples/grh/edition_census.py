"""Measure original and rewritten Lean sources with the same comment- and literal-aware lexer."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile

from leanreducer.source import HEADER, lexical_lines

ORIGINAL = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"
SECTION = re.compile(r"^(?:(?:public|private|noncomputable|meta)\s+)*(?:namespace|section|end)\b")
OPTIONS = re.compile(r"^(?:set_option|attribute|open|variable|universe)\b")


def source_stats(raw):
    text = raw.decode("utf-8")
    stats = Counter(modules=1, bytes=len(raw), physical=text.count("\n")+int(bool(text) and not text.endswith("\n")))
    for code, structure in lexical_lines(text):
        if not code.strip():
            continue
        stats["code"] += 1
        stats["code_chars"] += len("".join(code.split()))
        if HEADER.fullmatch(structure):
            stats["import_lines"] += 1
        elif SECTION.match(structure):
            stats["scope_lines"] += 1
        elif OPTIONS.match(structure):
            stats["options_open_variable_lines"] += 1
    return stats


def measure(files):
    totals, sizes, folders = Counter(), Counter(), Counter()
    for name, raw in files:
        try:
            stats = source_stats(raw)
        except (ValueError, UnicodeError) as error:
            raise ValueError(f"{name}: {error}") from error
        totals.update(stats)
        sizes[stats["code"]] += 1
        folders[PurePosixPath(name).parts[0]] += stats["code"]
    if totals["modules"] == 0:
        raise ValueError("empty source")
    def quantile(num, den):
        required = (totals["modules"]*num+den-1)//den
        count = 0
        for size, frequency in sorted(sizes.items()):
            count += frequency
            if count >= required:
                return size
        raise AssertionError("empty size distribution")
    return {"totals": dict(totals),
            "module_size_in_code_lines": {"median": quantile(1,2), "p90": quantile(9,10),
                                          "max": max(sizes)},
            "modules_at_most": {str(limit): {"modules": sum(v for n,v in sizes.items() if n<=limit),
                                              "code": sum(n*v for n,v in sizes.items() if n<=limit)}
                                for limit in (25,50,100,200)},
            "largest_top_level_paths_by_code": dict(folders.most_common(8))}


def original_files(path):
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            digest.update(block)
    if digest.hexdigest() != ORIGINAL:
        raise ValueError("original archive SHA-256 mismatch")
    with tarfile.open(path, mode="r|gz") as tar:
        for member in tar:
            name = PurePosixPath(member.name)
            if member.isfile() and name.parts[:2] == ("lean", "src") and name.suffix == ".lean":
                with tar.extractfile(member) as f:
                    yield str(name.relative_to("lean/src")), f.read()
            tar.members.clear()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--original-archive", type=Path)
    group.add_argument("--source", type=Path)
    args = parser.parse_args()
    if args.original_archive:
        result = measure(original_files(args.original_archive))
        if result["totals"]["modules"] != 175187 or result["totals"]["physical"] != 17374215:
            raise ValueError(f"unexpected original inventory: {result['totals']}")
        result["archive_sha256"] = ORIGINAL
    else:
        root = args.source
        result = measure((str(p.relative_to(root)),p.read_bytes()) for p in sorted(root.rglob("*.lean")))
    print(json.dumps(result, indent=2))
