"""Group theorems with identical type nodes and universe parameters in the compact export."""
from collections import defaultdict
import hashlib
import json
import sys

EXPECTED = "ab7b4223b9bd748a1aa68bdb63afb6d6264121fc834aadba7ba3d3796c32115b"


def collect(stream):
    names = [""]
    groups = defaultdict(list)
    digest = hashlib.sha256()
    theorem_count = 0
    for line in stream:
        digest.update(line)
        if line.startswith(b'{"in":'):
            record = json.loads(line)
            if record["in"] != len(names):
                raise ValueError("missing name in proof export")
            component = record.get("str", record.get("num"))
            prefix = names[component["pre"]]
            suffix = str(component.get("str", component.get("i")))
            names.append(prefix + "." + suffix if prefix else suffix)
        elif line.startswith(b'{"thm":'):
            theorem = json.loads(line)["thm"]
            key = theorem["type"], tuple(theorem["levelParams"])
            groups[key].append(names[theorem["name"]])
            theorem_count += 1
    if digest.hexdigest() != EXPECTED:
        raise ValueError("unexpected compact proof export SHA-256: " + digest.hexdigest())
    return {
        "sha256": EXPECTED,
        "theorem_records": theorem_count,
        "pairs": [group for group in groups.values() if len(group) > 1],
    }


if __name__ == "__main__":
    json.dump(collect(sys.stdin.buffer), sys.stdout, ensure_ascii=False)
    sys.stdout.write("\n")
