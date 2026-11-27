"""Restore the pinned public compact-edition dependencies for the incremental RH check."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import re
import subprocess

host = "https://rh-cache.taucetiproject.org"
digest = "74e325354bd43971531dbe5202ad9dfa3faa5d18ee34f65dcf2f1f0da0399981"
origin = host + "/artifacts/leanprover-community/riemann-hypothesis-grh-lean/grh-compact"
def download(url):
    return subprocess.check_output(["curl", "-fsSL", "--retry", "3", "--max-time", "90",
                                    "-A", "RiemannHypothesisCache/1.0", url])

def restore(row):
    name, key, filename, expected = row
    assert re.fullmatch(r"[\w']+(\.[\w']+)*", name) and re.fullmatch(r"[a-f0-9]{16}\.ltar", filename)
    if name in {"New.Main", "Main", "Statements"}:
        return
    parts = name.split(".")
    target = Path(".lake/build/lib/lean", *parts[:-1]).resolve()
    ir = Path(".lake/build/ir", *parts[:-1]).resolve()
    target.mkdir(parents=True, exist_ok=True)
    ir.mkdir(parents=True, exist_ok=True)
    data = download(f"{origin}/{filename[:-5]}.art")
    assert sha256(data).hexdigest() == expected
    with TemporaryDirectory() as tmp:
        archive = Path(tmp, filename)
        archive.write_bytes(data)
        job = [{"file": str(archive), "base": [str(target), str(ir)], "hash": key}]
        subprocess.run(["leantar", "--jobs", "1", "-j", "-x", "-"], input=json.dumps(job),
                       text=True, check=True, stdout=subprocess.DEVNULL)
    assert (target / (parts[-1] + ".olean")).is_file()

manifest = download(f"{host}/grh-lean/grh-compact/module-manifests/{digest}.jsonl.gz")
assert sha256(manifest).hexdigest() == digest
header, *rows = map(json.loads, gzip.decompress(manifest).splitlines())
assert header["modules"] == len(rows) == 794
with ThreadPoolExecutor(12) as pool:
    list(pool.map(restore, rows))
