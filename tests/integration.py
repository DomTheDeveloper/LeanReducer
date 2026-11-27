"""Real Lean integration test. Run from any directory with Lean 4.33.1 on PATH."""
import json
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(*args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True)


def main():
    with tempfile.TemporaryDirectory() as work:
        tmp = Path(work)
        repo = tmp/'project'
        shutil.copytree(ROOT/'tests/fixture',repo)
        run('git','init','--quiet',cwd=repo)
        run('git','add','.',cwd=repo)
        run('git','-c','user.name=LeanReducer','-c','user.email=test@example.invalid','commit','-qm','fixture',cwd=repo)
        run(sys.executable,'-m','leanreducer','reduce','--repo',str(repo),
            '--config',str(repo/'case.json'),'--output',str(tmp/'result'),'--target','9',
            '--module','Results','--decl','addZero','--tactic','assumption','--tactic','rfl',cwd=ROOT)
        record = json.loads((tmp/'result/verification.json').read_text())
        assert record['target_met'] and (record['before']['code'],record['after']['code']) == (11,9)
        assert [t['accepted'] for t in record['attempts']] == [False,True]
        assert record['axioms'] == {'checkedEndpoint':[]}
        assert not run('git','status','--porcelain',cwd=repo)
        run('git','apply',str(tmp/'result/reduction.patch'),cwd=repo)
        run('lake','build',cwd=repo)
        run('lake','env','leanchecker','Main',cwd=repo)
        print('Verified 11 → 9 code lines, unchanged endpoint type, no axioms.')


if __name__ == '__main__':
    main()
