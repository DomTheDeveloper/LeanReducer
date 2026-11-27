"""Independently expand the shared Lean command and compare all 794 modules to pinned Git blobs."""
import hashlib
from pathlib import Path
import re
import subprocess
import sys

REV = 'a57c37471c835968b1932a0f8347978b89ba7ab6'
HOST = 'Lib/General/Algebra/CechDescent.lean'
MARK = '-- LeanReducer shares the repeated Ext transparency settings.\n'
USE = re.compile(r'^sealAbelianExt(?= in$|$)', re.M)
MACRO = re.compile(r'macro "sealAbelianExt" : command =>\n  `\(seal ([^.\n]*?.*?)\)\n\n', re.S)
ORIGINAL = ('seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup\n'
            '  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv\n'
            '  CategoryTheory.Abelian.Ext.mapExactFunctor')


def verify(repo):
    src = repo/'grh-compact/src'
    host = (src/HOST).read_text()
    macro, = MACRO.finditer(host)
    if ('seal ' + macro[1]).split() != ORIGINAL.split():
        raise ValueError('the native macro does not expand to the original identifiers in order')
    names = subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','--name-only',REV,'--','grh-compact/src'],text=True).splitlines()
    files = sorted(p for p in src.rglob('*.lean'))
    if {str(f.relative_to(repo)) for f in files} != set(names):
        raise ValueError('source file set changed')
    total = scoped = 0
    digest = hashlib.sha256()
    for f in files:
        text = f.read_text()
        if f == src/HOST:
            text = MACRO.sub('',text,count=1)
        scoped += text.count('\nsealAbelianExt in\n')
        text, n = USE.subn(ORIGINAL,text)
        total += n
        if n or f == src/HOST:
            if text.count(MARK) != 1:
                raise ValueError(f'missing per-file change notice: {f}')
            text = text.replace(MARK,'')
        path = str(f.relative_to(repo))
        original = subprocess.check_output(['git','-C',str(repo),'show',REV+':'+path])
        if text.encode() != original:
            raise ValueError(f'expanded file differs: {path}')
        digest.update(path.encode()+b'\0'+hashlib.sha256(original).digest())
    if (len(files),total,scoped) != (794,21,6):
        raise ValueError('unexpected coverage')
    return {'files':len(files),'commands':total,'scoped':scoped,'expanded_tree_sha256':digest.hexdigest()}


if __name__ == '__main__':
    import json
    print(json.dumps(verify(Path(sys.argv[1]).resolve()),indent=2))
