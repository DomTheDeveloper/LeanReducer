"""Validate the scope and dependency accounting of a user-supplied research patch."""
import subprocess

from .verify import safe_path


def apply_reviewed(patch, checkout, project, spec):
    source = safe_path(project, spec['source'])
    protected = {safe_path(project, name) for name in spec.get('protected', [])}
    # Let Git interpret paths and quoting. It rejects absolute paths and traversal.
    subprocess.run(['git','apply','--index','--whitespace=error','--',str(patch.resolve())],
                   cwd=checkout, check=True)
    raw = subprocess.check_output(['git','diff','--cached','--name-only','--no-renames','-z'],cwd=checkout)
    paths = [safe_path(checkout, name.decode()) for name in raw.split(b'\0') if name]
    if not paths:
        raise ValueError('empty source patch')
    modes = subprocess.check_output(['git','diff','--cached','--raw','--no-renames','-z'],cwd=checkout)
    for item in modes.split(b'\0'):
        if item.startswith(b':'):
            before, after = item[1:].split()[:2]
            if not {before, after} <= {b'000000', b'100644'}:
                raise ValueError('the case permits only ordinary Lean source files')
    modules = set()
    for path in paths:
        if path in protected or not path.is_relative_to(source) or path.suffix != '.lean':
            raise ValueError(f'patch changes protected or non-source path: {path.relative_to(checkout)}')
        modules.add('.'.join(path.relative_to(source).with_suffix('').parts))
    return modules
