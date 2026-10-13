"""Print the import graph of the QCALean library as an indented list, grouped by folder.

Usage: python tools/depgraph.py

Each Lean file's line lists the QCALean files it imports directly, followed by the libraries
QCALean builds on (LocalAlgebrasLean, LinearAQFT, BosonicLean) from which it imports directly;
Mathlib is named only for a file that imports nothing else. Folders in the
order of the library's construction: Core -> Net -> Bosonic. Adapted from LocalAlgebrasLean's
tool of the same name.
"""
import os
import re

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SRC = os.path.join(ROOT, 'QCALean')
FOLDERS = ['Core', 'Net', 'Bosonic']
OUTSIDE = ['Mathlib', 'LocalAlgebrasLean', 'LinearAQFT', 'BosonicLean']


def modules():
    out = {}
    for dirpath, _, files in os.walk(SRC):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dirpath, f)
            name = os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')
            with open(path, encoding='utf-8') as fh:
                text = fh.read()
            imports = re.findall(r'(?m)^import (\S+)', text)
            own = [i for i in imports if i.startswith('QCALean.')]
            libs = [lib for lib in OUTSIDE if any(i.split('.')[0] == lib for i in imports)]
            out[name] = (own, libs)
    return out


def main():
    mods = modules()
    for folder in FOLDERS:
        names = sorted(n for n in mods if n.split('.')[1] == folder)
        if not names:
            continue
        print(f'- `{folder}/`')
        for n in names:
            own, libs = mods[n]
            siblings = [lib for lib in libs if lib != 'Mathlib']
            if own:
                deps = ', '.join('`' + d.split('.', 1)[1] + '`' for d in own)
                if siblings:
                    deps += ' and files of ' + ' and '.join(siblings)
            elif siblings:
                deps = 'files of ' + ' and '.join(siblings) + ' only'
            else:
                deps = 'Mathlib only'
            print(f"  - `{n.split('.', 1)[1]}` imports {deps}")


if __name__ == '__main__':
    main()
