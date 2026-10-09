#!/usr/bin/env python3
"""Rebuild a proof project and reject nonstandard transitive axioms.

Run through the shared bounded launcher when working in the Conjectures
workspace. Dependencies must already be installed. --dependency-project
allows reuse of a clean, identically pinned Mathlib checkout.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PIN = 'a3a10db0e9d66acbebf76c5e6a135066525ac900'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    text = path.read_text()
    # Mask nested comments so documentation examples are not treated as imports.
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            result.append('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            result.append('  ')
            i += 2
        elif depth:
            result.append('\n' if text[i] == '\n' else ' ')
            i += 1
        else:
            result.append(text[i])
            i += 1
    dependencies = []
    for line in ''.join(result).splitlines():
        line = line.split('--', 1)[0].strip()
        if not line or line in ('prelude', 'module'):
            continue
        match = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if not match:
            break  # Imports occur only in the module header, not in code strings.
        dependencies.extend(match.group(1).split())
    return dependencies


def command(args, cwd, env):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', choices=['math15-source10'])
    parser.add_argument('--dependency-project', type=Path)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    project = root / 'proofs' / args.project
    dep = (args.dependency_project or project).resolve()
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    prefix = Path(command([args.lake, 'env', 'lean', '--print-prefix'], dep, env))
    lean = str(prefix / 'bin/lean')
    version = command([lean, '--version'], dep, env)
    if not version.startswith('Lean (version 4.27.0,'):
        raise RuntimeError('Expected Lean 4.27.0')
    ml = dep if (dep / 'Mathlib').is_dir() else dep / '.lake/packages/mathlib'
    if command(['git', 'rev-parse', 'HEAD'], ml, env) != PIN:
        raise RuntimeError('Mathlib revision does not match the pin')
    if command(['git', 'status', '--porcelain', '--untracked-files=no'], ml, env):
        raise RuntimeError('Mathlib tracked sources are modified')
    if (ml / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.27.0':
        raise RuntimeError('Mathlib toolchain mismatch')
    raw_paths = command([args.lake, 'env', 'printenv', 'LEAN_PATH'], dep, env).split(os.pathsep)
    dep_paths = [(dep / p).resolve() for p in raw_paths if p]
    build = project / '.lake/build/lib/lean'
    build.mkdir(parents=True, exist_ok=True)
    env['LEAN_PATH'] = os.pathsep.join(map(str, [build] + dep_paths))
    files = {p.stem: p for p in project.glob('*.lean')}
    ordered, seen, active = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in active:
            raise RuntimeError('Local import cycle: ' + name)
        active.add(name)
        for dependency in imports(files[name]):
            if dependency in files:
                visit(dependency)
        active.remove(name)
        seen.add(name)
        ordered.append(name)

    visit('AxiomAudit')
    before = {n + '.lean': sha(files[n]) for n in ordered}
    # Bind each recursively imported external source and compiled object.
    source_roots = [ml, prefix / 'src/lean', prefix / 'src/lean/lake']
    for path in dep_paths:
        marker = '.lake/build/lib/lean'
        if str(path).endswith(marker):
            source_roots.append(Path(str(path)[:-len(marker)]))
    object_roots = dep_paths + [prefix / 'lib/lean']
    external, external_paths = {}, {}

    def bind(name):
        if name in files or name in external:
            return
        relative = Path(*name.split('.'))
        sources = [p / relative.with_suffix('.lean') for p in source_roots]
        objects = [p / relative.with_suffix('.olean') for p in object_roots]
        source = next((p for p in sources if p.is_file()), None)
        obj = next((p for p in objects if p.is_file()), None)
        if source is None or obj is None:
            raise RuntimeError('Missing source/object binding: ' + name)
        external[name] = {'source_sha256': sha(source), 'olean_sha256': sha(obj)}
        external_paths[name] = (source, obj)
        for child in imports(source):
            bind(child)

    bind('Init')
    for name in ordered:
        for dependency in imports(files[name]):
            bind(dependency)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    outputs = []
    for name in ordered:
        obj = build / (name + '.olean')
        obj.unlink(missing_ok=True)
        proc = subprocess.run([lean, '-j', '4', '-o', str(obj), name + '.lean'],
                              cwd=project, env=env, text=True, capture_output=True)
        output = proc.stdout + proc.stderr
        outputs.append(name + '\n' + output)
        (project / '.lake/verification.log').write_text('\n'.join(outputs))
        if proc.returncode:
            print(output[-12000:])
            return proc.returncode
        print(name + ': checked', flush=True)
    audit = outputs[-1]
    axioms = {name: [a.strip() for a in body.split(',') if a.strip()]
              for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.S)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
        axioms[name] = []
    expected = set(re.findall(r'^#print axioms (\S+)', files['AxiomAudit'].read_text(), re.M))
    missing = sorted(expected - axioms.keys())
    bad = {name: values for name, values in axioms.items() if set(values) - ALLOWED}
    after = {n + '.lean': sha(files[n]) for n in ordered}
    for name, (source, obj) in external_paths.items():
        if external[name] != {'source_sha256': sha(source), 'olean_sha256': sha(obj)}:
            raise RuntimeError('External dependency changed during verification: ' + name)
    if missing or bad or before != after:
        raise RuntimeError(str({'missing': missing, 'unexpected_axioms': bad,
                                'sources_unchanged': before == after}))
    result = {'status': 'LEAN_CHECKED', 'lean_version': version, 'mathlib_commit': PIN,
              'started_utc': started, 'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_hashes': after, 'declaration_axioms': axioms,
              'external_dependency_bindings': external,
              'unexpected_axioms': bad, 'missing_audits': missing,
              'checker_sha256': sha(Path(__file__)),
              'targets': ['LeanProofs.Math15.source10', 'LeanProofs.Math15.source12',
                          'Math15Source10.source10_exact_validator',
                          'Math15Source10.source12_exact_validator']}
    for name in result['targets']:
        if name not in axioms:
            raise RuntimeError('Missing exact target: ' + name)
    (root / 'evidence/source10.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Exact targets checked; ' + str(len(axioms)) + ' transitive axiom audits passed.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
