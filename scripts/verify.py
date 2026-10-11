#!/usr/bin/env python3
"""Verify frozen source integrity, or rebuild isolated projects with pinned Lean/Mathlib.
This script never downloads software or changes the supplied Mathlib checkout.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
CONFIG = json.loads((ROOT / 'verification/config.json').read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def uncomment(text):
    result = []
    i = depth = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i]); i += 1
    require(depth == 0, 'Unclosed Lean comment')
    return ''.join(result)

def integrity():
    manifest = json.loads((ROOT / 'verification/repository_sha256.json').read_text())
    ignored = {'.git', '.lake', '.replay', '__pycache__'}
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*')
              if p.is_file() and not (set(p.relative_to(ROOT).parts) & ignored)}
    expected_files = set(manifest) | {'verification/repository_sha256.json'}
    require(actual == expected_files, 'Unmanifested or missing packaged files: ' + str(sorted(actual ^ expected_files)))
    for path, expected in manifest.items():
        require(digest(ROOT/path) == expected, 'Changed packaged file: ' + path)
    provenance = json.loads((ROOT / 'verification/source_provenance.json').read_text())
    evidence = json.loads((ROOT / 'verification/2026-10-10/EVIDENCE_SHA256.json').read_text())
    count = 0
    for name, project in CONFIG['projects'].items():
        directory = ROOT/'projects'/name
        order = project['order']
        require(len(order) == len(set(order)), 'Duplicate module in ' + name)
        require({p.stem for p in directory.glob('*.lean')} == set(order), 'Module coverage: ' + name)
        seen = set()
        for module in order:
            path = directory/(module+'.lean')
            entry = provenance[str(path.relative_to(ROOT))]
            require(digest(path) == entry['sha256'] == evidence[entry['evidence_path']], 'Source identity: '+str(path))
            text = uncomment(path.read_text())
            # Audit programs may inspect/report these tokens; proof modules may not use them.
            if 'Audit' not in module and module != 'RuntimeAuxiliaryMetadata':
                require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', text), 'Forbidden proof feature: '+module)
            for dep in re.findall(r'^import\s+(\S+)', text, re.M):
                require(dep in seen or dep.split('.')[0] in {'Mathlib','Lean','Std','Init'}, 'Unordered or missing import: '+module+' -> '+dep)
            seen.add(module)
            count += 1
    print(f'PASS: {len(manifest)} packaged hashes; {count} source identities and ordered import closures.')

def replay(args):
    mathlib = Path(args.mathlib).resolve()
    binary = Path(args.lean_bin).resolve()
    out = Path(args.out).resolve()
    require(not out.exists(), 'Use a new output directory')
    require(out != ROOT and ROOT not in out.parents, 'Keep replay output outside the frozen repository')
    env = os.environ.copy()
    for key in ('LEAN_PATH','LEAN_SRC_PATH'):
        env.pop(key, None)
    env['PATH'] = str(binary) + os.pathsep + env.get('PATH','')
    env['LEAN_NUM_THREADS'] = '1'
    def output(command, cwd=None):
        return subprocess.check_output([str(x) for x in command], cwd=cwd, env=env, text=True).strip()
    version = output([binary/'lean','--version'])
    require('version '+CONFIG['lean_version']+',' in version and CONFIG['lean_commit'] in version, 'Wrong Lean release: '+version)
    require(output(['git','rev-parse','HEAD'],mathlib) == CONFIG['mathlib_commit'], 'Wrong Mathlib revision')
    require(not output(['git','status','--porcelain=v1','--untracked-files=no'],mathlib), 'Modified Mathlib tracked files')
    expected = json.loads((ROOT/'verification/2026-10-10/global_support/environment.json').read_text())
    actual_manifest = json.loads((mathlib/'lake-manifest.json').read_text())
    require(actual_manifest == expected['mathlib_lake_manifest'], 'Changed Mathlib dependency manifest')
    for pkg in actual_manifest['packages']:
        p = mathlib/'.lake/packages'/pkg['name']
        require(output(['git','rev-parse','HEAD'],p) == pkg['rev'], 'Wrong dependency: '+pkg['name'])
        require(not output(['git','status','--porcelain=v1','--untracked-files=no'],p), 'Modified dependency: '+pkg['name'])
    leanpath = output([binary/'lake','env','printenv','LEAN_PATH'],mathlib)
    paths = [Path(x) if Path(x).is_absolute() else mathlib/x for x in leanpath.split(os.pathsep)]
    paths = [x.resolve() for x in paths]
    for p in paths:
        require(p == binary.parent/'lib/lean' or mathlib/'.lake' in p.parents, 'Unexpected imported object path: '+str(p))
    out.mkdir(parents=True)
    receipt = {'utc':datetime.now(timezone.utc).isoformat(), 'lean_version':version, 'lean_sha256':digest(binary/'lean'), 'mathlib_commit':CONFIG['mathlib_commit'], 'projects':{}, 'whole_import_kernel_replay':'NOT_RUN'}
    selected = list(CONFIG['projects']) if args.project == 'all' else [args.project]
    for name in selected:
        project = CONFIG['projects'][name]
        source = out/name/'source'; build = out/name/'build'; logs = out/name/'logs'
        for p in (source,build,logs):
            p.mkdir(parents=True)
        require('"' not in str(out) and '\\' not in str(out), 'Unsupported audit output path quoting')
        relocations = []
        for module in project['order']:
            original = ROOT/'projects'/name/(module+'.lean')
            for p in paths:
                require(not (p/(module+'.olean')).exists(), 'Imported object shadows local module: '+module)
            text = original.read_text()
            prefix = project['audit_output_prefix']
            if prefix in text:
                require('Audit' in module, 'Output relocation would affect a proof module')
                text = text.replace(prefix, str(out/name))
                relocations.append(module)
            (source/original.name).write_text(text)
        run_env = dict(env, LEAN_PATH=os.pathsep.join(map(str,[build]+paths)))
        rows = []
        for module in project['order']:
            command = [str(binary/'lean'),'-j1','-R',str(source),'-o',str(build/(module+'.olean')),str(source/(module+'.lean'))]
            completed = subprocess.run(command,cwd=source,env=run_env,text=True,capture_output=True)
            log = completed.stdout + completed.stderr
            (logs/(module+'.log')).write_text(log)
            rows.append({'module':module,'returncode':completed.returncode,'log_sha256':digest(logs/(module+'.log'))})
            print(name+'/'+module, 'PASS' if completed.returncode == 0 else 'FAIL', flush=True)
            require(completed.returncode == 0, log)
            require(not re.search(r'(^|\n).*\b(warning|error):',log), log)
        axiom_log = (logs/(project['axiom_module']+'.log')).read_text()
        reports = re.findall(r'depends on axioms: \[(.*?)\]',axiom_log)
        require(reports, 'No axiom reports')
        for report in reports:
            require(set(report.split(', ')) <= set(CONFIG['allowed_axioms']), 'Unexpected axiom: '+report)
        receipt['projects'][name] = {'status':'PASS','modules':rows,'audit_output_only_relocations':relocations,'axiom_module':project['axiom_module']}
        (out/'REPLAY_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    integrity()
    print('PASS: selected source rebuilds and auditors; whole-import leanchecker was not run.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--project',choices=['all']+list(CONFIG['projects']),default='all')
    parser.add_argument('--mathlib')
    parser.add_argument('--lean-bin')
    parser.add_argument('--out')
    args = parser.parse_args()
    try:
        integrity()
        if args.replay:
            require(args.mathlib and args.lean_bin and args.out, 'Replay requires --mathlib, --lean-bin and --out')
            replay(args)
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print('FAIL:',error,file=sys.stderr)
        sys.exit(1)
