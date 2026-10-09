#!/usr/bin/env python3
"""Check local Palomar source/metadata rules using pinned upstream validators.

This script does not submit, register, publish, or perform the full registry sandbox
workflow. Build proofs and run the bundled Comparator/independent kernels separately.
Tool checkouts and reports must be kept outside the distributable source directory.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

PINS = {
    'PalomarSubmission': ('https://github.com/PalomarRegistry/PalomarSubmission', 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'),
    'formalization.yaml': ('https://github.com/mathlib-initiative/formalization.yaml', '99c678e569c7c4c0772db297c5ddd5e4c9b6322e'),
}

def command(argv, cwd=None):
    proc = subprocess.run([str(x) for x in argv], cwd=cwd, check=False, capture_output=True, text=True)
    if proc.returncode:
        raise RuntimeError(f'{argv[0]} failed ({proc.returncode}): {(proc.stderr or proc.stdout)[-1500:].strip()}')
    return proc.stdout.strip()

def pinned_checkout(directory, url, revision):
    if not directory.exists():
        command(['git', 'clone', '--no-checkout', '--filter=blob:none', url, directory])
        command(['git', '-C', directory, 'fetch', '--depth=1', 'origin', revision])
        command(['git', '-C', directory, 'checkout', '--detach', revision])
    actual = command(['git', '-C', directory, 'rev-parse', 'HEAD'])
    if actual != revision:
        raise RuntimeError(f'{directory}: expected {revision}, found {actual}; use a clean tools directory')
    if command(['git', '-C', directory, 'status', '--porcelain', '--untracked-files=no']):
        raise RuntimeError(f'{directory}: tracked upstream validator sources have local modifications')

def public_files(root):
    for directory, subdirectories, files in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(x for x in subdirectories if x not in {'.git', '.lake', '__pycache__'} and not (Path(directory)/x).is_symlink())
        for name in sorted(files):
            p = Path(directory)/name
            if p.is_file() and not p.is_symlink():
                yield p

def source_fingerprint(root):
    digest = hashlib.sha256()
    for p in public_files(root):
        digest.update(p.relative_to(root).as_posix().encode()+b'\0')
        digest.update(hashlib.sha256(p.read_bytes()).digest())
    return digest.hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repository', type=Path, default=Path.cwd())
    ap.add_argument('--tools-dir', type=Path, required=True, help='External directory for pinned upstream verifier checkouts')
    ap.add_argument('--report', type=Path, help='Write JSON report outside the source repository')
    ap.add_argument('--licensee-image', help='Existing Docker image containing the pinned Palomar licensee detector; otherwise use Ruby/Bundler')
    ap.add_argument('--skip-lean', action='store_true', help='Report Lean parser/import closure checks as unresolved')
    args = ap.parse_args()
    root = args.repository.resolve()
    toolsdir = args.tools_dir.resolve()
    if toolsdir == root or root in toolsdir.parents:
        ap.error('--tools-dir must be outside the source repository')
    if args.report and (args.report.resolve() == root or root in args.report.resolve().parents):
        ap.error('--report must be outside the source repository')
    toolsdir.mkdir(parents=True, exist_ok=True)
    for name, (url, revision) in PINS.items():
        pinned_checkout(toolsdir/name, url, revision)
    sys.path.insert(0, str(toolsdir/'PalomarSubmission'))
    from scripts import submission_contract as contract, source_requirements as sources, verify_submission as verifier
    import jsonschema
    report = {'checked_at_utc': dt.datetime.now(dt.timezone.utc).isoformat(), 'repository': str(root), 'source_fingerprint_sha256': source_fingerprint(root), 'tools': {k:{'url':u,'commit':r} for k,(u,r) in PINS.items()}, 'checks': [], 'limitations': ['Local preflight only; full Palomar registry sandbox, publication, submission, registration, and AI editorial review have not run.','This program does not establish legal redistribution rights, human mathematical review, or theorems being proved; run the proof build, axiom audit, Comparator, and independent kernel replay separately.']}
    try:
        report['source_commit'] = command(['git', '-C', root, 'rev-parse', 'HEAD'])
        report['source_dirty'] = bool(command(['git', '-C', root, 'status', '--porcelain']))
    except RuntimeError:
        report['source_commit'] = None
        report['source_dirty'] = None
    state = {}
    def check(name, action):
        try:
            evidence = action()
            report['checks'].append({'name':name, 'status':'passed', 'evidence':evidence})
        except Exception as ex:
            report['checks'].append({'name':name, 'status':'unresolved', 'error':str(ex)})
    def metadata():
        data = contract.load_formalization_metadata(root/'formalization.yaml')
        state['metadata']=data
        schema = json.loads((toolsdir/'formalization.yaml/schema/v0.4.schema.json').read_text())
        jsonschema.Draft7Validator(schema).validate(data)
        if data.get('version') != 'v0.4':
            raise RuntimeError('Declare version: v0.4 explicitly')
        state['metadata']=data
        return {'version':data['version'], 'license':data['project']['license'], 'authors':data['project']['authors'], 'responsible_maintainers':data['project']['responsible_maintainers']}
    def configuration():
        state['config']=verifier.load_comparator_config(root/'comparator.json')
        return state['config']
    def structure():
        configs=[p for p in [root/'lakefile.toml',root/'lakefile.lean'] if p.exists()]
        if len(configs)!=1 or configs[0].is_symlink() or not configs[0].is_file() or configs[0].stat().st_size>verifier.MAX_CONFIGURATION_BYTES:
            raise RuntimeError('Exactly one regular Lakefile under 1 MiB is required')
        if configs[0].suffix=='.toml':
            tomllib.loads(configs[0].read_text())
        manifest=root/'lake-manifest.json'
        if manifest.is_symlink() or not manifest.is_file():
            raise RuntimeError('Committed regular lake-manifest.json is required')
        if not isinstance(json.loads(manifest.read_text()),dict):
            raise RuntimeError('Manifest must be one JSON object')
        total=sum(p.stat().st_size for p in public_files(root))
        if total>verifier.MAX_SOURCE_BYTES:
            raise RuntimeError(f'Public source tree has {total} bytes; limit 500 MiB')
        verifier.reject_committed_build_artifacts(root)
        for p in public_files(root):
            with p.open('rb') as f:
                if f.read(150).startswith(b'version https://git-lfs.github.com/spec/v1'):
                    raise RuntimeError(f'Git LFS pointer: {p.relative_to(root)}')
        if (root/'.git').exists():
            verifier.validate_preservable_git_checkout(root,'submitted source')
        return {'lakefile':configs[0].name,'source_bytes_excluding_generated_lake_git':total,'manifest':'lake-manifest.json','compiled_artifacts_outside_lake':0,'lfs_pointers':0}
    def license_check():
        path=verifier.repository_license_file(root)
        if args.licensee_image:
            docker_env=os.environ.copy()
            for k in ('DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH'):
                docker_env.pop(k,None)
            proc=subprocess.run(['docker','--host=unix:///var/run/docker.sock','run','--rm','--network=none','--mount',f'type=bind,src={root},dst=/submitted,readonly',args.licensee_image,'/submitted'],env=docker_env,capture_output=True,text=True)
            if proc.returncode:
                raise RuntimeError('Docker licensee detector failed: '+proc.stderr[-1500:])
            detected=json.loads(proc.stdout)
            identifiers=[x['spdx_id'] for x in detected['licenses']]
            if len(identifiers)!=1 or len(detected['matched_files'])!=1:
                raise RuntimeError('Licensee did not detect exactly one unambiguous license')
            spdx=identifiers[0]
        else:
            bundle=shutil.which('bundle')
            if not bundle:
                raise RuntimeError('Ruby/Bundler unavailable; install locked PalomarSubmission/Gemfile dependencies or provide --licensee-image')
            spdx=verifier.detect_spdx_identifier(root,Path(bundle))
        if spdx!=state['metadata']['project']['license']:
            raise RuntimeError('Detected SPDX differs from metadata')
        return {'file':path.name,'spdx':spdx,'licensee_version':'10.0.0','redistribution_rights':'not established by mechanical detection'}
    def source_rules():
        evidence,issues=sources.inspect_lean_sources(root)
        if issues:
            raise RuntimeError('\n'.join(str(x) for x in issues))
        return evidence
    def dependencies():
        packages=verifier.manifest_packages(root)
        toolchain=(root/'lean-toolchain').read_text().strip()
        floor=json.loads((toolsdir/'PalomarSubmission/toolchains.json').read_text())['minimum']
        if verifier.parse_lean_version(toolchain,verifier.TOOLCHAIN_RE)<verifier.parse_lean_version(floor,verifier.VERSION_RE):
            raise RuntimeError(f'Toolchain below Palomar minimum {floor}')
        for p in packages:
            d=verifier.package_checkout(root,p,checkout=root)
            if command(['git','-C',d,'rev-parse','HEAD'])!=p['revision']:
                raise RuntimeError(f"Dependency {p['name']} checkout differs from manifest")
            if command(['git','-C',d,'status','--porcelain','--untracked-files=no']):
                raise RuntimeError(f"Dependency {p['name']} tracked source has modifications")
            verifier.validate_preservable_git_checkout(d,f"dependency {p['name']}",allow_inert_submodules=True)
        match=verifier.check_mathlib_toolchain(root,packages,checkout=root,project_toolchain=toolchain,project_toolchain_path='lean-toolchain')
        roots,aliases=verifier.allowed_roots()
        trusted={}
        # Authenticate the canonical semantic-release tag used by this package.
        # Other canonical-history revisions need the registry's full ancestry check.
        for p in packages:
            if verifier.canonical_repository(p['repository'],aliases).lower()=='leanprover-community/mathlib4':
                tag=toolchain.split(':',1)[1]
                refs=command(['git','ls-remote',p['url'],f'refs/tags/{tag}',f'refs/tags/{tag}^{{}}']).splitlines()
                if not any(x.split()[0]==p['revision'] for x in refs):
                    raise RuntimeError('Mathlib pin not authenticated by its canonical matching release tag; run registry ancestry check')
                nested=verifier.manifest_packages(verifier.package_checkout(root,p,checkout=root))
                actual={x['name']:x for x in packages}
                for expected in nested:
                    item=actual.get(expected['name'])
                    if not item or item['revision']!=expected['revision'] or item['repository'].lower()!=expected['repository'].lower():
                        raise RuntimeError(f"Substituted/missing Mathlib manifest dependency {expected['name']}")
                for name in {p['name'],*(x['name'] for x in nested)}:
                    trusted[name]=('leanprover-community/mathlib4','high')
        state['trusted']=trusted
        state['packages']=packages
        return {'toolchain':toolchain,'minimum':floor,'mathlib_toolchain':match,'package_count':len(packages),'trusted_package_names':sorted(trusted)}
    def lean_headers():
        if args.skip_lean:
            raise RuntimeError('Skipped by --skip-lean')
        files=[p for p in sources.lean_source_files(root) if p.name!='lakefile.lean']
        for start in range(0,len(files),64):
            batch=files[start:start+64]
            output=command(['lean','--deps-json',*batch],cwd=root)
            entries=json.loads(output)['imports']
            if len(entries)!=len(batch):
                raise RuntimeError('Unexpected Lean parsed-header count')
            for p,e in zip(batch,entries,strict=True):
                if not verifier.parse_lean_header(json.dumps({'imports':[e]})).is_module:
                    raise RuntimeError(f'{p}: Lean parser rejected module header')
        state['lean_prefix']=Path(command(['lean','--print-prefix'],cwd=root))
        return {'files_checked':len(files),'toolchain_bundled_tools':{k:str(p) for k,p in verifier.toolchain_tools(state['lean_prefix']).items()}}
    def challenge():
        if args.skip_lean:
            raise RuntimeError('Skipped by --skip-lean')
        config=state['config']
        sourcepath=command(['lake','env','printenv','LEAN_SRC_PATH'],cwd=root)
        ch=verifier.resolve_module_source(config['challenge_module'],project=root,lean_source_path=sourcepath)
        so=verifier.resolve_module_source(config['solution_module'],project=root,lean_source_path=sourcepath)
        lines=sources.physical_lines(ch.read_bytes().decode())
        if lines>verifier.MAX_CHALLENGE_LINES or ch.stat().st_size>verifier.MAX_CHALLENGE_BYTES:
            raise RuntimeError('Challenge exceeds hard line/byte limits')
        # --src-deps reports immediate source roots. Parse headers recursively
        # with Lean itself to audit the complete transitive import closure.
        searchroots=[Path(x) for x in sourcepath.split(os.pathsep) if x]
        searchroots.append(state['lean_prefix']/'src/lean')
        def resolve_import(name):
            suffix=Path(*name.split('.')).with_suffix('.lean')
            for directory in searchroots:
                candidate=directory/suffix
                if candidate.is_file():
                    return candidate.resolve()
            raise RuntimeError('No source for imported module '+name)
        pending={ch.resolve()}
        observed=set()
        imported_packages=set()
        while pending:
            batch=sorted(pending-observed)[:64]
            if not batch:
                break
            pending.difference_update(batch)
            parsed=json.loads(command(['lean','--deps-json',*batch],cwd=root))['imports']
            if len(parsed)!=len(batch):
                raise RuntimeError('Unexpected recursive source-header count')
            for p,item in zip(batch,parsed,strict=True):
                # Apply upstream error checking before preserving injected Init.
                verifier.parse_lean_header(json.dumps({'imports':[item]}))
                observed.add(p)
                for entry in item['result']['imports']:
                    dep=resolve_import(entry['module'])
                    if dep not in observed:
                        pending.add(dep)
        package_dirs={p['name']:verifier.package_checkout(root,p,checkout=root).resolve() for p in state['packages']}
        tracked_blobs={}
        untrusted=[]
        for p in sorted(observed-{ch.resolve()}):
            if p.is_relative_to(state['lean_prefix'].resolve()):
                continue
            package_name=next((n for n,d in package_dirs.items() if p.is_relative_to(d)),None)
            if package_name not in state['trusted']:
                untrusted.append(str(p)); continue
            directory=package_dirs[package_name]
            if package_name not in tracked_blobs:
                # HEAD is the authenticated exact manifest revision, checked
                # above. Batch its tracked blob identities instead of invoking
                # two Git processes for every imported Lean source.
                listing=command(['git','-C',directory,'ls-tree','-r','-z','HEAD'])
                tracked_blobs[package_name]={}
                for record in listing.split('\0'):
                    if record:
                        prefix,path=record.split('\t',1)
                        tracked_blobs[package_name][path]=prefix.split()[2]
            relative=p.relative_to(directory).as_posix()
            body=p.read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()
            if tracked_blobs[package_name].get(relative)!=blob:
                untrusted.append(str(p)); continue
            imported_packages.add(package_name)
        if untrusted:
            raise RuntimeError('Challenge imports unauthenticated/non-allowlisted source: '+str(untrusted[:100]))
        return {'source_count':len(observed)-1,'recursive_header_parser':'Lean --deps-json',
                'dependencies':[{'repository':r,'provenance':'allowlisted'} for r in sorted({state['trusted'][n][0] for n in imported_packages})],
                'imported_package_names':sorted(imported_packages),'untrusted_sources':[],
                'trust_level':'qualified' if any(state['trusted'][n][1]=='qualified' for n in imported_packages) else 'high',
                'challenge':str(ch.relative_to(root)),'solution':str(so.relative_to(root)),
                'challenge_lines':lines,'challenge_bytes':ch.stat().st_size,
                'readability_warning':lines>300 or ch.stat().st_size>32*1024}
    for name,fn in [('formalization_metadata_and_community_v04_schema',metadata),('comparator_config',configuration),('source_structure',structure),('root_license_spdx',license_check),('source_headers_and_line_limits',source_rules),('dependency_pins_canonical_mathlib_and_toolchain',dependencies),('lean_module_header_parser_and_bundled_tools',lean_headers),('challenge_transitive_imports_and_source_limits',challenge)]:
        check(name,fn)
    report['status']='passed' if all(x['status']=='passed' for x in report['checks']) else 'unresolved'
    output=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(output)
    print(output)
    return 0 if report['status']=='passed' else 1

if __name__=='__main__':
    raise SystemExit(main())
