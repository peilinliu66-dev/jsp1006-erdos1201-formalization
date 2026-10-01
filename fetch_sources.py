"""Install pinned external inputs and reconstruct the verified adaptations.

Fixed revisions, original source notices and file hashes are preserved.
All external Lean files and generated Far adaptations are excluded from Git.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(value):
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or '\\' in value or ':' in value:
        raise ValueError(f'Unsafe path: {value}')
    return Path(*p.parts)


def contained(root, value):
    p = (root / relative(value)).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError(f'Path escapes destination: {value}')
    return p


def checked(data, expected, label):
    if sha(data) != expected:
        raise ValueError(f'SHA256 mismatch: {label}')
    data.decode('utf-8')
    return data


def apply_patch(data, patch, path):
    sections = re.split(r'(?=^diff --git )', patch, flags=re.M)
    for section in sections:
        if not section.startswith(f'diff --git a/{path} b/{path}\n'):
            continue
        old = data.decode('utf-8').splitlines(keepends=True)
        lines = section.splitlines(keepends=True)
        result, pos, i = [], 0, 0
        while i < len(lines):
            match = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
            if not match:
                i += 1
                continue
            start = int(match[1]) - 1
            if start < pos:
                raise ValueError(f'Overlapping patch hunks: {path}')
            result.extend(old[pos:start])
            pos = start
            i += 1
            while i < len(lines) and not lines[i].startswith('@@ '):
                line = lines[i]
                if line.startswith((' ', '-')):
                    if pos >= len(old) or old[pos] != line[1:]:
                        raise ValueError(f'Patch context mismatch: {path}:{pos+1}')
                    if line[0] == ' ':
                        result.append(old[pos])
                    pos += 1
                elif line.startswith('+'):
                    result.append(line[1:])
                elif line.startswith('\\ No newline'):
                    raise ValueError('No-newline patch requires explicit handling')
                else:
                    break
                i += 1
        result.extend(old[pos:])
        data = ''.join(result).encode('utf-8')
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-project', type=Path,
                        help='Verify/install existing verified external and generated files without network')
    parser.add_argument('--jobs', type=int, default=6)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 12:
        parser.error('--jobs must be between 1 and 12')
    manifest = json.loads((HERE / 'external-sources.json').read_text(encoding='utf-8'))
    inputs = HERE / '.external_cache'

    def download(url, expected):
        if not url.startswith('https://raw.githubusercontent.com/'):
            raise ValueError('Only pinned GitHub raw source URLs are accepted')
        cached = inputs / expected
        if cached.exists():
            return checked(cached.read_bytes(), expected, url)
        with urlopen(Request(url, headers={'User-Agent': 'JSP1006-pinned-source/1'}), timeout=60) as response:
            data = response.read()
        checked(data, expected, url)
        inputs.mkdir(exist_ok=True)
        if not cached.exists():
            with cached.open('xb') as out:
                out.write(data)
        return data

    patches = {}
    if args.source_project is None:
        for p in manifest['patches']:
            patches[p['name']] = download(p['url'], p['sha256']).decode('utf-8')

    def obtain(entry):
        target = contained(HERE, entry['path'])
        if target.exists():
            return entry['path'], checked(target.read_bytes(), entry['packaged_sha256'], entry['path'])
        if args.source_project is not None:
            data = contained(args.source_project.resolve(), entry['path']).read_bytes()
        else:
            data = download(entry['raw_url'], entry['original_sha256'])
            for patch_name in entry.get('patches', []):
                data = apply_patch(data, patches[patch_name], entry['patch_path'])
            if entry.get('append_one_lf'):
                data += b'\n'
        checked(data, entry['packaged_sha256'], entry['path'])
        return entry['path'], data

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        staged = list(pool.map(obtain, manifest['sources']))
    by_path = dict(staged)
    for recipe in manifest['adaptations']:
        if args.source_project is not None:
            expected = contained(args.source_project.resolve(), recipe['path']).read_bytes()
        else:
            expected = None
        source_data = by_path[recipe['source_path']]
        checked(source_data, recipe['source_sha256'], recipe['source_path'])
        renamed = source_data.decode('utf-8')
        for rename in manifest.get('adaptation_renames', []):
            renamed = renamed.replace(rename['old'], rename['new'])
        if recipe.get('renamed_source_sha256'):
            checked(renamed.encode('utf-8'), recipe['renamed_source_sha256'], recipe['path'] + ' renamed input')
        source = renamed.splitlines(keepends=True)
        chunks = []
        for operation in recipe['operations']:
            if 'copy_lines' in operation:
                lo, hi = operation['copy_lines']
                if not 0 <= lo <= hi <= len(source):
                    raise ValueError(f'Invalid copy range: {recipe["path"]}')
                chunks.extend(source[lo:hi])
            else:
                chunks.append(operation['insert'])
        data = ''.join(chunks).encode('utf-8')
        checked(data, recipe['packaged_sha256'], recipe['path'])
        if expected is not None and data != expected:
            raise ValueError(f'Reconstruction differs from verified project: {recipe["path"]}')
        staged.append((recipe['path'], data))
    # Validate everything before writing any Lean source.
    for path, data in staged:
        target = contained(HERE, path)
        if target.exists():
            if target.read_bytes() != data:
                raise ValueError(f'Existing file differs: {path}')
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(data)
    receipt = {'status': 'PASSED', 'external_files': len(manifest['sources']),
               'reconstructed_adaptations': len(manifest['adaptations']),
               'all_output_sha256': {p: sha(d) for p, d in staged},
               'source_provenance': 'Fixed upstream revisions; original source notices preserved'}
    (HERE / 'bootstrap_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'all_output_sha256'}))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f'Pinned-source setup failed: {exc}', file=sys.stderr)
        raise SystemExit(1)
