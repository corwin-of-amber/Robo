#!/usr/bin/env python3
"""Check that the committed Lean toolchain, lockfile and Wasm overrides agree."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
release = root.joinpath('lean-toolchain').read_text().strip().split(':')[-1]
locked = {p['name']: p for p in json.loads(root.joinpath('lake-manifest.json').read_text())['packages']}
overrides = json.loads(root.joinpath('package-overrides.json').read_text())['packages']
errors = []
for package in overrides:
    entry = locked.get(package['name'])
    if entry is None:
        errors.append(f"{package['name']}: missing from lake-manifest.json")
        continue
    for field in ['rev', 'url', 'configFile']:
        if package.get(field) != entry.get(field):
            errors.append(f"{package['name']}: {field} differs between lockfile and overrides")
for name in ['Qq', 'batteries']:
    if locked[name]['inputRev'] != release:
        errors.append(f"{name}: expected release {release}, got {locked[name]['inputRev']}")
if errors:
    raise SystemExit('\n'.join(errors))
print(f'Dependency configuration agrees with {release}')
