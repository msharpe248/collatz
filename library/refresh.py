#!/usr/bin/env python3
"""Re-harvest ccchallenge.org and report formalisation entries not yet in
library/manifest.json (new repos to `git submodule add` under library/repos/,
named owner__repo). Read-only: prints a report, does not modify anything."""
import json, urllib.request, time
def get(u):
    with urllib.request.urlopen(u, timeout=30) as r: return json.load(r)
papers = get("https://ccchallenge.org/api/papers?limit=1000")
papers = papers["items"] if isinstance(papers, dict) else papers
known = {e["repository_url"].strip() for e in json.load(open(__file__.replace("refresh.py","manifest.json")))["formalisations"]}
new = 0
for p in papers:
    if p.get("formalisations_count", 0) == 0: continue
    for f in get(f"https://ccchallenge.org/api/papers/{p['bibtex_key']}/formalisations"):
        u = (f.get("repository_url") or "").strip()
        if u and u not in known:
            print(f"NEW: {p['bibtex_key']:30s} {f.get('proof_assistant','?'):8s} {u}  ({f.get('user_display_name')})")
            new += 1
    time.sleep(0.2)
print(f"{new} new entries" if new else "library is up to date with ccchallenge.org")
