# The Collatz formalization library

Every machine formalization of a paper from the Collatz literature that
[ccchallenge.org](https://ccchallenge.org) knows about, vendored here as
git submodules, plus this repository's own formalizations, indexed three
ways by symlinks.

    git clone --recurse-submodules https://github.com/msharpe248/collatz
    # or, in an existing clone:
    git submodule update --init --depth 1

| directory | contents |
|---|---|
| `repos/owner__repo/` | the formalization repositories (submodules, pinned commits) |
| `by-paper/<bibtex_key>/` | symlinks to every formalization of that paper (keys as on ccchallenge.org) |
| `by-assistant/<lean4\|...>/` | by proof assistant |
| `by-status/<formalising\|...>/` | by ccchallenge status |
| `manifest.json` | full metadata: paper, contributor, AI assistance, status, local path |
| `refresh.py` | re-harvests ccchallenge.org and reports entries missing here |

Notes: submodules pin the commit that was current when added — `git submodule
update --remote` advances them. One formalization (Tao 2022 on
[ProofAtlas](https://www.proofatlas.ai/sources/tao-almost-bounded-orbits/),
397 Lean files) is web-only with no git remote; see `manifest.json`.
Symlinks require a filesystem that supports them (macOS/Linux; on Windows
enable `core.symlinks`).
