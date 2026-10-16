# Atlas records

`catalogue.json` lists stable instance IDs in navigation order. Each existing `data/<id>/` folder contains the exact target `instance.rec`, prospective motivation `why.md`, and a context and related-instance index in `provenance.json`.

A solve PR adds `proof.json`, `Solution.lean`, `solution.md`, optional `witness.json`, and optional flat Lean helpers to that same folder. It cannot edit existing files. See [the full proposal specification](../CONTRIBUTING.md).

The trusted publisher adds `acceptance.json` after checking the successful workflow and merge. It derives `solution.rec`, including solver identity, accepted PR, theorem, and any displayed denominator. `scripts/build-content.py` validates the acceptance bindings before generating solved status and credit. A hand-edited record, local compilation, or schema check cannot establish acceptance.

`.rec` files use YAML. Exact polynomial expressions use the variable order `X0, X1, X2, Y0, Y1, Y2`, rational coefficients, and `**` for powers. Display LaTeX and mesh coefficients are presentation only. An accepted target must not be silently repurposed for another `(F,q,A)`.

## Editing an accepted explanation

Edit `solution.md` directly and rebuild the content. The site uses its current text. This does not change the accepted proof, contributor credit, or PR link, and does not require another Lean run. The original submission is retained in Git history. The target, Lean sources, proof manifest, and witness remain tied to the checked proof.

## Generated files and local preview

Do not hand-edit `record.json`, `solution.json`, `why.html`, `solution.html`, `data/index.json`, `data/revision.json`, or `leaderboard/credits.json`. For authorized source maintenance, rebuild and validate:

```sh
python3 scripts/build-content.py
python3 scripts/validate-records.py
python3 scripts/check-content.py
```

`python3 scripts/preview.py` serves the local website, watches sources, and rebuilds valid changes. The browser retains its route, reading position, and open construction dialog; refresh is deferred during free-camera exploration. The static site reads generated local assets and has no external runtime dependency.
