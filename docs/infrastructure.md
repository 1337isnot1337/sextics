# Repository architecture

The project uses direct GitHub PRs with protected Lean verification, owner sign-off, and a trusted publication step. There is no participant account service or custom submission application. Contribution format and checks are documented in `solve-proposals.md`; owner operations are in `proposal-verification.md`.

Each instance lives permanently in `data/<id>/`. Its protected target and prospective context exist before a solve. A solve PR adds proof sources, an explanation, and optional witness data to that same folder. After a checked merge, the publisher adds an acceptance receipt and derives the canonical solution record. The atlas, explanations, PR links, and leaderboard are generated from these records.

`formal/lean/` pins the shared contract, Lean toolchain, and mathlib manifest. `scripts/proposals/` implements source restrictions, sandboxed compilation, kernel replay, theorem/axiom auditing, owner review, and publication. `.github/workflows/` invokes trusted base-branch code; candidate workflow and setup files are never executed as part of solve verification.

`docs/technical/index.json` and its Markdown sources define the expandable technical chapters. The content builder renders bundled KaTeX and local HTML. `assets/` contains local runtime scripts, styles, fonts, avatars, and meshes. `slices/` saves per-instance planes and cameras. No external runtime requests are needed to view the site.

The loopback preview watches content and UI files, rebuilds valid edits, and refreshes the browser while preserving its route. It defers refresh during free-camera exploration. Publication and remote repository changes require separate owner authorization.
