# Working context

Read `AGENTS.md` and the contribution specification before work. This is a static website whose exact targets, solution sources, explanations, and acceptance receipts live under `data/<id>/`.

A solve first enters through a direct PR adding only permitted files to an existing instance folder. The protected checker verifies the base target, source diff, Lean theorem, optional displayed witness, kernel replay, and axioms. The owner signs off and merges the checked head. The trusted publisher validates the merge and produces canonical solution records and leaderboard credit. See `docs/proposal-verification.md`.

Do not infer acceptance from a rendered mesh or a local compilation. Do not change status flags manually. Ask before remote operations or publication.

The local preview is `python3 scripts/preview.py` at `http://127.0.0.1:8765/`. Explore mode shows a small instance/status pill, a return toggle, and a collapsible general visualization guide. Returning eases the camera to its saved view. The geometry box is ±10 and x-ray reach is 2.0. Preserve the homepage's separately saved Contact cone plane and camera.
