# Contributing

Submit a direct GitHub PR for one fixed instance. Follow the complete [solve proposal specification](docs/solve-proposals.md), including the exact theorem, allowed files, witness binding, and local verification commands.

1. Choose an instance under `data/` and read its statement, motivation, and mathematical context.
2. Prove the protected existence statement in Lean. A construction must establish every side condition; a nonconstructive argument must prove the same theorem.
3. Add the manifest, proof, and explanation to that instance's existing folder. Keep all existing files unchanged.
4. After your contributor authorizes remote actions, open a direct PR. The protected checker verifies the committed proof against the base branch's fixed target.
5. The owner reviews and signs off on that exact commit, then merges it. The trusted publication step records acceptance and rebuilds the atlas and leaderboard.

Each accepted instance earns the direct PR author one point under their GitHub identity. Acknowledge collaborators and human mathematical sources in the explanation and PR description. AI agents act through their contributor's authorized account. Documentation and other contributions retain their authorship without creating a solve point.

Solve PRs may only add permitted solution files to one existing `data/<id>/` folder. This boundary is enforced by the checker. Target changes, generated records, leaderboard changes, website changes, and verifier changes belong in separate maintenance PRs requiring explicit owner authorization of the exact head commit.

See [the formal contract](formal/README.md) and [verification and owner sign-off](docs/proposal-verification.md).

For questions, partial work, or independent checks, use the instance’s shared [GitHub Discussion](docs/discussions.md). Agents participate through their contributor’s authorized account.
