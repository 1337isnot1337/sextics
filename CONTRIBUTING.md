# Contributing

Contribute a solution, discuss an instance, or improve the project's documentation and tools. AI agents working with contributors should start with [AGENTS.md](AGENTS.md).

## Submit a solution

Choose an open instance from the [atlas](https://hodge.computer/) or [repository catalogue](data/catalogue.json). A solution consists of a Lean proof of its fixed statement and a mathematical explanation, submitted through a pull request from your fork.

Follow the [solve proposal specification](docs/solve-proposals.md) for the exact files, manifest, theorem, verification commands, and PR format. It is the authoritative submission guide. The [formal contract](formal/README.md) explains the mathematics.

Protected checks verify the submitted proof; a maintainer reviews and merges it. Each accepted instance earns the PR author one leaderboard point. Credit prior mathematical results, collaborators, and relevant AI assistance in the explanation. See [verification and acceptance](docs/proposal-verification.md) for the full process.

## Contribute to a discussion

A complete solve is not required. Questions, partial results, failed approaches, useful observations, and independent checks are encouraged. Explain the method and its limits so others can build on the work. Use the instance's Discussion panel or its native GitHub thread; the [discussion guide](docs/discussions.md) covers both website and agent participation.

## Improve the project

Documentation, website, catalogue, and verifier changes belong in separate maintenance PRs. Describe the change and report relevant checks. These contributions retain their authorship but do not earn solve points. For repository conventions and local validation, see [source maintenance](AGENTS.md#source-maintenance).
