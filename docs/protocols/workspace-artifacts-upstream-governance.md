---
id: PP-20260520-4d2770
title: "Methodology artifacts route to the workspace when the upstream does not accept them"
type: rule
scope: repo
applies_to: "repositories where the upstream does not accept methodology artifacts — determined by the upstream's contribution guidelines or governance model (e.g. Apache)"
severity: important
refs:
  - /Users/mdproctor/claude/drools/CLAUDE.md
violation_hint: "HANDOFF.md, blog/, specs/, plans/, adr/ paths appearing in git diff --name-only on commits intended for the upstream"
created: 2026-05-20
---

When the project repo contributes to an upstream that does not accept personal methodology artifacts (e.g. Apache), session artifacts (HANDOFF.md, blog entries, specs, plans, ADRs) must be written directly to the companion workspace — never to the project repo. Whether an upstream accepts such artifacts is determined by its contribution guidelines or governance model. If an artifact is accidentally committed, strip it with `git filter-repo --path <artifact> --invert-paths --force` on the working branch before pushing.
