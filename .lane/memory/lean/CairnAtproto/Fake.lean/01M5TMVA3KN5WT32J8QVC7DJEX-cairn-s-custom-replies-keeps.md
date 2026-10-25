---
id: 01M5TMVA3KN5WT32J8QVC7DJEX
anchor: def replies
created: 2026-10-25T23:03:06Z
norm: '1'
supersedes: 01M5TJ37JP2DJ12ZK2BDJN6GN8
---

Cairn's Custom.replies keeps no state between replies, so this draws a server state per request. The token a request carries and what the host captures come from the Request itself (itemOf, captureOf); Hooks.capture overrides capture only for the leak-detection control run.
