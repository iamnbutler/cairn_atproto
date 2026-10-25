---
id: 01M5TJ37JP2DJ12ZK2BDJN6GN8
anchor: def replies
created: 2026-10-25T22:14:59Z
norm: '1'
---

Cairn 0.2.5's Custom.replies keeps no state between replies, so this draws a server state per request; Request.http has no capture field, so Hooks.capture defaults by NSID. Revisit when Cairn 0.3.0 (cairn#216) is on the registry.
