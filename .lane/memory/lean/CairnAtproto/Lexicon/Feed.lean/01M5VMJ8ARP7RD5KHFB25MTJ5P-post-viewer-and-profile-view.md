---
id: 01M5VMJ8ARP7RD5KHFB25MTJ5P
anchor: nonDefault
created: 2026-10-26T08:17:23Z
norm: '1'
---

Post.viewer and Profile.viewer are written only when not {} (nonDefault), so public and fake JSON is unchanged and tools/fake-pds/model.ts needs no viewer member. Adding a field to Post or Profile changes their anonymous-constructor arity: Sky's ⟨…⟩ patterns break on upgrade.
