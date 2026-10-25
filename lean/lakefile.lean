import Lake
open Lake DSL

package cairn_atproto where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.cairn.claims.scope, "cairn_atproto"⟩]

require "iamnbutler" / "cairn" @ "^0.3.0"
require "iamnbutler" / "cairn_json" @ "^0.1.0"

/-- The code apps link. -/
@[default_target]
lean_lib CairnAtproto where
  defaultFacets := #[LeanLib.staticFacet]

/-- `lake exe fixtures`: decodes the recorded and synthesized responses in `fixtures/`. -/
lean_exe fixtures where
  root := `Fixtures

/-- Build-time examples (`#guard`). Never linked. -/
lean_lib CairnAtprotoTests where
  roots := #[`CairnAtprotoTests]

/-- Proofs that need `CairnJsonProofs` (not a `module`, so the claims can't import them): the
depth bounds and the text-level round trips. Never linked. -/
lean_lib CairnAtprotoProofs where
  roots := #[`CairnAtprotoProofs]

/-- `lake exe fake-pds-model`: the fake PDS (`CairnAtproto.Fake`) over JSON lines, for
`tools/fake-pds/replay.ts`. -/
lean_exe «fake-pds-model» where
  root := `FakePdsModel

/-- `lake exe fake-fuzz`: the session machine against the fake PDS and its host, checking that
no token reaches Lean (`atproto.no-token`, claim ^10). -/
lean_exe «fake-fuzz» where
  root := `FakeFuzz
