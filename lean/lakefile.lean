import Lake
open Lake DSL

package cairn_atproto where
  leanOptions := #[⟨`weak.cairn.claims.scope, "cairn_atproto"⟩]

require "iamnbutler" / "cairn" @ "^0.2.5"
require "iamnbutler" / "cairn_json" @ "^0.1.0"

@[default_target]
lean_lib CairnAtproto where
  defaultFacets := #[LeanLib.staticFacet]

/-- `lake exe fixtures`: decodes the recorded and synthesized responses in `fixtures/`. -/
lean_exe fixtures where
  root := `Fixtures

/-- Build-time examples (`#guard`). Never linked. -/
lean_lib CairnAtprotoTests where
  roots := #[`CairnAtprotoTests]
