import Lake
open Lake DSL

package cairn_atproto where
  leanOptions := #[⟨`weak.cairn.claims.scope, "cairn_atproto"⟩]

require "iamnbutler" / "cairn" @ "^0.2.5"
require "iamnbutler" / "cairn_json" @ "^0.1.0"

@[default_target]
lean_lib CairnAtproto where
  defaultFacets := #[LeanLib.staticFacet]
