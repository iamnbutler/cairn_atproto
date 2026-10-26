module

public import CairnAtproto.Lexicon.Feed

/-! # `app.bsky.actor` and `app.bsky.graph`: profiles and mutes

* **`ProfileDetail`** (`app.bsky.actor.getProfile`, `#profileViewDetailed`): the basic profile
  (with the viewer's state: following, muted, blocked) and its description and counts. The
  authoritative read of a mute: `muteActor` writes no record, so the AppView's
  `viewer.muted` is where a mute shows.
* **`muteActor`**, **`unmuteActor`** (`app.bsky.graph`): `{"actor": <DID or handle>}`; both
  answer 200 with no body, and muting a muted account (or unmuting one that isn't) succeeds.

The calls are `Session.Call.getProfile`, `muteActor` and `unmuteActor` (`CairnAtproto.Acts`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

def nsidGetProfile : String := "app.bsky.actor.getProfile"
def nsidMuteActor : String := "app.bsky.graph.muteActor"
def nsidUnmuteActor : String := "app.bsky.graph.unmuteActor"

/-- `app.bsky.actor.defs#profileViewDetailed`, the parts Sky reads. -/
structure ProfileDetail where
  /-- DID, handle, display name, avatar and the viewer's state. -/
  profile : Profile
  description : Option String := none
  followersCount : Nat := 0
  followsCount : Nat := 0
  postsCount : Nat := 0
deriving Repr, DecidableEq, Inhabited

def ProfileDetail.ofJson (j : Json) : Option ProfileDetail := do
  let profile ← Profile.ofJson j
  some { profile, description := j.str? "description",
         followersCount := (j.nat? "followersCount").getD 0,
         followsCount := (j.nat? "followsCount").getD 0, postsCount := (j.nat? "postsCount").getD 0 }

/-- The profile's members, then the detail's. -/
def ProfileDetail.toJson (d : ProfileDetail) : Json :=
  match d.profile.toJson with
  | .obj kvs => .obj (kvs ++ opt "description" Json.str d.description ++
      [("followersCount", Json.ofNat d.followersCount), ("followsCount", Json.ofNat d.followsCount),
       ("postsCount", Json.ofNat d.postsCount)])
  | j => j

/-- `muteActor` / `unmuteActor`'s input. -/
def actorJson (actor : String) : Json := .obj [("actor", .str actor)]

end CairnAtproto
