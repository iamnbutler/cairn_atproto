import CairnAtproto
import Cairn.Claims.Core
import Cairn.Claims.Elab

/-! # FakeApp: a small app for `cairn fuzz` against the fake PDS as a server

`Fake.server` (cairn#260's `Cairn.Fuzz.Server`) run for real: `make fuzz-app`, or `cairn fuzz
FakeApp` in this package, walks this app through Cairn's runtime with the whole fake PDS and its
host's Keychain as the server's world, so the app's likes persist through a sequence, replies
fail before the server acts or are lost after, and between steps posts arrive, other accounts
act, the AppView catches up and the access token expires.

The app opens a saved session (the world starts with the Keychain holding a signed-in session's
tokens, `Fake.World.saved`, as Sky's does at launch: the fake's identifier and password come from the
seed the world draws, which the app can't know), loads the timeline, likes posts from it and
signs out. Its calls go through `CairnAtproto.Session`, which refreshes the rotated tokens.

Claims (scope `fake_app`, unpublished; the library is never linked by an app):

| Id | Kind | What |
|---|---|---|
| ^1 | place | the window |
| ^2–^5 | move | open the saved session, load the timeline, like a post, sign out |
| ^6 | invariant | a like the server acknowledged shows liked; `cairn fuzz` checks the server holds it, after every step and once every reply is in |
-/

namespace FakeApp
open Cairn Cairn.Claims CairnAtproto CairnAtproto.Session

/-- How many posts of the timeline the window shows. -/
def shown : Nat := 4

structure State where
  session : Session.State := {}
  /-- The app's next call id. -/
  nextCall : Nat := 1
  /-- The `getTimeline` call in flight. -/
  timelineCall : Option Nat := none
  /-- The posts shown, newest first. -/
  posts : List Post := []
  /-- Like calls in flight: call id and the post's URI. -/
  pending : List (Nat × String) := []
  /-- Posts whose like the server acknowledged (2xx). -/
  acked : List String := []
  /-- The last problem, in words. -/
  note : String := ""
deriving Inhabited

/-- Whether post `uri` shows liked: acknowledged, or its like in flight. -/
def State.likedShown (s : State) (uri : String) : Bool :=
  s.acked.contains uri || s.pending.any (·.2 == uri)

def State.signedIn (s : State) : Option Account :=
  match s.session.phase with
  | .signedIn a => some a
  | _ => none

/-- The service the app saved: the fake's (`Fake.Config.service`). -/
def service : String := ({} : Fake.Config).service

/-- How call `id` ended. -/
def onAnswer (s : State) (id : Nat) (a : Answer) : State :=
  if s.timelineCall = some id then
    match a with
    | .reply r => match Outcome.ofReply FeedPage.ofJson r with
      | .ok p => { s with timelineCall := none, posts := (p.feed.map (·.post)).take shown, note := "" }
      | _ => { s with timelineCall := none, note := "Couldn't load the timeline." }
    | .signedOut => { s with timelineCall := none, note := "Signed out." }
  else match s.pending.lookup id with
    | some uri =>
      let s := { s with pending := s.pending.filter (·.1 != id) }
      match WriteOutcome.ofAnswer a with
      | .acked => { s with acked := if s.acked.contains uri then s.acked else uri :: s.acked }
      | _ => { s with note := "A like didn't go through." }
    | none => s

/-- What the app does with one thing the session puts out. -/
def handleOut (acc : State × List Effect) : Out → State × List Effect
  | .send rid _ r => (acc.1, acc.2 ++ [.request rid r])
  | .forget rid item => (acc.1, acc.2 ++ [.request rid (.forgetSecret item)])
  | .cancel rid => (acc.1, acc.2 ++ [.cancelRequest rid])
  | .answer id a => (onAnswer acc.1 id a, acc.2)
  | .event _ => acc

/-- One input to the session, and what the app does with everything it puts out. -/
def drive (s : State) (i : Input) : State × List Effect :=
  (Session.step s.session i).2.foldl handleOut ({ s with session := (Session.step s.session i).1 }, [])

/-- Like the post at `uri` (its CID `cid`) as `a`, with a record key from the call id. -/
def likeCall (s : State) (a : Account) (p : Post) : State × List Effect :=
  let rkey := (Tid.ofNat? s.nextCall).map Tid.encode |>.getD "2222222222222"
  let w : PutRecord := { repo := a.did, rkey, record := .likeOf p "2026-10-26T12:00:00.000Z" }
  drive { s with nextCall := s.nextCall + 1, pending := (s.nextCall, p.uri) :: s.pending }
    (.call s.nextCall (Call.putRecord w))

def likePress (s : State) (k : Nat) : State × List Effect :=
  match s.signedIn, s.posts[k - 1]? with
  | some a, some p => likeCall s a p
  | _, _ => (s, [])

def loadPress (s : State) : State × List Effect :=
  drive { s with nextCall := s.nextCall + 1, timelineCall := some s.nextCall }
    (.call s.nextCall (Call.getTimeline (some shown)))

/-! The acknowledged likes only grow. -/

theorem onAnswer_acked (s : State) (id : Nat) (a : Answer) : s.acked ⊆ (onAnswer s id a).acked := by
  unfold onAnswer
  split
  · split
    · split <;> exact List.Subset.refl _
    · exact List.Subset.refl _
  · split
    · split
      · dsimp only; split
        · exact List.Subset.refl _
        · exact List.subset_cons_self _ _
      · exact List.Subset.refl _
    · exact List.Subset.refl _

theorem handleOut_acked (acc : State × List Effect) (o : Out) :
    acc.1.acked ⊆ (handleOut acc o).1.acked := by
  cases o <;> simp only [handleOut] <;> first | exact List.Subset.refl _ | exact onAnswer_acked _ _ _

theorem foldl_acked : ∀ (os : List Out) (acc : State × List Effect),
    acc.1.acked ⊆ (os.foldl handleOut acc).1.acked
  | [], _ => List.Subset.refl _
  | o :: os, acc => fun _ h => foldl_acked os (handleOut acc o) (handleOut_acked acc o h)

theorem drive_acked (s : State) (i : Input) : s.acked ⊆ (drive s i).1.acked :=
  foldl_acked (Session.step s.session i).2 ({ s with session := (Session.step s.session i).1 }, [])

/-- `drive` from a state with the same acknowledged likes. -/
theorem drive_acked' {s : State} (t : State) (i : Input) (h : t.acked = s.acked) :
    s.acked ⊆ (drive t i).1.acked := fun _ hx => drive_acked t i (h ▸ hx)

theorem loadPress_acked (s : State) : s.acked ⊆ (loadPress s).1.acked := by
  unfold loadPress; exact drive_acked' _ _ rfl

theorem likePress_acked (s : State) (k : Nat) : s.acked ⊆ (likePress s k).1.acked := by
  unfold likePress likeCall
  split
  · exact drive_acked' _ _ rfl
  · exact List.Subset.refl _

theorem signOut_acked (s : State) : s.acked ⊆ (drive s .signOut).1.acked := drive_acked _ _

theorem resume_acked (s : State) : s.acked ⊆ (drive s (.resume service)).1.acked := drive_acked _ _

place ^1 window "FakeApp window" where
  does "The window: Open, Load, Sign out, the timeline's newest posts with a Like each, and a line for problems."

def openRef : ControlRef := ⟨2, 0⟩
def loadRef : ControlRef := ⟨3, 0⟩
def likeRef (k : Nat) : ControlRef := ⟨4, k⟩
def signOutRef : ControlRef := ⟨5, 0⟩

move ^2 openSession (s : State) "Open the saved session" in ^1 where
  does "Press Open: resume the session the Keychain items hold."
  sees "A refreshSession request goes out with the refresh item; once it answers, the app is signed in."
  enabled := s.session.phase == .launched
  on press
    emit := drive s (.resume service)
    post s' := s.acked ⊆ s'.acked
    sound := by intro s _; exact resume_acked s

move ^3 load (s : State) "Load the timeline" in ^1 where
  does "Press Load."
  sees "A getTimeline call goes out; its answer replaces the posts shown."
  enabled := s.signedIn.isSome && s.timelineCall.isNone
  on press
    emit := loadPress s
    post s' := s.acked ⊆ s'.acked
    sound := by intro s _; exact loadPress_acked s

move ^4 like (s : State) (k : Nat) "Like a post" in ^1 where
  does "Press a post's Like."
  sees "It shows liked at once; a putRecord of a like goes out. Acknowledged, it stays liked; otherwise it doesn't."
  enabled := s.signedIn.isSome && 1 ≤ k && k ≤ s.posts.length
  on press
    emit := likePress s k
    post s' := s.acked ⊆ s'.acked
    sound := by intro s k _; exact likePress_acked s k

move ^5 signOut (s : State) "Sign out" in ^1 where
  does "Press Sign out."
  sees "Both Keychain items are forgotten and every call in flight is answered signed out."
  enabled := s.signedIn.isSome
  on press
    emit := drive s .signOut
    post s' := s.acked ⊆ s'.acked
    sound := by intro s _; exact signOut_acked s

/-- The host's replies go to the session. -/
def receive (s : State) : Msg → State × List Effect
  | .reply id r => drive s (.reply id r)
  | _ => (s, [])

def machine : Machine State := { init := {}, moves := moves%, receive }

theorem acked_shown (s : State) : ∀ u ∈ s.acked, s.likedShown u = true := by
  intro u h
  simp [State.likedShown, h]

invariant ^6 ackedShown "An acknowledged like shows liked" for machine where
  does "A post whose like the server acknowledged shows liked. `cairn fuzz` checks that the server holds every acknowledged like, after every step and once every reply is in, against the fake PDS (`Fake.server`): replies failing before it acts or lost after, tokens expiring and rotating, other accounts acting."
  holds s := ∀ u ∈ s.acked, s.likedShown u = true
  init := acked_shown _
  step := fun _ _ _ => acked_shown _
  receive := fun _ _ _ => acked_shown _

def claimInfos : List ClaimInfo := claims%

/-! ## View -/

def ink : Color := ⟨28, 28, 30, 255⟩
def muted : Color := ⟨120, 120, 128, 255⟩
def accent : Color := ⟨0, 122, 255, 255⟩

def button (r : ControlRef) (label : String) : Node :=
  .box { padding := ⟨6, 16, 6, 16⟩, radius := 6, background := some accent }
    (some { ref := r, label })
    [.text { font := { size := 13 }, color := ⟨255, 255, 255, 255⟩ } label]

def postRow (s : State) (k : Nat) (p : Post) : Node :=
  let liked := s.likedShown p.uri
  .box { axis := .row, width := .fill, gap := 8, align := .center } none
    [ .box { padding := ⟨3, 8, 3, 8⟩, radius := 4 }
        (some { ref := likeRef k, label := s!"Like post {k}", checked := some liked })
        [.text { font := { size := 13 }, color := ink } (if liked then "♥" else "♡")],
      .text { font := { size := 13 }, color := ink } (p.uri.takeEnd 12).toString ]

def view (s : State) (_ : UI) : Node :=
  .box { width := .fill, height := .fill, padding := ⟨16, 16, 16, 16⟩, gap := 8, clip := true } none
    ([ .box { axis := .row, gap := 8 } none
        ((if s.session.phase == .launched then [button openRef "Open"] else []) ++
         (if s.signedIn.isSome && s.timelineCall.isNone then [button loadRef "Load"] else []) ++
         (if s.signedIn.isSome then [button signOutRef "Sign out"] else [])) ] ++
     (if s.signedIn.isSome then (s.posts.zipIdx 1).map fun (p, k) => postRow s k p else []) ++
     [.text { font := { size := 13 }, color := muted } s.note])

def app : App State := machine.toApp [.window 1 "FakeApp" view] claimInfos

/-! ## The fuzz setup -/

/-- Every like the server acknowledged is in the tester's repo. -/
def ackedHeld (s : State) (w : Fake.World) : Bool := s.acked.all (w.likedBy ·)

/-- Likes most; Sign out only once a like is acknowledged, since a sequence that signs out can't
like again (the fake's password is the world's). -/
def weights (s : State) (r : ControlRef) : Nat :=
  if r.claim == 4 then 8 else if r.claim == 3 then 3
  else if r.claim == 5 then (if s.acked.isEmpty then 0 else 1) else 1

def fuzz : Cairn.Fuzz.Custom State where
  weights := weights
  server := some { Fake.server {} [(6, ackedHeld)] [(6, ackedHeld)] with
    init := Fake.World.saved <$> Fake.worldGen {} }

end FakeApp
