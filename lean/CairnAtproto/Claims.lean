module

public import Cairn.Claims.Core
meta import Cairn.Claims.Elab
public import CairnAtproto.Proofs.Session

/-! # The session machine's claims

The claims about `CairnAtproto.Session` (`cairn_atproto^N`), stated over a harness `machine`
whose state is a `Session.Model` (the session and the log of every step it took). Its moves
are the app's inputs (`signIn`, `resume`, a call, `signOut`) and its `receive` hands every
reply to the session (`Input.reply`). The payloads are fixed (the harness signs in to
`probeHost` with blank credentials and makes `getTimeline` calls) because the claims don't
depend on them: each invariant's `holds` is `Ok m ∧ P m`, and `Ok.feed` keeps `Ok` for *every*
input (`CairnAtproto.Proofs.Session`), so `P` holds after any sequence of inputs, from any app.

| Id | Claim |
|---|---|
| ^1–^4 | the app's inputs: sign in, resume, a call, sign out |
| ^5 | at most one `refreshSession` in flight |
| ^6 | every call sent at most twice |
| ^7 | a call is sent again only in the step a refresh succeeds |
| ^8 | signed out (or signing in), no request carrying a Keychain secret is issued |
| ^9 | a failed refresh ends every held call; a refused one forgets both items |
| ^10 | no Lean value holds a token (assumed; evidence: `SessionInfo.ofJson_replaceTokens` and #208's fuzz) | -/

@[expose] public section

namespace CairnAtproto.Claims
open Cairn Cairn.Claims CairnAtproto.Session

/-- The host the harness signs in to and resumes with. -/
def probeHost : String := "https://bsky.social"

/-- Each invariant: `Ok`, which every step keeps, and the property it claims. -/
theorem keeps {P : Model → Prop} (hp : ∀ m, Ok m → P m) (m : Model) (i : Input)
    (h : Ok m ∧ P m) : Ok (m.feed i) ∧ P (m.feed i) :=
  ⟨h.1.feed i, hp _ (h.1.feed i)⟩

move ^1 signInMove (s : Model) "Sign in" where
  does "Sign in with a handle and an app password."
  sees "A createSession request goes out with the password marked redact, or the session answers busy."
  on press
    apply := s.feed (.signIn probeHost "" "")
    post s' := s'.s.phase.noSession = true ∨ s'.s = s.s
    sound := by
      intro s
      simp only [signInMove.press.apply, signInMove.press.post, Model.feed, step]
      split
      · split <;> simp [Phase.noSession]
      · split <;> simp [Phase.noSession]
      · simp

move ^2 resumeMove (s : Model) "Resume" where
  does "Launch with a saved service: resume the session the Keychain items hold."
  sees "At launch a refreshSession request goes out, authorised by the refresh item; later, nothing happens."
  on press
    apply := s.feed (.resume probeHost)
    post s' := s.s.phase = .launched → s'.s.phase.isRefreshing = true
    sound := by intro s h; simp [resumeMove.press.apply, Model.feed, step, h, Phase.isRefreshing]

move ^3 callMove (s : Model) (k : Nat) "Make a call" where
  does "Make an XRPC call (here getTimeline) with id k."
  sees "Signed in, it is sent with the access item; refreshing, it is held; otherwise it is answered signedOut."
  on press
    apply := s.feed (.call k (Call.getTimeline))
    post s' := s'.s.nextTicket = s.s.nextTicket + 1
    sound := by
      intro s k
      simp only [callMove.press.apply, callMove.press.post, Model.feed, step]
      split <;> simp [sendCall]

move ^4 signOutMove (s : Model) "Sign out" where
  does "Sign out."
  sees "Both Keychain items are forgotten, every held call is answered signedOut, and the session is signed out."
  on press
    apply := s.feed .signOut
    post s' := s'.s.phase = .signedOut ∧ s'.s.held = []
    sound := by intro s; simp [signOutMove.press.apply, signOutMove.press.post, Model.feed, step, forgetBoth]

/-- The host's replies go to the session; nothing else reaches it. -/
def receive (s : Model) : Msg → Model × List Effect
  | .reply id r => (s.feed (.reply id r), [])
  | _ => (s, [])

def machine : Machine Model := { init := {}, moves := moves%, receive }

theorem receive_keeps {P : Model → Prop} (hp : ∀ m, Ok m → P m) (s : Model) (m : Msg)
    (h : Ok s ∧ P s) : Ok (machine.receive s m).1 ∧ P (machine.receive s m).1 := by
  cases m with
  | reply id r => exact keeps hp s _ h
  | _ => exact h

theorem update_keeps {P : Model → Prop} (hp : ∀ m, Ok m → P m) :
    ∀ s a, (Ok s ∧ P s) → Ok (machine.update s a).1 ∧ P (machine.update s a).1 :=
  machine.preserves <|
    Move.all_cons (signInMove.preserves _ fun s h => keeps hp s _ h)
      (Move.all_cons (resumeMove.preserves _ fun s h => keeps hp s _ h)
      (Move.all_cons (callMove.preserves _ fun s _ h => keeps hp s _ h)
      (Move.all_cons (signOutMove.preserves _ fun s h => keeps hp s _ h) Move.all_nil)))

invariant ^5 oneRefresh "One refresh at a time" for machine where
  does "At most one refreshSession request is in flight: a call answered ExpiredToken while one is in flight joins it."
  holds m := Ok m ∧ OneRefresh m.log
  init := ⟨Ok.init, Ok.init.inv.oneRefresh⟩
  step := update_keeps fun _ h => h.inv.oneRefresh
  receive := receive_keeps fun _ h => h.inv.oneRefresh

invariant ^6 atMostTwice "A call is sent at most twice" for machine where
  does "Every call the app makes is sent at most twice."
  holds m := Ok m ∧ AtMostTwice m.log
  init := ⟨Ok.init, Ok.init.inv.atMostTwice⟩
  step := update_keeps fun _ h => h.inv.atMostTwice
  receive := receive_keeps fun _ h => h.inv.atMostTwice

invariant ^7 retryAfterRefresh "A second send only after a successful refresh" for machine where
  does "A call that was sent before is sent again only in the step a refresh in flight gets a 2xx session reply."
  holds m := Ok m ∧ RetryAfterRefresh m.log
  init := ⟨Ok.init, Ok.init.retry⟩
  step := update_keeps fun _ h => h.retry
  receive := receive_keeps fun _ h => h.retry

invariant ^8 noSecretSignedOut "Signed out, no secret is sent" for machine where
  does "While signed out or signing in, no request carrying a Keychain secret is issued."
  holds m := Ok m ∧ NoSecretSignedOut m.log
  init := ⟨Ok.init, Ok.init.noSecret⟩
  step := update_keeps fun _ h => h.noSecret
  receive := receive_keeps fun _ h => h.noSecret

invariant ^9 refusalEndsAll "A failed refresh ends the held calls" for machine where
  does "When the refresh in flight fails every held call is answered in that step; when it is refused both Keychain items are forgotten and the held calls are answered signedOut. Calls are held only while a refresh is in flight."
  holds m := Ok m ∧ RefusalEndsAll m
  init := ⟨Ok.init, Ok.init.refusal⟩
  step := update_keeps fun _ h => h.refusal
  receive := receive_keeps fun _ h => h.refusal

assume ^10 noTokens "No Lean value holds a token" where
  does "No type in cairn_atproto holds an access or refresh token: the session state has DIDs, handles, service URLs, request ids and the app's calls; SessionInfo has no token field and its decoder never reads accessJwt or refreshJwt (SessionInfo.ofJson_replaceTokens). By construction; checked by the trusted-base fuzz."
  check "atproto.no-token"

def claimInfos : List ClaimInfo := claims%

end CairnAtproto.Claims
