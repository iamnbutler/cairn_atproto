module

public import CairnAtproto.Session

/-! # What the session machine guarantees

The claims (`CairnAtproto.Claims`) are stated over a `Model`: the session's state and the log
of every step it has taken (the state before, the input, everything it put out), newest first.
What they say is read off the log, from what an observer of the session's inputs and outputs
sees: requests sent (`sentIn`), requests answered (a `reply` input), requests in flight
(`openIn`), and how many times each call was sent (`sendsOf`). The proofs here hold for every
input, so for every app.

* `step_noSecret`: with no session, no step sends a request with a secret.
* `step_refused`: a refused refresh forgets both items and answers every held call.
* `Inv` (the session's bookkeeping agrees with the log) is kept by every step
  (`Inv.feed`), and gives at most one refresh in flight (`Inv.oneRefresh`), every call sent at
  most twice (`Inv.twice`) and a second send only on a successful refresh
  (`Inv.retryAfterRefresh`). -/

@[expose] public section

namespace CairnAtproto.Session
open CairnAtproto

/-! ## The log -/

/-- One step: the state before, the input, and what it put out. -/
structure Entry where
  before : State
  input : Input
  outs : List Out

/-- The session and every step it took, newest first. -/
structure Model where
  s : State := init
  log : List Entry := []

def Model.feed (m : Model) (i : Input) : Model :=
  { s := (step m.s i).1, log := ⟨m.s, i, (step m.s i).2⟩ :: m.log }

def Out.sent? : Out → Option (Nat × Kind)
  | .send rid k _ => some (rid, k)
  | _ => none

/-- The requests a step sent, with what each is for. -/
def sentIn (os : List Out) : List (Nat × Kind) := os.filterMap Out.sent?

/-- Whether the input is the reply to request `rid`. -/
def Input.replies : Input → Nat → Bool
  | .reply r _, rid => r == rid
  | _, _ => false

/-- Every request sent. -/
def allSent : List Entry → List (Nat × Kind)
  | [] => []
  | e :: rest => sentIn e.outs ++ allSent rest

/-- The requests sent and not yet answered. -/
def openIn : List Entry → List (Nat × Kind)
  | [] => []
  | e :: rest => sentIn e.outs ++ (openIn rest).filter (fun x => !e.input.replies x.1)

/-- How many times call `t` has been sent. -/
def sendsOf (t : Nat) (log : List Entry) : Nat := (allSent log).countP (·.2 == .call t)

/-- `P` held of every step, given the steps before it. -/
def Steps (P : Entry → List Entry → Prop) : List Entry → Prop
  | [] => True
  | e :: rest => P e rest ∧ Steps P rest

/-! ## What the claims say -/

def Phase.noSession : Phase → Bool
  | .signedOut | .signingIn .. => true
  | _ => false

def Phase.isRefreshing : Phase → Bool
  | .refreshing .. => true
  | _ => false

def Out.hasSecret : Out → Bool
  | .send _ _ h => h.secret.isSome
  | _ => false

/-- With no session (signed out, or signing in), a step sends nothing with a Keychain secret. -/
def NoSecretSignedOut (log : List Entry) : Prop :=
  Steps (fun e _ => e.before.phase.noSession = true → ∀ o ∈ e.outs, o.hasSecret = false) log

/-- The step answers the refresh in flight with a failure: anything but a session. -/
def FailedRefresh (e : Entry) : Prop :=
  ∃ rid host a r, e.before.phase = .refreshing rid host a ∧ e.input = .reply rid r ∧
    sessionOf r = none

/-- Every held call answered in that step. -/
def HeldEnded (e : Entry) : Prop := ∀ p ∈ e.before.held, ∃ a, Out.answer p.id a ∈ e.outs

/-- The step answers the refresh in flight with a refusal. -/
def RefusedRefresh (e : Entry) : Prop :=
  ∃ rid host a r, e.before.phase = .refreshing rid host a ∧ e.input = .reply rid r ∧
    sessionOf r = none ∧ transient r = false

/-- Both items forgotten and every held call answered `signedOut`, in that step. -/
def EndsHeld (e : Entry) : Prop :=
  (∃ rid, Out.forget rid accessItem ∈ e.outs) ∧ (∃ rid, Out.forget rid refreshItem ∈ e.outs) ∧
    ∀ p ∈ e.before.held, Out.answer p.id .signedOut ∈ e.outs

/-- A failed refresh ends every held call; a refused one also forgets both items and answers the
held calls `signedOut`; and calls are held only while a refresh is in flight. -/
def RefusalEndsAll (m : Model) : Prop :=
  Steps (fun e _ => (FailedRefresh e → HeldEnded e) ∧ (RefusedRefresh e → EndsHeld e)) m.log ∧
    (m.s.phase.isRefreshing = false → m.s.held = [])

/-- At most one `refreshSession` in flight. -/
def OneRefresh (log : List Entry) : Prop := ((openIn log).filter (·.2 == .refresh)).length ≤ 1

/-- Every call sent at most twice. -/
def AtMostTwice (log : List Entry) : Prop := ∀ t, sendsOf t log ≤ 2

/-- The step is a 2xx reply to a refresh in flight. -/
def RefreshSucceeded (e : Entry) (rest : List Entry) : Prop :=
  ∃ rid st hs b, e.input = .reply rid (.http st hs b) ∧ isSuccess st = true ∧
    (rid, Kind.refresh) ∈ openIn rest

/-- A call sent again is sent in the step a refresh succeeds. -/
def RetryAfterRefresh (log : List Entry) : Prop :=
  Steps (fun e rest => ∀ t, 0 < (sentIn e.outs).countP (·.2 == .call t) → 0 < sendsOf t rest →
    RefreshSucceeded e rest) log

/-! ## No session, no secret -/

theorem createSession_secret (h i p : String) : (createSession h i p).secret = none := rfl

theorem forgetBoth_noSecret (s : State) : ∀ o ∈ (forgetBoth s).2, o.hasSecret = false := by
  simp [forgetBoth, Out.hasSecret]

theorem answerAll_noSecret (ps : List Pending) (a : Answer) :
    ∀ o ∈ answerAll ps a, o.hasSecret = false := by
  simp [answerAll, Out.hasSecret]

theorem onCallReply_noSecret (s : State) (rid : Nat) (r : Cairn.Reply)
    (h : s.phase.noSession = true) : ∀ o ∈ (onCallReply s rid r).2, o.hasSecret = false := by
  unfold onCallReply
  split
  · exact forgetBoth_noSecret _
  · split
    · simp
    · split
      · cases hph : s.phase <;> simp_all [Phase.noSession, Out.hasSecret]
      · simp [Out.hasSecret]

theorem step_noSecret (s : State) (i : Input) (h : s.phase.noSession = true) :
    ∀ o ∈ (step s i).2, o.hasSecret = false := by
  cases i with
  | signIn host id pw =>
    simp only [step]
    split
    · split <;> simp [Out.hasSecret, createSession_secret]
    · split <;> simp [Out.hasSecret, createSession_secret]
    · simp [Out.hasSecret]
  | resume host =>
    simp only [step]
    split
    · simp_all [Phase.noSession]
    · simp
  | call id c =>
    simp only [step]
    split <;> simp_all [Phase.noSession, Out.hasSecret]
  | signOut =>
    simp only [step]
    intro o ho
    simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with (ho | ho) | ho
    · exact answerAll_noSecret _ _ o ho
    · exact forgetBoth_noSecret _ o ho
    · subst ho; rfl
  | reply rid r =>
    simp only [step]
    split
    · split
      · unfold onSignIn
        split
        · simp [Out.hasSecret]
        · intro o ho
          simp only [List.mem_append, List.mem_singleton] at ho
          rcases ho with ho | ho
          · exact forgetBoth_noSecret _ o ho
          · subst ho; rfl
      · exact onCallReply_noSecret _ _ _ h
    · simp_all [Phase.noSession]
    · exact onCallReply_noSecret _ _ _ h

theorem noSecretSignedOut_feed (m : Model) (i : Input) (h : NoSecretSignedOut m.log) :
    NoSecretSignedOut (m.feed i).log :=
  ⟨fun hn => step_noSecret m.s i hn, h⟩

/-! ## A refused refresh -/

theorem step_refused (s : State) (i : Input) (h : RefusedRefresh ⟨s, i, (step s i).2⟩) :
    EndsHeld ⟨s, i, (step s i).2⟩ := by
  obtain ⟨rid, host, a, r, hp, hi, hs, ht⟩ := h
  simp only at hp hi
  subst hi
  simp only [EndsHeld, step, hp, ite_true, onRefresh, hs, ht, Bool.false_eq_true, ite_false,
    forgetBoth, answerAll]
  refine ⟨⟨s.next, by simp⟩, ⟨s.next + 1, by simp⟩, fun p hp => ?_⟩
  simp only [List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

theorem step_failed (s : State) (i : Input) (h : FailedRefresh ⟨s, i, (step s i).2⟩) :
    HeldEnded ⟨s, i, (step s i).2⟩ := by
  obtain ⟨rid, host, a, r, hp, hi, hs⟩ := h
  simp only at hp hi
  subst hi
  intro p hp'
  simp only [step, hp, ite_true, onRefresh, hs]
  split
  · refine ⟨.reply r, ?_⟩
    simp only [answerAll, List.mem_append, List.mem_map]
    exact Or.inl ⟨p, hp', rfl⟩
  · refine ⟨.signedOut, ?_⟩
    simp only [answerAll, forgetBoth, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl ⟨p, hp', rfl⟩)

theorem step_held (s : State) (i : Input) (h : s.phase.isRefreshing = false → s.held = []) :
    (step s i).1.phase.isRefreshing = false → (step s i).1.held = [] := by
  cases i <;> simp only [step, onCallReply, onSignIn, onRefresh, startRefresh, sendCall, sendAll,
    forgetBoth] <;> (repeat' split) <;> simp_all [Phase.isRefreshing]

theorem refusalEndsAll_feed (m : Model) (i : Input) (h : RefusalEndsAll m) :
    RefusalEndsAll (m.feed i) :=
  ⟨⟨⟨fun hf => step_failed m.s i hf, fun hr => step_refused m.s i hr⟩, h.1⟩, step_held m.s i h.2⟩

/-! ## The bookkeeping agrees with the log -/

def Phase.refreshRid : Phase → Option Nat
  | .refreshing rid _ _ => some rid
  | _ => none

/-- What the session's state says about the log it produced. -/
structure Inv (s : State) (log : List Entry) : Prop where
  /-- Every request id used is below `next`. -/
  fresh : ∀ x ∈ allSent log, x.1 < s.next
  /-- No call at or past `nextTicket` has been sent. -/
  ticketsFresh : ∀ t, s.nextTicket ≤ t → sendsOf t log = 0
  twice : ∀ t, sendsOf t log ≤ 2
  /-- A call in flight has been sent `tries` times. -/
  inflight : ∀ x ∈ s.inflight, sendsOf x.2.ticket log = x.2.tries ∧ x.2.ticket < s.nextTicket
  /-- A held call has been sent `tries` times, at most once. -/
  held : ∀ p ∈ s.held, sendsOf p.ticket log = p.tries ∧ p.tries ≤ 1 ∧ p.ticket < s.nextTicket
  /-- One pending call per ticket. -/
  distinct : (s.inflight.map (·.2.ticket) ++ s.held.map (·.ticket)).Nodup
  openSent : ∀ x ∈ openIn log, x ∈ allSent log
  openNodup : ((openIn log).map (·.1)).Nodup
  /-- A refresh in flight is the phase's, or abandoned. -/
  refreshes : ∀ x ∈ openIn log, x.2 = .refresh → s.phase.refreshRid = some x.1 ∨ x.1 ∈ s.abandoned
  phaseOpen : ∀ rid, s.phase.refreshRid = some rid → (rid, Kind.refresh) ∈ openIn log
  /-- At most one abandoned request, and only when signed out. -/
  abandoned : s.abandoned = [] ∨ (s.phase = .signedOut ∧ s.abandoned.length = 1)

theorem Inv.init : Inv Session.init [] where
  fresh := by simp [allSent]
  ticketsFresh := by simp [sendsOf, allSent]
  twice := by simp [sendsOf, allSent]
  inflight := by simp [Session.init]
  held := by simp [Session.init]
  distinct := by simp [Session.init]
  openSent := by simp [openIn]
  openNodup := by simp [openIn]
  refreshes := by simp [openIn]
  phaseOpen := by simp [Session.init, Phase.refreshRid]
  abandoned := by simp [Session.init]

/-! ### The log, one step at a time -/

@[simp] theorem allSent_cons (e : Entry) (rest : List Entry) :
    allSent (e :: rest) = sentIn e.outs ++ allSent rest := rfl

@[simp] theorem openIn_cons (e : Entry) (rest : List Entry) :
    openIn (e :: rest) = sentIn e.outs ++ (openIn rest).filter (fun x => !e.input.replies x.1) :=
  rfl

theorem sendsOf_cons (t : Nat) (e : Entry) (rest : List Entry) :
    sendsOf t (e :: rest) = (sentIn e.outs).countP (·.2 == .call t) + sendsOf t rest := by
  simp [sendsOf, List.countP_append]

@[simp] theorem sentIn_nil : sentIn [] = [] := rfl
@[simp] theorem sentIn_append (a b : List Out) : sentIn (a ++ b) = sentIn a ++ sentIn b := by
  simp [sentIn, List.filterMap_append]
@[simp] theorem sentIn_send (rid : Nat) (k : Kind) (h : Http) (os : List Out) :
    sentIn (.send rid k h :: os) = (rid, k) :: sentIn os := rfl
@[simp] theorem sentIn_forget (rid : Nat) (i : String) (os : List Out) :
    sentIn (.forget rid i :: os) = sentIn os := rfl
@[simp] theorem sentIn_answer (id : Nat) (a : Answer) (os : List Out) :
    sentIn (.answer id a :: os) = sentIn os := rfl
@[simp] theorem sentIn_event (e : Event) (os : List Out) : sentIn (.event e :: os) = sentIn os := rfl
@[simp] theorem sentIn_answerAll (ps : List Pending) (a : Answer) : sentIn (answerAll ps a) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [answerAll] at ih ⊢; exact ih

theorem mem_numbered {n : Nat} {ps : List Pending} {x : Nat × Pending} (h : x ∈ numbered n ps) :
    n ≤ x.1 ∧ x.1 < n + ps.length ∧ x.2 ∈ ps := by
  induction ps generalizing n with
  | nil => simp [numbered] at h
  | cons p ps ih =>
    simp only [numbered, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h; simp only [List.length_cons, List.mem_cons]
      exact ⟨by omega, by omega, Or.inr this.2.2⟩

theorem numbered_snd (n : Nat) (ps : List Pending) : (numbered n ps).map (·.2) = ps := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih => simp [numbered, ih]

theorem numbered_fst (n : Nat) (ps : List Pending) :
    (numbered n ps).map (·.1) = List.range' n ps.length := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih => simp [numbered, ih, List.range'_succ]

theorem sentIn_sendAll (service : String) (s : State) (ps : List Pending) :
    sentIn (sendAll service s ps).2 = (numbered s.next ps).map (fun x => (x.1, Kind.call x.2.ticket)) := by
  simp only [sendAll]
  generalize numbered s.next ps = ns
  induction ns with
  | nil => rfl
  | cons x ns ih => simp [ih]

theorem mem_openIn_cons {x : Nat × Kind} {e : Entry} {rest : List Entry} :
    x ∈ openIn (e :: rest) ↔ x ∈ sentIn e.outs ∨ (x ∈ openIn rest ∧ e.input.replies x.1 = false) := by
  simp

theorem countP_call_zero {l : List (Nat × Kind)} (h : ∀ x ∈ l, ∀ t, x.2 ≠ .call t) (t : Nat) :
    l.countP (·.2 == .call t) = 0 := by
  rw [List.countP_eq_zero]; intro x hx; simpa using h x hx t

/-- A step that sends no call (at most sign-in and refresh requests, under fresh ids) keeps `Inv`
when its new state only drops or moves pending calls (a call moves from in flight to held only
after one send) and keeps the refresh facts. -/
theorem Inv.noCalls {s s' : State} {log : List Entry} {i : Input} {os : List Out}
    (h : Inv s log)
    (hos : ∀ x ∈ sentIn os, s.next ≤ x.1 ∧ x.1 < s'.next ∧ ∀ t, x.2 ≠ .call t)
    (hosNodup : ((sentIn os).map (·.1)).Nodup)
    (hnext : s.next ≤ s'.next) (htick : s.nextTicket ≤ s'.nextTicket)
    (hinfl : ∀ x ∈ s'.inflight, sendsOf x.2.ticket log = x.2.tries ∧ x.2.ticket < s'.nextTicket)
    (hheld : ∀ p ∈ s'.held, sendsOf p.ticket log = p.tries ∧ p.tries ≤ 1 ∧ p.ticket < s'.nextTicket)
    (hdist : (s'.inflight.map (·.2.ticket) ++ s'.held.map (·.ticket)).Nodup)
    (hnew : ∀ x ∈ sentIn os, x.2 = .refresh → s'.phase.refreshRid = some x.1 ∨ x.1 ∈ s'.abandoned)
    (hrefresh : ∀ x ∈ openIn log, x.2 = .refresh → i.replies x.1 = false →
      s'.phase.refreshRid = some x.1 ∨ x.1 ∈ s'.abandoned)
    (hphase : ∀ rid, s'.phase.refreshRid = some rid → (rid, Kind.refresh) ∈ sentIn os ∨
      ((rid, Kind.refresh) ∈ openIn log ∧ i.replies rid = false))
    (hab : s'.abandoned = [] ∨ (s'.phase = .signedOut ∧ s'.abandoned.length = 1)) :
    Inv s' (⟨s, i, os⟩ :: log) := by
  have hcount : ∀ t, (sentIn os).countP (·.2 == .call t) = 0 :=
    countP_call_zero (fun x hx => (hos x hx).2.2)
  have hsends : ∀ t, sendsOf t (⟨s, i, os⟩ :: log) = sendsOf t log := by
    intro t; rw [sendsOf_cons, hcount, Nat.zero_add]
  exact {
  fresh := by
    intro x hx; simp only [allSent_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (hos x hx).2.1
    · exact Nat.lt_of_lt_of_le (h.fresh x hx) hnext
  ticketsFresh := by
    intro t ht; rw [hsends]; exact h.ticketsFresh t (Nat.le_trans htick ht)
  twice := by intro t; rw [hsends]; exact h.twice t
  inflight := by intro x hx; rw [hsends]; exact hinfl x hx
  held := by intro p hp; rw [hsends]; exact hheld p hp
  distinct := hdist
  openSent := by
    intro x hx; rw [mem_openIn_cons] at hx
    simp only [allSent_cons, List.mem_append]
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (h.openSent x hx.1)
  openNodup := by
    simp only [openIn_cons, List.map_append]
    refine List.nodup_append.2 ⟨hosNodup, (List.Sublist.map _ List.filter_sublist).nodup h.openNodup, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have h1 := (hos x hx).1
    have h2 := h.fresh y (h.openSent y ((List.mem_filter.1 hy).1))
    omega
  refreshes := by
    intro x hx hk; rw [mem_openIn_cons] at hx
    rcases hx with hx | hx
    · exact hnew x hx hk
    · exact hrefresh x hx.1 hk hx.2
  phaseOpen := by
    intro rid hr; rw [mem_openIn_cons]
    rcases hphase rid hr with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  abandoned := hab }


/-! ### Facts the invariant gives -/

theorem Inv.abandoned_nil {s : State} {log : List Entry} (h : Inv s log) (hp : s.phase ≠ .signedOut) :
    s.abandoned = [] := by
  rcases h.abandoned with h0 | ⟨h1, _⟩
  · exact h0
  · exact absurd h1 hp

theorem inj_of_nodup_map {α β : Type} {f : α → β} {l : List α} (hl : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, he.symm⟩ hl.1
    · exact absurd ⟨a, ha, he⟩ hl.1
    · exact ih hl.2 ha hb

/-- Moving call `p` (request `rid`) from in flight to held keeps tickets distinct. -/
theorem nodup_hold {infl : List (Nat × Pending)} {held : List Pending} {rid : Nat} {p : Pending}
    (hd : (infl.map (·.2.ticket) ++ held.map (·.ticket)).Nodup) (hm : (rid, p) ∈ infl) :
    ((infl.filter (·.1 ≠ rid)).map (·.2.ticket) ++ (held ++ [p]).map (·.ticket)).Nodup := by
  rw [List.nodup_append] at hd ⊢
  obtain ⟨h1, h2, h3⟩ := hd
  have hsub : ∀ a ∈ (infl.filter (·.1 ≠ rid)).map (·.2.ticket), a ∈ infl.map (·.2.ticket) :=
    fun a ha => (List.Sublist.map _ List.filter_sublist).subset ha
  refine ⟨(List.Sublist.map _ List.filter_sublist).nodup h1, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨h2, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb hab
    exact h3 _ (List.mem_map_of_mem hm) _ ha rfl
  · intro a ha b hb hab
    rw [List.map_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact h3 a (hsub a ha) b hb hab
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb hab
      obtain ⟨q, hq, hqt⟩ := List.mem_map.1 ha
      have hq' := List.mem_filter.1 hq
      have := inj_of_nodup_map h1 hq'.1 hm hqt
      subst this
      simp at hq'

/-! ### Each step keeps the invariant -/

/-- A step that leaves the state as it was and sends nothing, and doesn't answer the refresh in
flight. -/
theorem Inv.idle {s : State} {log : List Entry} {i : Input} {os : List Out} (h : Inv s log)
    (hos : sentIn os = []) (hr : ∀ rid, s.phase.refreshRid = some rid → i.replies rid = false) :
    Inv s (⟨s, i, os⟩ :: log) := by
  refine Inv.noCalls h (by simp [hos]) (by simp [hos]) (Nat.le_refl _) (Nat.le_refl _) h.inflight
    h.held h.distinct (by simp [hos]) ?_ ?_ h.abandoned
  · intro x hx hk _; exact h.refreshes x hx hk
  · intro rid h1; exact Or.inr ⟨h.phaseOpen rid h1, hr rid h1⟩

/-- A step that drops the calls of request `rid` from in flight and sends nothing. -/
theorem Inv.drop {s : State} {log : List Entry} {rid : Nat} {r : Cairn.Reply} {os : List Out}
    (h : Inv s log) (hos : sentIn os = [])
    (hr : ∀ rid', s.phase.refreshRid = some rid' → rid ≠ rid') :
    Inv { s with inflight := s.inflight.filter (fun x => decide (x.1 ≠ rid)) }
      (⟨s, .reply rid r, os⟩ :: log) := by
  refine Inv.noCalls h (by simp [hos]) (by simp [hos]) (Nat.le_refl _) (Nat.le_refl _) ?_
    h.held ?_ (by simp [hos]) ?_ ?_ h.abandoned
  · intro x hx; exact h.inflight x (List.mem_filter.1 hx).1
  · have := h.distinct
    rw [List.nodup_append] at this ⊢
    refine ⟨(List.Sublist.map _ List.filter_sublist).nodup this.1, this.2.1, ?_⟩
    intro a ha b hb
    exact this.2.2 a ((List.Sublist.map _ List.filter_sublist).subset ha) b hb
  · intro x hx hk _; exact h.refreshes x hx hk
  · intro rid1 h1
    exact Or.inr ⟨h.phaseOpen rid1 h1, by simpa [Input.replies] using hr rid1 h1⟩

theorem Inv.of_callReply {s : State} {log : List Entry} {rid : Nat} {r : Cairn.Reply}
    (h : Inv s log) (hr : ∀ rid', s.phase.refreshRid = some rid' → rid ≠ rid') :
    Inv (onCallReply s rid r).1 (⟨s, .reply rid r, (onCallReply s rid r).2⟩ :: log) := by
  unfold onCallReply
  split
  · rename_i hab
    refine Inv.noCalls h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [forgetBoth, Input.replies]
    · exact fun a b hm => h.inflight (a, b) hm
    · exact h.held
    · exact h.distinct
    · intro a b hm hb hrep
      rcases h.refreshes (a, b) hm hb with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun e => hrep e.symm⟩
    · intro rid1 h1; exact ⟨h.phaseOpen _ h1, hr _ h1⟩
    · rcases h.abandoned with h0 | ⟨hp, hl⟩
      · simp [h0] at hab
      · obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hl
        simp only [ha, List.mem_singleton] at hab ⊢
        exact Or.inl fun _ e => e.trans hab.symm
  · split
    · exact Inv.idle h rfl (fun rid' h1 => by simpa [Input.replies] using hr rid' h1)
    · rename_i fst p hf
      have hm := List.mem_of_find?_eq_some hf
      have hfst : fst = rid := by simpa using List.find?_some hf
      subst hfst
      simp only []
      split
      · rename_i hexp
        split
        · rename_i a hph
          have hab := h.abandoned_nil (by simp [hph])
          refine Inv.noCalls h ?_ (by simp [startRefresh]) (by simp [startRefresh])
            (by simp [startRefresh]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · simp [startRefresh]
          · intro x hx; exact h.inflight x (List.mem_filter.1 hx).1
          · intro q hq
            simp only [startRefresh, List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact h.held q hq
            · have := h.inflight _ hm
              simp only [Bool.and_eq_true, beq_iff_eq] at hexp
              exact ⟨this.1, by omega, this.2⟩
          · exact nodup_hold h.distinct hm
          · simp [startRefresh, Phase.refreshRid]
          · intro x hx hk _
            rcases h.refreshes x hx hk with h1 | h1
            · simp [hph, Phase.refreshRid] at h1
            · simp [hab] at h1
          · simp [startRefresh, Phase.refreshRid]
          · simp [startRefresh, hab]
        · rename_i rid' host a hph
          refine Inv.noCalls h (by simp) (by simp) (Nat.le_refl _) (Nat.le_refl _) ?_ ?_ ?_
            (by simp) ?_ ?_ h.abandoned
          · intro x hx; exact h.inflight x (List.mem_filter.1 hx).1
          · intro q hq
            simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact h.held q hq
            · have := h.inflight _ hm
              simp only [Bool.and_eq_true, beq_iff_eq] at hexp
              exact ⟨this.1, by omega, this.2⟩
          · exact nodup_hold h.distinct hm
          · intro x hx hk _; exact h.refreshes x hx hk
          · intro rid1 h1
            exact Or.inr ⟨h.phaseOpen rid1 h1, by simpa [Input.replies] using hr rid1 h1⟩
        · exact Inv.drop h rfl hr
      · exact Inv.drop h rfl hr

theorem Inv.signInStart {s : State} {log : List Entry} {host idn pw : String} (h : Inv s log)
    (hph : s.phase = .launched ∨ s.phase = .signedOut) (hab : s.abandoned = []) :
    Inv { s with phase := .signingIn s.next host, next := s.next + 1 }
      (⟨s, .signIn host idn pw, [.send s.next .signIn (createSession host idn pw)]⟩ :: log) := by
  refine Inv.noCalls h (by simp) (by simp) (by simp) (Nat.le_refl _) h.inflight h.held h.distinct
    (by simp) ?_ (by simp [Phase.refreshRid]) (Or.inl hab)
  intro x hx hk _
  rcases h.refreshes x hx hk with h1 | h1
  · rcases hph with hph | hph <;> simp [hph, Phase.refreshRid] at h1
  · simp [hab] at h1

theorem Inv.of_signIn {s : State} {log : List Entry} {rid : Nat} {host : String}
    {r : Cairn.Reply} (h : Inv s log) (hph : s.phase = .signingIn rid host) :
    Inv (onSignIn s host r).1 (⟨s, .reply rid r, (onSignIn s host r).2⟩ :: log) := by
  have hab := h.abandoned_nil (by simp [hph])
  have hno : ∀ x ∈ openIn log, x.2 = .refresh → False := by
    intro x hx hk
    rcases h.refreshes x hx hk with h1 | h1
    · simp [hph, Phase.refreshRid] at h1
    · simp [hab] at h1
  unfold onSignIn
  split
  · refine Inv.noCalls h (by simp) (by simp) (by simp) (Nat.le_refl _) h.inflight h.held
      h.distinct (by simp) (fun x hx hk _ => (hno x hx hk).elim) (by simp [Phase.refreshRid])
      (Or.inl hab)
  · refine Inv.noCalls h (by simp [forgetBoth]) (by simp [forgetBoth]) (by simp [forgetBoth])
      (Nat.le_refl _) h.inflight h.held h.distinct (by simp [forgetBoth])
      (fun x hx hk _ => (hno x hx hk).elim) (by simp [forgetBoth, Phase.refreshRid])
      (Or.inl hab)

theorem count_le_one_of_nodup {l : List Nat} (hl : l.Nodup) (a : Nat) : l.count a ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.nodup_cons] at hl
    rw [List.count_cons]
    by_cases hab : b = a
    · subst hab; simp [List.count_eq_zero_of_not_mem hl.1]
    · have := ih hl.2; simp [hab]; omega

theorem countP_numbered (n : Nat) (ps : List Pending) (t : Nat) :
    ((numbered n ps).map (fun x => (x.1, Kind.call x.2.ticket))).countP (·.2 == .call t) =
      (ps.map (·.ticket)).count t := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih => simp [numbered, List.count_cons, ih, List.countP_cons]

theorem Inv.of_refreshed {s : State} {log : List Entry} {rid : Nat} {host : String}
    {prev : Option Account} {r : Cairn.Reply} (h : Inv s log)
    (hph : s.phase = .refreshing rid host prev) (a : Account) (e : Event) :
    Inv (sendAll a.service { s with phase := .signedIn a, held := [] } s.held).1
      (⟨s, .reply rid r,
        .event e :: (sendAll a.service { s with phase := .signedIn a, held := [] } s.held).2⟩ ::
        log) := by
  have hab := h.abandoned_nil (by simp [hph])
  have hsent : sentIn (.event e :: (sendAll a.service { s with phase := .signedIn a, held := [] }
      s.held).2) = (numbered s.next s.held).map (fun x => (x.1, Kind.call x.2.ticket)) := by
    rw [sentIn_event, sentIn_sendAll]
  have hcount : ∀ t, sendsOf t (⟨s, .reply rid r, .event e :: (sendAll a.service
      { s with phase := .signedIn a, held := [] } s.held).2⟩ :: log) =
      (s.held.map (·.ticket)).count t + sendsOf t log := by
    intro t; rw [sendsOf_cons, hsent, countP_numbered]
  have hd := List.nodup_append.1 h.distinct
  have hheldNodup : (s.held.map (·.ticket)).Nodup := hd.2.1
  have hheldTick : ∀ t, s.nextTicket ≤ t → (s.held.map (·.ticket)).count t = 0 := by
    intro t ht
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    have := (h.held p hp).2.2; omega
  simp only [sendAll] at hsent hcount ⊢
  exact {
  fresh := by
    intro x hx
    simp only [allSent_cons, List.mem_append] at hx
    rw [hsent] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := mem_numbered hy; simp only; omega
    · have := h.fresh x hx; simp only; omega
  ticketsFresh := by
    intro t ht; rw [hcount, hheldTick t ht, h.ticketsFresh t ht]
  twice := by
    intro t; rw [hcount]
    by_cases hm : t ∈ s.held.map (·.ticket)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      have h1 := count_le_one_of_nodup hheldNodup p.ticket
      have h2 := h.held p hp
      omega
    · rw [List.count_eq_zero_of_not_mem hm]; have := h.twice t; omega
  inflight := by
    intro x hx
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩ | hx
    · have hp := (mem_numbered hy).2.2
      have h1 := count_le_one_of_nodup hheldNodup y.2.ticket
      have h2 : 0 < (s.held.map (·.ticket)).count y.2.ticket :=
        List.count_pos_iff.2 (List.mem_map_of_mem hp)
      have h3 := h.held y.2 hp
      simp only [hcount]; exact ⟨by omega, h3.2.2⟩
    · rw [hcount, List.count_eq_zero_of_not_mem]
      · simpa using h.inflight x hx
      · intro hm; exact hd.2.2 _ (List.mem_map_of_mem hx) _ hm rfl
  held := by simp
  distinct := by
    have hmap : ((numbered s.next s.held).map
        (fun x => (x.1, { x.2 with tries := x.2.tries + 1 }))).map (·.2.ticket) =
        s.held.map (·.ticket) := by
      rw [List.map_map, ← numbered_snd s.next s.held, List.map_map]
      simp only [numbered_snd]; rfl
    simp only [List.map_append, hmap, List.map_nil, List.append_nil]
    exact List.perm_append_comm.nodup_iff.1 h.distinct
  openSent := by
    intro x hx
    simp only [openIn_cons, allSent_cons, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (h.openSent x (List.mem_filter.1 hx).1)
  openNodup := by
    simp only [openIn_cons, List.map_append]
    rw [hsent, List.map_map]
    have hr : (numbered s.next s.held).map ((·.1) ∘ fun x => (x.1, Kind.call x.2.ticket)) =
        List.range' s.next s.held.length := by
      rw [← numbered_fst]; rfl
    rw [hr]
    refine List.nodup_append.2 ⟨List.nodup_range' _, (List.Sublist.map _ List.filter_sublist).nodup
      h.openNodup, ?_⟩
    intro u hu v hv huv
    rw [List.mem_range'] at hu
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
    have := h.fresh y (h.openSent y (List.mem_filter.1 hy).1)
    omega
  refreshes := by
    intro x hx hk
    rw [mem_openIn_cons, hsent] at hx
    rcases hx with hx | ⟨hx, hrep⟩
    · obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; simp at hk
    · rcases h.refreshes x hx hk with h1 | h1
      · simp only [hph, Phase.refreshRid, Option.some.injEq] at h1
        subst h1; simp [Input.replies] at hrep
      · simp [hab] at h1
  phaseOpen := by simp [Phase.refreshRid]
  abandoned := Or.inl hab }

theorem Inv.of_refresh {s : State} {log : List Entry} {rid : Nat} {host : String}
    {prev : Option Account} {r : Cairn.Reply} (h : Inv s log)
    (hph : s.phase = .refreshing rid host prev) :
    Inv (onRefresh s host prev r).1 (⟨s, .reply rid r, (onRefresh s host prev r).2⟩ :: log) := by
  have hab := h.abandoned_nil (by simp [hph])
  have hno : ∀ x ∈ openIn log, x.2 = .refresh → (Input.reply rid r).replies x.1 = false →
      False := by
    intro x hx hk hrep
    rcases h.refreshes x hx hk with h1 | h1
    · simp only [hph, Phase.refreshRid, Option.some.injEq] at h1
      subst h1; simp [Input.replies] at hrep
    · simp [hab] at h1
  unfold onRefresh
  split
  · exact Inv.of_refreshed h hph _ _
  · split
    · refine Inv.noCalls h (by simp) (by simp) (by simp) (Nat.le_refl _) h.inflight (by simp)
        (by simpa using (List.nodup_append.1 h.distinct).1) (by simp)
        (fun x hx hk hr => (hno x hx hk hr).elim) ?_ (Or.inl hab)
      cases prev <;> simp [Phase.refreshRid]
    · refine Inv.noCalls h (by simp [forgetBoth]) (by simp [forgetBoth]) (by simp [forgetBoth])
        (Nat.le_refl _) h.inflight (by simp [forgetBoth])
        (by simpa [forgetBoth] using (List.nodup_append.1 h.distinct).1) (by simp [forgetBoth])
        (fun x hx hk hr => (hno x hx hk hr).elim) (by simp [forgetBoth, Phase.refreshRid])
        (Or.inl hab)

theorem Inv.of_sendCall {s : State} {log : List Entry} {id : Nat} {c : Call} {a : Account}
    (h : Inv s log) :
    Inv (sendCall a.service { s with nextTicket := s.nextTicket + 1 }
        { id, ticket := s.nextTicket, call := c, tries := 0 }).1
      (⟨s, .call id c, (sendCall a.service { s with nextTicket := s.nextTicket + 1 }
        { id, ticket := s.nextTicket, call := c, tries := 0 }).2⟩ :: log) := by
  have hcount : ∀ t, sendsOf t (⟨s, .call id c, (sendCall a.service
      { s with nextTicket := s.nextTicket + 1 }
      { id, ticket := s.nextTicket, call := c, tries := 0 }).2⟩ :: log) =
      (if t = s.nextTicket then 1 else 0) + sendsOf t log := by
    intro t; rw [sendsOf_cons]
    by_cases ht : t = s.nextTicket
    · subst ht; simp [sendCall]
    · simp [sendCall, ht, Ne.symm ht]
  have hold : ∀ t, t < s.nextTicket → sendsOf t (⟨s, .call id c, (sendCall a.service
      { s with nextTicket := s.nextTicket + 1 }
      { id, ticket := s.nextTicket, call := c, tries := 0 }).2⟩ :: log) = sendsOf t log := by
    intro t ht; rw [hcount]; simp [show t ≠ s.nextTicket by omega]
  have hd := List.nodup_append.1 h.distinct
  exact {
  fresh := by
    intro x hx
    simp only [allSent_cons, List.mem_append, sendCall, sentIn_send, sentIn_nil,
      List.mem_singleton] at hx ⊢
    rcases hx with rfl | hx
    · simp
    · have := h.fresh x hx; omega
  ticketsFresh := by
    intro t ht; simp only [sendCall] at ht
    rw [hcount, h.ticketsFresh t (by omega)]; simp [show t ≠ s.nextTicket by omega]
  twice := by
    intro t; rw [hcount]
    by_cases ht : t = s.nextTicket
    · subst ht; rw [h.ticketsFresh _ (Nat.le_refl _)]; simp
    · simp only [ht, ite_false, Nat.zero_add]; exact h.twice t
  inflight := by
    intro x hx
    simp only [sendCall, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [hcount, h.ticketsFresh _ (Nat.le_refl _)]; simp [sendCall]
    · have := h.inflight x hx
      rw [hold _ this.2]; exact ⟨this.1, by simp only [sendCall]; omega⟩
  held := by
    intro p hp
    have := h.held p hp
    rw [hold _ this.2.2]; exact ⟨this.1, this.2.1, by simp only [sendCall]; omega⟩
  distinct := by
    simp only [sendCall, List.map_cons, List.cons_append, List.nodup_cons, List.mem_append,
      List.mem_map]
    refine ⟨?_, h.distinct⟩
    rintro (⟨x, hx, he⟩ | ⟨p, hp, he⟩)
    · have := (h.inflight x hx).2; omega
    · have := (h.held p hp).2.2; omega
  openSent := by
    intro x hx
    simp only [openIn_cons, allSent_cons, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (h.openSent x (List.mem_filter.1 hx).1)
  openNodup := by
    simp only [openIn_cons, sendCall, sentIn_send, sentIn_nil, List.singleton_append,
      List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup h.openNodup⟩
    rintro ⟨y, hy, he⟩
    have := h.fresh y (h.openSent y (List.mem_filter.1 hy).1)
    omega
  refreshes := by
    intro x hx hk
    simp only [openIn_cons, sendCall, sentIn_send, sentIn_nil, List.singleton_append,
      List.mem_cons, List.mem_filter, Input.replies] at hx ⊢
    rcases hx with rfl | ⟨hx, _⟩
    · simp at hk
    · exact h.refreshes x hx hk
  phaseOpen := by
    intro rid h1
    simp only [sendCall] at h1
    simp only [openIn_cons, List.mem_append, List.mem_filter, Input.replies]
    exact Or.inr ⟨h.phaseOpen rid h1, rfl⟩
  abandoned := h.abandoned }

theorem Inv.of_hold {s : State} {log : List Entry} {id : Nat} {c : Call}
    (h : Inv s log) :
    Inv { s with nextTicket := s.nextTicket + 1,
                 held := s.held ++ [{ id, ticket := s.nextTicket, call := c, tries := 0 }] }
      (⟨s, .call id c, []⟩ :: log) := by
  refine Inv.noCalls h (by simp) (by simp) (Nat.le_refl _) (Nat.le_succ _) ?_ ?_ ?_
    (by simp) (fun x hx hk _ => h.refreshes x hx hk)
    (fun rid h1 => Or.inr ⟨h.phaseOpen rid h1, rfl⟩) h.abandoned
  · intro x hx; have := h.inflight x hx; exact ⟨this.1, by simp only; omega⟩
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · have := h.held q hq; exact ⟨this.1, this.2.1, by simp only; omega⟩
    · exact ⟨h.ticketsFresh _ (Nat.le_refl _), by simp, by simp⟩
  · have hd := List.nodup_append.1 h.distinct
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← List.append_assoc]
    refine List.nodup_append.2 ⟨h.distinct, by simp, ?_⟩
    intro u hu v hv huv
    simp only [List.mem_singleton] at hv
    subst hv huv
    simp only [List.mem_append, List.mem_map] at hu
    rcases hu with ⟨x, hx, he⟩ | ⟨p, hp, he⟩
    · have := (h.inflight x hx).2; omega
    · have := (h.held p hp).2.2; omega

theorem Inv.of_step {s : State} {log : List Entry} (h : Inv s log) (i : Input) :
    Inv (step s i).1 (⟨s, i, (step s i).2⟩ :: log) := by
  cases i with
  | signIn host idn pw =>
    simp only [step]
    split
    · split
      · rename_i _ hph hab
        exact Inv.signInStart h (Or.inl hph) (by simpa using hab)
      · exact Inv.idle h rfl (by simp [Input.replies])
    · split
      · rename_i _ hph hab
        exact Inv.signInStart h (Or.inr hph) (by simpa using hab)
      · exact Inv.idle h rfl (by simp [Input.replies])
    · exact Inv.idle h rfl (by simp [Input.replies])
  | resume host =>
    simp only [step]
    split
    · rename_i _ hph
      have hab := h.abandoned_nil (by simp [hph])
      refine Inv.noCalls h (by simp) (by simp) (by simp) (Nat.le_refl _) h.inflight h.held
        h.distinct (by simp [Phase.refreshRid]) ?_ (by simp [Phase.refreshRid]) (Or.inl hab)
      intro x hx hk _
      rcases h.refreshes x hx hk with h1 | h1
      · simp [hph, Phase.refreshRid] at h1
      · simp [hab] at h1
    · exact Inv.idle h rfl (by simp [Input.replies])
  | call id c =>
    simp only [step]
    split
    · exact Inv.of_sendCall h
    · exact Inv.of_hold h
    · refine Inv.noCalls h (by simp) (by simp) (Nat.le_refl _) (Nat.le_succ _) ?_ ?_ h.distinct
        (by simp) (fun x hx hk _ => h.refreshes x hx hk)
        (fun rid h1 => Or.inr ⟨h.phaseOpen rid h1, rfl⟩) h.abandoned
      · intro x hx; have := h.inflight x hx; exact ⟨this.1, by simp only; omega⟩
      · intro q hq; have := h.held q hq; exact ⟨this.1, this.2.1, by simp only; omega⟩
  | signOut =>
    simp only [step]
    refine Inv.noCalls h (by simp [forgetBoth]) (by simp [forgetBoth]) (by simp [forgetBoth])
      (Nat.le_refl _) h.inflight (by simp [forgetBoth])
      (by simpa [forgetBoth] using (List.nodup_append.1 h.distinct).1) (by simp [forgetBoth]) ?_
      (by simp [forgetBoth, Phase.refreshRid]) ?_
    · intro x hx hk _
      rcases h.refreshes x hx hk with h1 | h1
      · cases hph : s.phase <;> simp_all [Phase.refreshRid, forgetBoth]
      · simp [forgetBoth, h1]
    · rcases h.abandoned with h0 | ⟨hp0, hl⟩
      · cases hph : s.phase <;> simp [forgetBoth, h0]
      · simp [forgetBoth, hp0, hl]
  | reply rid r =>
    simp only [step]
    split
    · split
      · rename_i _ rid' host hph heq
        subst heq
        exact Inv.of_signIn h hph
      · rename_i _ rid' host hph hne
        exact Inv.of_callReply h (by
          intro x hx; simp [hph, Phase.refreshRid] at hx)
    · split
      · rename_i _ rid' host a hph heq
        subst heq
        exact Inv.of_refresh h hph
      · rename_i _ rid' host a hph hne
        exact Inv.of_callReply h (by
          intro x hx; simp [hph, Phase.refreshRid] at hx; omega)
    · rename_i hph1 hph2
      exact Inv.of_callReply h (by
        intro rid' h1; cases hph : s.phase <;> simp_all [Phase.refreshRid])

theorem Inv.feed {m : Model} (h : Inv m.s m.log) (i : Input) : Inv (m.feed i).s (m.feed i).log :=
  h.of_step i

/-! ### What the invariant gives -/

theorem length_le_one_of_const {α : Type} {l : List α} (f : α → Nat) (hl : (l.map f).Nodup)
    (r : Nat) (hc : ∀ x ∈ l, f x = r) : l.length ≤ 1 := by
  match l, hl, hc with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: _, hl, hc =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hl
    exact absurd ((hc x (by simp)).trans (hc y (by simp)).symm) hl.1.1

/-- At most one refresh in flight. -/
theorem Inv.oneRefresh {s : State} {log : List Entry} (h : Inv s log) : OneRefresh log := by
  unfold OneRefresh
  let r0 : Nat := match s.phase.refreshRid with
    | some r => r
    | none => s.abandoned.headD 0
  apply length_le_one_of_const (·.1)
    ((List.Sublist.map _ List.filter_sublist).nodup h.openNodup) r0
  intro x hx
  have ⟨hx, hk⟩ := List.mem_filter.1 hx
  have hk : x.2 = .refresh := by simpa using hk
  rcases h.refreshes x hx hk with h1 | h1
  · simp only [r0, h1]
  · cases hr : s.phase.refreshRid with
    | some r =>
      have : s.phase ≠ .signedOut := by intro e; simp [e, Phase.refreshRid] at hr
      simp [h.abandoned_nil this] at h1
    | none =>
      simp only [r0, hr]
      rcases h.abandoned with h0 | ⟨_, hl⟩
      · simp [h0] at h1
      · obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hl
        simp only [hb, List.mem_singleton] at h1
        simp [hb, h1]

theorem Inv.atMostTwice {s : State} {log : List Entry} (h : Inv s log) : AtMostTwice log := h.twice

theorem onCallReply_noCall (s : State) (rid : Nat) (r : Cairn.Reply) :
    ∀ x ∈ sentIn (onCallReply s rid r).2, ∀ t, x.2 ≠ .call t := by
  unfold onCallReply
  split
  · simp [forgetBoth]
  · split
    · simp
    · simp only []
      split
      · split <;> simp [startRefresh]
      · simp

theorem sessionOf_some {r : Cairn.Reply} {info : SessionInfo} (h : sessionOf r = some info) :
    ∃ st hs b, r = .http st hs b ∧ isSuccess st = true := by
  unfold sessionOf at h
  split at h
  · rename_i st hs b
    split at h
    · exact ⟨st, hs, b, rfl, by assumption⟩
    · simp at h
  · simp at h

/-- The only steps that send calls: a new call (its first send), and a refresh that succeeded. -/
theorem step_sendsCall (s : State) (i : Input) {x : Nat × Kind} (hx : x ∈ sentIn (step s i).2)
    {t : Nat} (hk : x.2 = .call t) :
    (∃ id c, i = .call id c ∧ t = s.nextTicket) ∨
      (∃ rid host prev r info, s.phase = .refreshing rid host prev ∧ i = .reply rid r ∧
        sessionOf r = some info) := by
  cases i with
  | signIn host idn pw =>
    simp only [step] at hx
    split at hx
    all_goals (try split at hx) <;> simp at hx <;> (obtain rfl := hx; simp at hk)
  | resume host =>
    simp only [step] at hx
    split at hx <;> simp at hx
    subst hx; simp at hk
  | call id c =>
    simp only [step] at hx
    split at hx <;> simp [sendCall] at hx
    subst hx; simp at hk; exact Or.inl ⟨id, c, rfl, hk.symm⟩
  | signOut => simp [step, forgetBoth] at hx
  | reply rid r =>
    simp only [step] at hx
    split at hx
    · split at hx
      · unfold onSignIn at hx; split at hx <;> simp [forgetBoth] at hx
      · exact absurd hk (onCallReply_noCall s rid r x hx t)
    · split at hx
      · rename_i _ rid' host prev hph heq
        subst heq
        unfold onRefresh at hx
        split at hx
        · rename_i info _
          exact Or.inr ⟨rid, host, prev, r, info, hph, rfl, by assumption⟩
        · split at hx <;> simp [forgetBoth] at hx
      · exact absurd hk (onCallReply_noCall s rid r x hx t)
    · exact absurd hk (onCallReply_noCall s rid r x hx t)

/-- A step sends a call that was sent before only when a refresh in flight succeeds. -/
theorem Inv.retryStep {s : State} {log : List Entry} (h : Inv s log) (i : Input) :
    ∀ t, 0 < (sentIn (step s i).2).countP (·.2 == .call t) → 0 < sendsOf t log →
      RefreshSucceeded ⟨s, i, (step s i).2⟩ log := by
  intro t hc hs
  obtain ⟨x, hx, hk⟩ := List.countP_pos_iff.1 hc
  have hk : x.2 = .call t := by simpa using hk
  rcases step_sendsCall s i hx hk with ⟨id, c, _, rfl⟩ | ⟨rid, host, prev, r, info, hph, rfl, hr⟩
  · rw [h.ticketsFresh _ (Nat.le_refl _)] at hs; exact absurd hs (Nat.lt_irrefl 0)
  · obtain ⟨st, hs', b, rfl, hok⟩ := sessionOf_some hr
    exact ⟨rid, st, hs', b, rfl, hok, h.phaseOpen rid (by simp [hph, Phase.refreshRid])⟩

/-- Everything the claims say, together: kept by every step. -/
structure Ok (m : Model) : Prop where
  inv : Inv m.s m.log
  noSecret : NoSecretSignedOut m.log
  refusal : RefusalEndsAll m
  retry : RetryAfterRefresh m.log

theorem Ok.init : Ok {} :=
  ⟨Inv.init, trivial, ⟨trivial, fun _ => rfl⟩, trivial⟩

theorem Ok.feed {m : Model} (h : Ok m) (i : Input) : Ok (m.feed i) :=
  ⟨h.inv.feed i, noSecretSignedOut_feed m i h.noSecret, refusalEndsAll_feed m i h.refusal,
    ⟨h.inv.retryStep i, h.retry⟩⟩

end CairnAtproto.Session
