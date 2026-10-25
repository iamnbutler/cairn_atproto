module

public import CairnAtproto.Fake

/-! # The fake PDS's timeline only grows at its head

Post `k` is `postAt cfg k`, a function of the configuration and `k` alone, so the timeline of
`length` posts is `timeline cfg length`, and a longer one extends it at the head
(`timeline_extends`). Every request keeps the configuration and never shortens the timeline
(`Server.handle_cfg`, `Server.handle_length`, `Server.handle_timeline`); every control keeps
them too. A page is a contiguous run of it (`page_feed`, `page_head`). So whatever
requests come, each post the server has shown stays as it was, at the same place counted from
the oldest, and new posts appear only above it. -/

@[expose] public section

namespace CairnAtproto.Fake

theorem timeline_extends (c : Config) (n m : Nat) :
    timeline c (n + m) = (List.range' n m).reverse.map (postAt c) ++ timeline c n := by
  simp only [timeline, List.range_eq_range']
  rw [show n + m = n + m from rfl, ← List.range'_append_1, List.reverse_append, List.map_append]
  simp

/-- A page is a contiguous run of the timeline: the `n` posts after the newest `L - k`. -/
theorem page_feed (c : Config) (L n k : Nat) (hk : k ≤ L) :
    (page c L n (some k)).feed = ((timeline c L).drop (L - k)).take n := by
  apply List.ext_getElem
  · simp [page, timeline]; omega
  · intro i h1 h2
    simp [page, timeline] at *
    simp [timeline] at h2; congr 1; omega

/-- The head page is the newest `n` posts. -/
theorem page_head (c : Config) (L n : Nat) : (page c L n none).feed = (timeline c L).take n := by
  have := page_feed c L n L (Nat.le_refl L)
  simp only [Nat.sub_self, List.drop_zero] at this
  rw [← this]; rfl

theorem Server.check_ok {s s' : Server} {kind : String} {auth : Option String}
    (h : s.check kind auth = .ok s') : s'.cfg = s.cfg ∧ s'.length = s.length := by
  unfold Server.check at h
  repeat (first | split at h | simp_all)
  all_goals (cases h; simp)

theorem Server.issue_keeps (s : Server) : s.issue.1.cfg = s.cfg ∧ s.issue.1.length = s.length := by
  simp [Server.issue]

theorem Server.createSession_keeps (s : Server) (b : String) :
    (s.createSession b).1.cfg = s.cfg ∧ (s.createSession b).1.length = s.length := by
  unfold Server.createSession
  repeat' split
  all_goals simp [Server.issue]

theorem Server.xrpc_keeps (s : Server) (r : Req) (n : String) (ps : List (String × String)) :
    (s.xrpc r n ps).1.cfg = s.cfg ∧ (s.xrpc r n ps).1.length = s.length := by
  dsimp only [Server.xrpc]
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact Server.createSession_keeps s r.body
    | (rename_i h; obtain ⟨h1, h2⟩ := Server.check_ok h
       first
         | simp [Server.issue, h1, h2]
         | exact ⟨h1, h2⟩)

theorem Server.control_keeps (s : Server) (c : Control) :
    (s.control c).cfg = s.cfg ∧ s.length ≤ (s.control c).length := by
  cases c <;> simp [Server.control]

/-- A request keeps the configuration. -/
theorem Server.handle_cfg (s : Server) (r : Req) : (s.handle r).1.cfg = s.cfg := by
  dsimp only [Server.handle]
  repeat' split
  all_goals first
    | rfl
    | exact (Server.xrpc_keeps _ _ _ _).1
    | exact (Server.control_keeps _ _).1

/-- A request never shortens the timeline. -/
theorem Server.handle_length (s : Server) (r : Req) : s.length ≤ (s.handle r).1.length := by
  dsimp only [Server.handle]
  repeat' split
  all_goals first
    | exact Nat.le_refl _
    | exact (Server.control_keeps _ _).2
    | (rw [(Server.xrpc_keeps _ _ _ _).2]; simp)
    | (simp; done)

/-- So the timeline after any run of requests extends the one before at its head. -/
theorem Server.handle_timeline (s : Server) (r : Req) :
    ∃ m, timeline (s.handle r).1.cfg (s.handle r).1.length =
      (List.range' s.length m).reverse.map (postAt s.cfg) ++ timeline s.cfg s.length := by
  refine ⟨(s.handle r).1.length - s.length, ?_⟩
  rw [Server.handle_cfg, ← timeline_extends, Nat.add_sub_cancel' (Server.handle_length s r)]

end CairnAtproto.Fake
