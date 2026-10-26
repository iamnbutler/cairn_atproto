module

/-! # AT URIs

`at://<repo>/<collection>/<rkey>` names a record: the repo (an account's DID, or a handle), the
collection (an NSID such as `app.bsky.feed.like`) and the record key (a TID for likes, reposts,
follows and posts). A post's `uri`, a like's `viewer.like` and a follow's `viewer.following` are
all AT URIs; `AtUri.parse` reads one, and `toString` writes it back
(`AtUri.parse_toString`, for parts without `/`). Only record URIs are read: `at://did` alone, a
query or a fragment is `none`. -/

@[expose] public section

namespace CairnAtproto

/-- A record's address. -/
structure AtUri where
  /-- The account: a DID (or a handle). -/
  repo : String
  /-- The record type's NSID. -/
  collection : String
  /-- The record key. -/
  rkey : String
deriving Repr, DecidableEq, Inhabited

def AtUri.toString (u : AtUri) : String := "at://" ++ u.repo ++ "/" ++ u.collection ++ "/" ++ u.rkey

instance : ToString AtUri := ⟨AtUri.toString⟩

/-- Characters split at every `/`. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: splitSlash cs
    else match splitSlash cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- Read `at://repo/collection/rkey`, each part non-empty. -/
def AtUri.parse (s : String) : Option AtUri :=
  match s.toList with
  | 'a' :: 't' :: ':' :: '/' :: '/' :: rest =>
    match splitSlash rest with
    | [r, c, k] =>
      if r.isEmpty || c.isEmpty || k.isEmpty then none
      else some { repo := String.ofList r, collection := String.ofList c, rkey := String.ofList k }
    | _ => none
  | _ => none

/-- The parts are non-empty and hold no `/`, as every real DID, NSID and record key. -/
def AtUri.Valid (u : AtUri) : Prop :=
  u.repo ≠ "" ∧ u.collection ≠ "" ∧ u.rkey ≠ "" ∧
    '/' ∉ u.repo.toList ∧ '/' ∉ u.collection.toList ∧ '/' ∉ u.rkey.toList

theorem splitSlash_noSlash : ∀ (a : List Char), '/' ∉ a → splitSlash a = [a]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := splitSlash_noSlash cs (fun m => h (List.mem_cons_of_mem _ m))
    simp [splitSlash, hc, ih]

theorem splitSlash_append : ∀ (a b : List Char), '/' ∉ a →
    splitSlash (a ++ '/' :: b) = a :: splitSlash b
  | [], b, _ => by simp [splitSlash]
  | c :: cs, b, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := splitSlash_append cs b (fun m => h (List.mem_cons_of_mem _ m))
    simp [splitSlash, hc, ih]

/-- **An AT URI reads back as itself.** -/
theorem AtUri.parse_toString (u : AtUri) (h : u.Valid) : AtUri.parse u.toString = some u := by
  obtain ⟨r, c, k⟩ := u
  obtain ⟨hr, hc, hk, sr, sc, sk⟩ := h
  have e : (AtUri.toString ⟨r, c, k⟩).toList =
      'a' :: 't' :: ':' :: '/' :: '/' :: (r.toList ++ '/' :: (c.toList ++ '/' :: k.toList)) := by
    simp [AtUri.toString, String.toList_append]
  have hr' : r.toList ≠ [] := by simpa using hr
  have hc' : c.toList ≠ [] := by simpa using hc
  have hk' : k.toList ≠ [] := by simpa using hk
  simp [AtUri.parse, e, splitSlash_append _ _ sr, splitSlash_append _ _ sc,
    splitSlash_noSlash _ sk, List.isEmpty_iff, hr', hc', hk']

end CairnAtproto
