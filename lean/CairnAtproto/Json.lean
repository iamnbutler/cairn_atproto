module

public import CairnJson

/-! # Reading and writing lexicon objects

Small readers over `CairnJson.Json` that every decoder in this package uses, so the round-trip
proofs (`CairnAtproto.Proofs.RoundTrip`) reason about one set of definitions:

* `Json.str? k`, `Json.nat? k`, `Json.bool? k`, `Json.obj? k`, `Json.arr? k` read member `k`
  of an object (the first one, as `Json.field` does), or give `none`. `null` reads as absent.
* `optMap` decodes every element of a list or nothing, by plain structural recursion.
* `opt k v` writes an optional member: `[(k, v)]` or nothing.

The readers extend `CairnJson.Json`'s namespace so they read as `j.str? "did"`. Counts are `Nat`s written as plain integers (`⟨n, 0⟩`), as the AppView writes them. -/

@[expose] public section

namespace CairnJson

/-- A non-negative integer written without a fraction or exponent. -/
def Json.asNat : Json → Option Nat
  | .num ⟨m, 0⟩ => if 0 ≤ m then some m.toNat else none
  | _ => none

/-- A natural number as JSON. -/
def Json.ofNat (n : Nat) : Json := .num ⟨(n : Int), 0⟩

def Json.str? (j : Json) (k : String) : Option String := (j.field k).bind Json.getStr
def Json.nat? (j : Json) (k : String) : Option Nat := (j.field k).bind Json.asNat
def Json.bool? (j : Json) (k : String) : Option Bool := (j.field k).bind Json.getBool
def Json.arr? (j : Json) (k : String) : Option (List Json) := (j.field k).bind Json.getArr

/-- An object, as it is. -/
def Json.asObj : Json → Option Json
  | .obj kvs => some (.obj kvs)
  | _ => none

/-- Member `k` when it is an object (as a `Json`, for further reading). -/
def Json.obj? (j : Json) (k : String) : Option Json := (j.field k).bind Json.asObj

/-- The `$type` of a lexicon object, `""` when it has none. -/
def Json.type (j : Json) : String := (j.str? "$type").getD ""

end CairnJson

namespace CairnAtproto
open CairnJson

/-- Every element decoded, or `none`. -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x with
    | none => none
    | some y =>
      match optMap f xs with
      | none => none
      | some ys => some (y :: ys)

/-- An optional member. -/
def opt {α : Type} (k : String) (f : α → Json) : Option α → List (String × Json)
  | none => []
  | some v => [(k, f v)]

end CairnAtproto
