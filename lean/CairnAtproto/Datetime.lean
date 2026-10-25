module

/-! # Datetimes

`parseDatetime` reads an RFC 3339 timestamp, as the AT Protocol's `datetime` format writes
them (`createdAt`, `indexedAt`), into milliseconds since the Unix epoch, UTC. It lives here until a
`cairn_date` exists.

Accepted: `YYYY-MM-DDTHH:MM:SS`, an optional fraction of any length (milliseconds are its first
three digits; the rest is dropped, so it rounds toward the past), then `Z` or `±HH:MM`. `T`
and `Z` may be lower case, as RFC 3339 allows. The date must exist (leap years counted) and
the time be within `00:00:00` and `23:59:60`. A leap second (`:60`) reads as one second past
`:59`, the next minute's start, as POSIX time has no leap seconds. -/

@[expose] public section

namespace CairnAtproto

def isLeap (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y : Int) (m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeap y then 29 else 28
  | _ => 0

/-- Days from 1970-01-01 to the given civil date (Howard Hinnant's `days_from_civil`). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if 0 ≤ y then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy := (153 * mp + 2) / 5 + (d : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def digitOf (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- Exactly `n` digits as a number, and the rest. -/
def digitsN : Nat → List Char → Option (Nat × List Char)
  | 0, cs => some (0, cs)
  | n + 1, cs =>
    match digitsN n cs with
    | some (v, c :: rest) =>
      match digitOf c with
      | some d => some (v * 10 + d, rest)
      | none => none
    | _ => none

/-- The milliseconds of a fraction's digits (its first three, padded), and what follows it. -/
def fractionMs : List Char → Nat × List Char
  | cs =>
    let ds := cs.takeWhile (fun c => (digitOf c).isSome)
    let rest := cs.drop ds.length
    let three := (ds ++ ['0', '0', '0']).take 3
    (three.foldl (fun n c => n * 10 + (digitOf c).getD 0) 0, rest)

/-- The offset from UTC in minutes. -/
def offsetMinutes : List Char → Option Int
  | ['Z'] | ['z'] => some 0
  | [s, h1, h2, ':', m1, m2] => do
    let sign : Int ← if s = '+' then some 1 else if s = '-' then some (-1) else none
    let (h, _) ← digitsN 2 [h1, h2]
    let (m, _) ← digitsN 2 [m1, m2]
    if h ≤ 23 ∧ m ≤ 59 then some (sign * ((h : Int) * 60 + m)) else none
  | _ => none

/-- An RFC 3339 timestamp as milliseconds since the epoch, UTC. -/
def parseDatetime (s : String) : Option Int := do
  let cs := s.toList
  let (y, cs) ← digitsN 4 cs
  let cs ← match cs with | '-' :: r => some r | _ => none
  let (mo, cs) ← digitsN 2 cs
  let cs ← match cs with | '-' :: r => some r | _ => none
  let (d, cs) ← digitsN 2 cs
  let cs ← match cs with | 'T' :: r | 't' :: r => some r | _ => none
  let (h, cs) ← digitsN 2 cs
  let cs ← match cs with | ':' :: r => some r | _ => none
  let (mi, cs) ← digitsN 2 cs
  let cs ← match cs with | ':' :: r => some r | _ => none
  let (sec, cs) ← digitsN 2 cs
  let (ms, cs) ← match cs with
    | '.' :: r =>
      if (r.takeWhile (fun c => (digitOf c).isSome)).isEmpty then none else some (fractionMs r)
    | r => some (0, r)
  let off ← offsetMinutes cs
  if 1 ≤ mo ∧ mo ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y mo ∧ h ≤ 23 ∧ mi ≤ 59 ∧ sec ≤ 60 then
    let days := daysFromCivil y mo d
    let secs : Int := days * 86400 + (h : Int) * 3600 + (mi : Int) * 60 + sec - off * 60
    some (secs * 1000 + ms)
  else none

end CairnAtproto
