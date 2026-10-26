module

public import CairnAtproto.Json

/-! # Record keys: TIDs

A TID (timestamp identifier, the AT Protocol's record-key format for likes, reposts, follows and
posts) is a 64-bit number with its top bit zero: 53 bits of microseconds since the Unix epoch,
then 10 bits of *clock id*, written as 13 characters of the base-32 "sortable" alphabet
`234567abcdefghijklmnopqrstuvwxyz`, most significant first. Because the alphabet is in ASCII
order, TIDs sort as text the way they sort as numbers.

A client that chooses its own record keys can send a write twice and have it written once: a
`putRecord` with a key it already wrote replaces the record with itself (`cairn_atproto^22`).
So Sky mints a key per act from its clock (`TidClock.mint`) and keeps it with the write.

* `Tid`: microseconds (`< 2^53`) and clock id (`< 1024`); `Tid.toNat` is the 63-bit number.
* `Tid.encode` writes the 13 characters; `Tid.decode` reads them back, or `none` for anything
  that isn't a TID (`Tid.decode_encode`, `Tid.encode_length`, `Tid.encode_chars`).
* `TidClock`: a session's minter. `TidClock.new clockId` (the clock id taken mod 1024: pick one
  at random per launch, so two launches in the same microsecond differ), then
  `mint clock nowMicros`, which uses `nowMicros` unless it isn't past the last one minted, and
  then the last one plus one. So the keys a session mints strictly increase, even when the
  clock stands still or steps back (`TidClock.mint_increasing`, `cairn_atproto^18`). `mint` is
  `none` only once the microseconds would pass `2^53` (in the year 2255).

The proofs are in `CairnAtproto.Proofs.Tid`. -/

@[expose] public section

namespace CairnAtproto

/-- `2^53`: TID microseconds are below it. -/
def tidMicrosBound : Nat := 9007199254740992

/-- `2^10`: TID clock ids are below it. -/
def tidClockBound : Nat := 1024

/-- A record key in TID form. -/
structure Tid where
  /-- Microseconds since the Unix epoch. -/
  micros : Nat
  /-- The clock id, which tells apart clients minting in the same microsecond. -/
  clock : Nat
  micros_lt : micros < tidMicrosBound
  clock_lt : clock < tidClockBound
deriving DecidableEq

instance : Repr Tid where
  reprPrec t _ := s!"Tid({t.micros}, {t.clock})"

/-- The 63-bit number: microseconds, then the clock id in the low 10 bits. -/
def Tid.toNat (t : Tid) : Nat := t.micros * tidClockBound + t.clock

/-- The sortable base-32 alphabet, in ASCII order. -/
def tidAlphabet : List Char :=
  ['2', '3', '4', '5', '6', '7', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
   'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']

/-- Digit `d` (below 32) as its character. -/
def tidChar (d : Nat) : Char := tidAlphabet.getD d '2'

/-- The digit a character stands for, if it is one of the alphabet's. -/
def tidDigit (c : Char) : Option Nat := go tidAlphabet 0
where
  go : List Char → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x = c then some i else go xs (i + 1)

/-- `n`'s last `w` base-32 digits, most significant first. -/
def base32Digits : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, n => base32Digits w (n / 32) ++ [n % 32]

/-- The number base-32 digits (most significant first) stand for. -/
def ofBase32 (ds : List Nat) : Nat := ds.foldl (fun a d => a * 32 + d) 0

/-- The 13 characters of a TID. -/
def Tid.encode (t : Tid) : String := String.ofList ((base32Digits 13 t.toNat).map tidChar)

instance : ToString Tid := ⟨Tid.encode⟩

/-- A TID's number, read back into microseconds and clock id. -/
def Tid.ofNat? (n : Nat) : Option Tid :=
  if h : n < tidMicrosBound * tidClockBound then
    some { micros := n / tidClockBound, clock := n % tidClockBound,
           micros_lt := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using h),
           clock_lt := Nat.mod_lt _ (by decide) }
  else none

/-- Read a TID: exactly 13 characters of the alphabet, the first of them `2`–`j` (the top bit
zero). Anything else is `none`. -/
def Tid.decode (s : String) : Option Tid :=
  let cs := s.toList
  if cs.length = 13 then
    match optMap tidDigit cs with
    | some ds => Tid.ofNat? (ofBase32 ds)
    | none => none
  else none

/-! ## Minting -/

/-- A session's TID minter: its clock id and the microseconds of the last TID it minted. -/
structure TidClock where
  /-- The clock id, below 1024. -/
  clock : Nat := 0
  /-- The microseconds of the last TID minted, if any. -/
  last : Option Nat := none
deriving Repr, DecidableEq, Inhabited

/-- A minter for a launch, with clock id `clockId % 1024`. -/
def TidClock.new (clockId : Nat) : TidClock := { clock := clockId % tidClockBound }

/-- The microseconds the next TID gets at clock reading `now`: `now`, unless that isn't past the
last one, then the last plus one. -/
def TidClock.next (g : TidClock) (now : Nat) : Nat :=
  match g.last with
  | none => now
  | some l => max now (l + 1)

/-- Mint a TID at clock reading `now` (microseconds since the epoch, from the app's clock):
the TID and the minter after it. `none` only past `2^53` microseconds (the year 2255). -/
def TidClock.mint (g : TidClock) (now : Nat) : Option (Tid × TidClock) :=
  if h : g.next now < tidMicrosBound then
    some ({ micros := g.next now, clock := g.clock % tidClockBound, micros_lt := h,
            clock_lt := Nat.mod_lt _ (by decide) },
          { g with last := some (g.next now) })
  else none

end CairnAtproto
