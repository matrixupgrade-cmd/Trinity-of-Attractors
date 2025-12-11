import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open List Nat

/-- Build the sequential list starting at t whose sum reaches s.
    Example:
      s=13, t=1 → [1,2,3,4,3]
      s=13, t=2 → [2,3,4,4]
      s=13, t=3 → [3,4,5,1]
      ...
-/
def buildSeq (s t : Nat) : List Nat :=
  let rec go (n curSum : Nat) (acc : List Nat) :=
    if curSum + (t + n) > s then
      let r := s - curSum
      if r = 0 then acc.reverse else (r :: acc).reverse
    else
      go (n+1) (curSum + (t+n)) ((t+n) :: acc)
  go 0 0 []

/-- Scan t = 1,2,3,... until the list length is ≤ 2. -/
def countdown (s : Nat) : List Nat :=
  let rec try (t : Nat) :=
    if t > s then [s] else
      let L := buildSeq s t
      if L.length ≤ 2 then L else try (t+1)
  try 1

/-- Normalize list to exactly 2 elements by padding left. -/
def asPair : List Nat → List Nat
| []        => [0,0]
| [x]       => [0,x]
| [x,y]     => [x,y]
| x::y::_   => [x,y]

/-- Apply the parity kick rule. -/
def kick (L R : List Nat) : (List Nat × List Nat) :=
  let a := L.getD 0 0
  let b := L.getD 1 0
  let c := R.getD 0 0
  let d := R.getD 1 0
  let sL := a + b
  let sR := c + d
  if sL % 2 = 0 then
    -- Left kicks right
    let a' := if a = 0 then 0 else a - 1
    let c' := c + 1
    ([a',b], [c',d])
  else if sR % 2 = 0 then
    -- Right kicks left
    let c' := if c = 0 then 0 else c - 1
    let a' := a + 1
    ([a',b], [c',d])
  else
    (L, R) -- freeze

/-- One step: countdown both sides to pairs, then apply kick. -/
def stepPair (sL sR : Nat) : (Nat × Nat) × (List Nat × List Nat) :=
  let L0 := asPair (countdown sL)
  let R0 := asPair (countdown sR)
  let (L1, R1) := kick L0 R0
  ((L1.sum, R1.sum), (L1, R1))

/-- Run simulation. -/
partial def run (N : Nat) (limit := 2000) : IO Unit := do
  if N % 2 = 1 then
    IO.println "Input must be even."
  else
    let init := (N/2, N/2)
    let rec loop (sL sR : Nat) (i : Nat) (prev? : Option (List Nat × List Nat)) := do
      if i = 0 then
        IO.println "Iteration limit reached."
      else
        let ((sL', sR'), (Lp, Rp)) := stepPair sL sR
        IO.println s!"step {limit - i}:  L={Lp},  R={Rp}   | sums = ({sL'}, {sR'})"
        match prev? with
        | none => loop sL' sR' (i - 1) (some (Lp, Rp))
        | some (LpPrev, RpPrev) =>
            if Lp = LpPrev ∧ Rp = RpPrev then
              IO.println "Frozen / absorbing state."
            else
              loop sL' sR' (i - 1) (some (Lp, Rp))
    loop init.1 init.2 limit none
