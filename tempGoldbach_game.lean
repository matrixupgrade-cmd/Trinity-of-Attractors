import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open List Nat

/--
  Sum of a sequential list like `[1,2,3,4,5]` is triangular:
  This checks whether a list is exactly `[1,2,...,k]`.
-/
def isSequential (L : List Nat) : Bool :=
  L == List.range (L.length + 1) |>.tail

/-- Detect whether left or right is a sequential pattern. -/
def sequentialSide (L : List Nat) : Bool := isSequential L

/--
  compress one side: repeatedly push a+b then recurse until 2 remain.
-/
def compressSide : List Nat → List Nat
| []        => []
| [a]       => [a]
| [a,b]     => [a,b]
| a :: b :: rest =>
    compressSide ((a + b) :: rest)

/-- compress both sides -/
def compress (L R : List Nat) : (List Nat × List Nat) :=
  (compressSide L, compressSide R)

/--
  Kick operation.
  If L is sequential, (+) kicks RIGHT: subtract 2 from left side and add 2 to right side on the (+) pivot.
  If R is sequential, kick LEFT.
  If neither sequential, do nothing.
  
  We assume lists have at least 2 numbers (after compression they always do).
-/
def kick (L R : List Nat) : (List Nat × List Nat) :=
  let L0 := L.getD 0 0
  let L1 := L.getD 1 0
  let R0 := R.getD 0 0
  let R1 := R.getD 1 0
  if sequentialSide L then
    -- kick RIGHT: left loses 2, right gains 2
    ([L0 - 2, L1], [R0 + 2, R1])
  else if sequentialSide R then
    -- kick LEFT: right loses 2, left gains 2
    ([L0 + 2, L1], [R0 - 2, R1])
  else
    (L, R)

/--
  One full update step:
  1. compress both sides
  2. check for sequential sum patterns
  3. apply kick if needed
-/
def step (L R : List Nat) : (List Nat × List Nat) :=
  let (Lc, Rc) := compress L R
  kick Lc Rc

/-- Check if both sides are primes and sum to the target even number. -/
def isGoal (target : Nat) (L R : List Nat) : Bool :=
  match L, R with
  | [a,b], [c,d] =>
      a.Prime && b.Prime && c.Prime && d.Prime &&
      (a + b + c + d = target)
  | _, _ => false

/--
  Play the tension-Goldbach convergence game.
  Start from (L,R) initial lists representing the even number.
  Run steps until:
    • goal reached
    • or max iterations
-/
partial def runSteps (target : Nat) (L R : List Nat) (limit := 2000) : Nat → IO Unit
| 0 => IO.println "Reached iteration limit."
| n+1 => do
  IO.println s!"step {limit - (n+1)} → L={L}, R={R}"
  if isGoal target L R then
    IO.println s!"✔️ Goal reached! {L} and {R} combine to {target} via primes."
  else
    let (L2, R2) := step L R
    runSteps target L2 R2 n

/--
  Build the initial sequential lists for the decomposition
  2N = N_left + N_right
  where Goldbach-style tension starts from (sum left, sum right).
-/
def initialLists (N : Nat) : (List Nat × List Nat) :=
  let L := List.range (N/2 + 1) |>.tail
  let R := List.range (N - N/2 + 1) |>.tail
  (L, R)

/-- Main interactive call: run the game starting from even number `n`. -/
def play (n : Nat) : IO Unit := do
  if n % 2 = 1 then
    IO.println "Input must be even."
  else
    let (L, R) := initialLists n
    runSteps n L R 2000
