/-
01_interaction_weathering.lean

Purpose:
Show that interaction of two finite semigroups, followed by weathering
(quotient by eventual indistinguishability), can produce new periodic
elements not inherited from either system alone.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Iterate
import Mathlib.Algebra.Group.Semigroup

set_option autoImplicit false

/-- Two pre-gyro systems: finite semigroups, no identity, no inverse. -/
variable {A B : Type}
variable [Semigroup A] [Semigroup B]
variable [Fintype A] [Fintype B]

/-!
## Interaction semigroup
Elements are finite mixed words over A ⊔ B.
-/

/-- A mixed interaction word. -/
structure Interaction where
  word : List (Sum A B)

namespace Interaction

/-- Concatenation of interaction words. -/
def mul (x y : Interaction) : Interaction :=
⟨x.word ++ y.word⟩

instance : Mul Interaction := ⟨mul⟩

/-- Semigroup structure by concatenation. -/
instance : Semigroup Interaction := by
  refine ⟨?assoc⟩
  intro x y z
  cases x; cases y; cases z
  simp [Mul.mul, mul, List.append_assoc]

end Interaction

/-!
## Iteration dynamics
-/

/-- Iteration of interaction under semigroup multiplication. -/
def iter (n : Nat) (x : Interaction) : Interaction :=
Nat.iterate (fun y => y * x) n x

/-!
## Weathering
Two interactions are equivalent if they become indistinguishable
after sufficient iteration.
-/

/-- Eventual indistinguishability under iteration. -/
def eventually_equiv (x y : Interaction) : Prop :=
∃ N : Nat, ∀ n ≥ N, iter n x = iter n y

/-- Weathered interaction space. -/
def Weathered : Type :=
Quot eventually_equiv

/-!
## Periodicity
What survives weathering.
-/

/-- A weathered element is periodic if it repeats under iteration. -/
def is_periodic (x : Weathered) : Prop :=
∃ n : Nat, n > 0 ∧
  Quot.liftOn x
    (fun r => iter n r)
    (by
      intro a b h
      -- well-definedness of iteration under equivalence
      sorry
    )
  = x

/-- The periodic core of the weathered system. -/
def PeriodicCore : Set Weathered :=
{ x | is_periodic x }

/-!
## Embedding original systems
-/

/-- Embed A-actions as interaction words. -/
def liftA (a : A) : Interaction :=
⟨[Sum.inl a]⟩

/-- Embed B-actions as interaction words. -/
def liftB (b : B) : Interaction :=
⟨[Sum.inr b]⟩

/-- Lift A into the weathered space. -/
def liftA_w (a : A) : Weathered :=
Quot.mk _ (liftA a)

/-- Lift B into the weathered space. -/
def liftB_w (b : B) : Weathered :=
Quot.mk _ (liftB b)

/-!
## Innovation theorem
Mixed interaction creates new cycles not inherited from A or B.
-/

/--
There exists a periodic weathered interaction that does not come
from either system alone.
-/
theorem mixed_words_create_new_cycles :
  ∃ x : Weathered,
    is_periodic x ∧
    (¬ ∃ a : A, x = liftA_w a) ∧
    (¬ ∃ b : B, x = liftB_w b) :=
by
  -- Core existence argument:
  -- finiteness → eventual repetition → periodic class
  -- mixed words ensure non-trivial origin
  sorry
