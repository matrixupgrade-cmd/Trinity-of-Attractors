import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Iterate
import Mathlib.Tactic

set_option autoImplicit false

/- ============================================================
  1. Phase types and FlowNetwork
============================================================ -/

inductive Phase := | Plasma | Liquid | Diamond

structure FlowNetwork (V : Type) [Fintype V] [DecidableEq V] where
  weight : V → V → ℝ≥0∞ -- weights, non-negative

variable {V : Type} [Fintype V] [DecidableEq V]

-- Placeholder step function: user can define greedy asymmetry
def MetamorphosisStep (G : FlowNetwork V) : FlowNetwork V := sorry

def trajectory (G₀ : FlowNetwork V) : ℕ → FlowNetwork V :=
  Function.iterate MetamorphosisStep G₀

/- ============================================================
  2. Recurrent / Liquid elements
============================================================ -/

def recurrent (G : FlowNetwork V) : Type :=
{ H : FlowNetwork V // ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory H n = trajectory H (n + p) }

def same_orbit (G : FlowNetwork V) (x y : recurrent G) : Prop :=
  ∃ k, trajectory x.val k = y.val

instance same_orbit_setoid (G : FlowNetwork V) : Setoid (recurrent G) :=
{ r := same_orbit G,
  iseqv :=
    ⟨
      fun x => ⟨0, rfl⟩,
      fun ⟨k,hk⟩ => ⟨k, hk.symm⟩,
      fun ⟨k,hk⟩ ⟨l,hl⟩ => ⟨k+l, by rw [Function.iterate_add_apply]; exact hl.trans hk⟩ ⟩ }

def OrbitIdx (G : FlowNetwork V) := Quotient (same_orbit_setoid G)

instance OrbitIdx_fintype (G : FlowNetwork V) [Fintype (recurrent G)] : Fintype (OrbitIdx G) :=
Fintype.ofFinite _

def orbit_rep (G : FlowNetwork V) (i : OrbitIdx G) : recurrent G := Classical.choose (Quotient.exists_rep i)

/-- period of an orbit representative -/
def orbit_period (G : FlowNetwork V) (x : recurrent G) : ℕ :=
let prop := x.property
Classical.choose (Classical.choose_spec prop).snd

/- ============================================================
  3. Direct product of cyclic groups
============================================================ -/

def Y (G : FlowNetwork V) : Type := ∀ i : OrbitIdx G, Fin (orbit_period G (orbit_rep G i))

instance Y_fintype (G : FlowNetwork V) [Fintype (recurrent G)] : Fintype (Y G) :=
Fintype.piFinite _

def op_Y (G :FlowNetwork V) (a b : Y G) : Y G :=
fun i => ⟨(a i).val + (b i).val % orbit_period G (orbit_rep G i), Nat.mod_lt _ _⟩

def id_Y (G : FlowNetwork V) : Y G := fun i => ⟨0, Nat.zero_lt _⟩

def inv_Y (G : FlowNetwork V) (a : Y G) : Y G :=
fun i => ⟨(orbit_period G (orbit_rep G i) - (a i).val) % orbit_period G (orbit_rep G i), Nat.mod_lt _ _⟩

def Group_Y (G : FlowNetwork V) : Group (Y G) :=
{ op := op_Y G,
  id := id_Y G,
  assoc := by intros a b c i; simp [op_Y]; rw [Nat.add_mod, Nat.add_mod],
  left_id := by intros a i; simp [op_Y]; rw [Nat.zero_add_mod],
  right_id := by intros a i; simp [op_Y]; rw [Nat.add_zero_mod],
  inv := inv_Y G,
  left_inv := by intros a i; simp [op_Y, inv_Y]; rw [Nat.add_mod, Nat.sub_add_cancel (le_of_lt (Fin.is_lt _))],
  right_inv := by intros a i; simp [op_Y, inv_Y]; rw [Nat.add_mod, Nat.sub_add_cancel (le_of_lt (Fin.is_lt _))] }

/- ============================================================
  4. Iso between recurrent elements and Y
============================================================ -/

def to_Y (G : FlowNetwork V) (x : recurrent G) : Y G :=
fun i =>
  let rep := orbit_rep G i
  let prop := rep.property
  let N := Classical.choose (Classical.choose_spec prop).fst
  let p := Classical.choose (Classical.choose_spec prop).snd
  let k := Nat.find (⟨true, exists k, trajectory rep.val (N + k) = x.val⟩)
  ⟨k % p, Nat.mod_lt _ _⟩

def from_Y (G : FlowNetwork V) (y : Y G) : recurrent G :=
let reps := fun i => orbit_rep G i
⟨trajectory (reps default).val (y default).val, sorry⟩ -- construct recurrent element (simplified)

def iso_recurrent_Y (G : FlowNetwork V) : recurrent G ≃ Y G :=
{ toFun := to_Y G,
  invFun := from_Y G,
  left_inv := fun x => sorry,
  right_inv := fun y => sorry }

/- ============================================================
  5. Trivial monoid for Diamond
============================================================ -/

structure TrivialMonoid (X : Type) : Monoid X where
  op := fun a b => a
  id := default
  assoc := by simp
  left_id := by simp
  right_id := by simp

/- ============================================================
  6. Full algebraic structure theorem
============================================================ -/

theorem Metamorphosis_to_algebraic_structure
  (G₀ : FlowNetwork V)
  [Fintype (recurrent G₀)] :
  ∃ φ : Phase,
    (φ = Liquid → ∃ (G' : Type) [Fintype G'] (A : Group G'), Nonempty (recurrent G₀ ≃ G')) ∧
    (φ = Diamond → ∃ (M : Monoid (FlowNetwork V)), Nonempty (∃ y, ∀ n ≥ 0, trajectory G₀ n = y)) ∧
    (φ = Plasma → ∀ n m, n ≠ m → trajectory G₀ n ≠ trajectory G₀ m) :=
by
  -- classify phase
  by_cases hDiamond : ∃ N, ∀ n ≥ N, trajectory G₀ n = trajectory G₀ N
  · let φ := Phase.Diamond
    use φ
    constructor; intro h; contradiction
    constructor; intro h
    use TrivialMonoid (FlowNetwork V)
    rcases hDiamond with ⟨N,hN⟩
    use trajectory G₀ N, hN
    intro h; contradiction
  · by_cases hLiquid : ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory G₀ n = trajectory G₀ (n + p)
    · let φ := Phase.Liquid
      use φ
      constructor; intro h
      let G' := Y G₀
      use G', inferInstance, Group_Y G₀, ⟨iso_recurrent_Y G₀⟩
      constructor; intro h; contradiction
      intro h; contradiction
    · let φ := Phase.Plasma
      use φ
      constructor; intro h; contradiction
      constructor; intro h; contradiction
      intro n m hnm
      intro eq
      -- contradiction: repetition would imply Diamond or Liquid
      sorry
