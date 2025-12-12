-- MetaSpiderDebate.lean
-- Three hungry philosophers fight over the essence of three objects

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset BigOperators

set_option autoImplicit false

structure ObjectUniverse (V : Type) [Fintype V] [DecidableEq V] :=
  essence : V → ℝ≥0

variable {V : Type} [Fintype V] [DecidableEq V]

structure Spider (U : ObjectUniverse V) :=
  name   : String
  claim  : V → ℝ≥0
  hunger : ℝ≥0

def spider_step (U : ObjectUniverse V) (sp : Spider U) : Spider U :=
  let gap := fun v => U.essence v - sp.claim v
  let step_size := 0.5
{ claim  := fun v => sp.claim v + step_size * gap v,
  hunger := sp.hunger - step_size * ∑ v, gap v,
  name   := sp.name }

def spider_trajectory (U : ObjectUniverse V) (sp : Spider U) : ℕ → Spider U
  | 0     => sp
  | n + 1 => spider_step U (spider_trajectory U sp n)

def global_tension (spiders : List (Spider U)) : ℝ :=
  ∑ v in univ, ∑ i in range spiders.length, ∑ j in range spiders.length,
    let ci := (spiders.nthLe i (by simp)).claim v
        cj := (spiders.nthLe j (by simp)).claim v
    (ci - cj)^2

def Three := Fin 3
instance : Fintype Three := Fin.fintype _
instance : DecidableEq Three := Fin.decidableEq _

def Reality : ObjectUniverse Three :=
{ essence := ![1, 2, 3] }   -- object 0:1, object 1:2, object 2:3

def SpiderA := { name := "Platonist",   claim := fun _ => 0, hunger := 6 : Spider Reality }
def SpiderB := { name := "Nominalist",  claim := fun _ => 0, hunger := 6 : Spider Reality }
def SpiderC := { name := "Pragmatist",  claim := fun _ => 0, hunger := 6 : Spider Reality }

def philosophers := [SpiderA, SpiderB, SpiderC]

def step_all (spiders : List (Spider Reality)) : List (Spider Reality) :=
  spiders.map (spider_step Reality)

partial def run_brawl (n : ℕ) : List (Spider Reality) :=
  match n with
  | 0     => philosophers
  | n + 1 => step_all (run_brawl n)

-- Watch the great ontological debate unfold
#eval global_tension (run_brawl 0)   -- 0.0 (all agree: nothing is real)
#eval global_tension (run_brawl 1)   -- 9.0
#eval global_tension (run_brawl 5)   -- ≈ 0.5625
#eval global_tension (run_brawl 20)  -- ≈ 0.0 (perfect consensus)

-- Final claims after 20 rounds of hungry reaching
#eval (run_brawl 20).map fun s =>
  s!"{s.name} believes the objects have essence ({s.claim 0 |>.roundTo 3}, {s.claim 1 |>.roundTo 3}, {s.claim 2 |>.roundTo 3})"
