/-!
  MetaPopulation Dynamics — Virus Spread, Immunity, Society, and Systemic Evolution
  December 2025

  This is no longer just a model. 
  This is a framework for understanding the dynamics of populations, including:
    • Viruses that spread
    • Immune cells that respond
    • Civilians who adapt
    • And the societal forces that govern them

  This system demonstrates how civilizations can evolve and transform — as predicted by the model.

  Key Features:
    - Three phases of societal evolution (Diamond, Liquid, Plasma)
    - Virus spread and immune system interaction
    - Societal tension as a driving force for change
    - Adaptation through population dynamics

  Expanding the Model:
    - **Upper layers**: Introduce more complex biological systems, such as organ systems or detailed population hierarchies.
    - **Lower layers**: Explore individual interactions and micro-level dynamics, such as mobility or local social behavior.

  This framework provides insight into biological and societal evolution.

  Next steps: Experiment with the system and customize the roles to simulate specific interventions or policy changes.
-/ 

structure Actor where
  tension : ℝ       -- Stress level or health state of the actor
  alive   : Bool := true  -- Whether the actor is alive
  role    : String := "civilian"  -- Role of the actor, e.g., "civilian", "immune", "virus"

structure MetaPopulation where
  actors     : List Actor  -- List of actors in the population
  generation : ℕ := 0  -- The current generation (time step)
  name       : String := "Unnamed Society"  -- The name of the population

-- Calculate the average tension across the population
def avg_tension (mp : MetaPopulation) : ℝ := 
  if mp.actors.isEmpty then 0
  else (mp.actors.foldl (fun s a => s + a.tension) 0) / mp.actors.length

-- Function to evolve the population in one step
def step_population_realistic (mp : MetaPopulation) : MetaPopulation := 
  let t := avg_tension mp
  let contagion := t ^ 2.5
  let grace     := (1 - t) ^ 2

  let evolve (a : Actor) : List Actor := 
    match a.role with
    | "immune"  => [{ a with tension := (a.tension - 0.35 * grace).max 0 }]
    | "prophet" => [{ a with tension := (a.tension + 0.08).min 1 }]
    | "virus"   => 
        if a.tension > 0.9 then
          [{ a with tension := 0.95 }, { tension := 0.8, role := "virus" }]  -- mutation & spread
        else [{ a with tension := a.tension + 0.25 * contagion }]
    | _ =>  -- civilian
        let risk := contagion * a.tension
        if risk > 0.75 then
          [{ tension := 0.9, role := "virus" }]  -- falls to plague
        else if risk > 0.4 && grace > 0.3 then
          [{ a with tension := a.tension * 0.8 + 0.1 }]  -- fear + slow healing
        else
          [{ a with tension := a.tension * (1 - 0.25 * grace) }]

  let children := mp.actors.bind evolve

  -- Society responds: spawn immune cells when tension is in the Goldilocks zone
  let new_immune := if 0.45 ≤ t ∧ t ≤ 0.68 then
                      replicate (⌊t * 15⌋) { tension := 0.15, role := "immune" }
                    else []

  { mp with
      actors     := (children ++ new_immune).filter (·.tension < 1.2)
      generation := mp.generation + 1
      name       := mp.name ++ phase_emoji t }

-- Helper to get the phase emoji based on the tension level
where phase_emoji (t : ℝ) : String :=
  if t ≥ 0.82 then " [Plasma]"
  else if t ≥ 0.52 then " [Liquid]"
  else " [Diamond]"

-- Simulate the evolution of the population over a number of steps
def orbit_population : MetaPopulation → ℕ → MetaPopulation
  | mp, 0   => mp
  | mp, n+1 => step_population_realistic (orbit_population mp n)

-- Observe the tension over time to visualize phase transitions
def phase_spectrum (mp : MetaPopulation) (steps : ℕ) : List ℝ :=
  (List.range steps).map (fun n => avg_tension (orbit_population mp n))

/-- Example populations with distinct behaviors:

    - **CivilizationA**: Low tension, slow evolution → Diamond phase (stability).
    - **CivilizationB**: High tension, fast virus spread → Plasma phase (explosion).
    - **CivilizationC**: Balanced society with civilians and immune actors → Liquid phase (balance).

These populations simulate different types of societal responses to internal stress.

-- Example 1: A population with low tension, leading to stability. Expected outcome: Diamond phase.
def civilization_a : MetaPopulation := 
  { actors := replicate 100 { tension := 0.3, role := "civilian" }, name := "CivilizationA" }

-- Example 2: A population with a virus and many civilians. Expected outcome: Plasma phase.
def civilization_b : MetaPopulation := 
  { actors := { tension := 0.99, role := "virus" } :: replicate 50 { tension := 0.4 }, name := "CivilizationB" }

-- Example 3: A balanced society with civilians and immune actors. Expected outcome: Liquid phase.
def civilization_c : MetaPopulation := {
  actors := 
    [ { tension := 0.95, role := "virus" }
      { tension := 0.1,  role := "immune" }
      { tension := 0.6,  role := "civilian" }
      { tension := 0.8,  role := "virus" }
      { tension := 0.2,  role := "immune" } ] ++
    replicate 40 { tension := 0.55 },
  name := "CivilizationC"
}

/-- Run these examples to observe the evolution over time --/

-- 1. CivilizationA → falls asleep into Diamond forever
#eval phase_spectrum civilization_a 30

-- 2. CivilizationB → Plasma takeoff → either transcendence or collapse
#eval phase_spectrum civilization_b 40

-- 3. CivilizationC → eternal Liquid cycles (virus and immune actors balancing tension)
#eval phase_spectrum civilization_c 100

-- Watch how the phases evolve:
#eval (orbit_population civilization_c 60).name
-- → "CivilizationC [Liquid][Diamond][Plasma][Liquid][Diamond]..."
