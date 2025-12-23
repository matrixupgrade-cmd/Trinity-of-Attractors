theorem liquid_phase_turing_universal
  {Q Σ : Type}
  [DecidableEq Q] [DecidableEq Σ]
  [Fintype Q] [Fintype Σ]
  (blank : Σ)

  -- TM encoded as a local cell automaton
  (cell : Cell Q Σ)

  -- correctness of the local rule
  (cell_correct :
    ∀ cfg : TM.Cfg Q Σ,
      decode
        (liquid_step
          (cell := cell)
          (blank := blank)
          (encode (blank := blank) cfg))
      = TM.step cfg)

  -- boundedness invariant (liquid phase)
  (maxTape : ℕ)
  (hbounded :
    ∀ n cfg,
      let ms := iter_liquid n (encode (blank := blank) cfg)
      in
      ms.tape.left.length
        + ms.tape.right.length
        + 1 ≤ maxTape) :

  ∀ cfg : TM.Cfg Q Σ,
  ∃ n₀ period : ℕ, period > 0 ∧
    (∀ n ≥ n₀,
      core (iter_liquid (n + period) (encode (blank := blank) cfg))
        = core (iter_liquid n (encode (blank := blank) cfg))) ∧
    (∀ n,
      decode_at
        (cell := cell)
        (iter_liquid n (encode (blank := blank) cfg))
        n
      = Function.iterate TM.step n cfg)
