module

public import Theory.Frattini.PGroup

/-!
# Frattini adapters for BG section 1

The reusable finite `p`-group Frattini theory lives in
`Theory.Frattini.PGroup`. This module retains only the source-numbered wrapper
used by the Feit--Thompson development.
-/

/-- Lemma 1.7(a): if `H ⊔ Φ(R) = ⊤`, then `H = ⊤`. -/
public theorem lemma_1_7_a {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] : ∀ H : Subgroup R, H ⊔ frattini R = ⊤ → H = ⊤ :=
  frattini_nongenerating_of_isPGroup (R := R) (p := p)
