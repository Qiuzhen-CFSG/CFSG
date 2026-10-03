module

public import FeitThompson.BGsection5.theorem_5_5_b
public import FeitThompson.BGsection4.lemma_4_7
public import FeitThompson.BGsection4.lemma_4_13
public import FeitThompson.BGsection4.theorem_4_16


/-! # Theorem 5.5(c.2) from BG Section 5 -/

private theorem commutatorAction_eq_bot_of_actsTrivially_local
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (htriv : ActsTrivially (A := A) (G := G)) :
    commutatorAction (A := A) (G := G) = ⊥ := by
  rw [commutatorAction_eq_closure, Subgroup.closure_eq_bot_iff]
  intro x hx
  rcases hx with ⟨a, g, rfl⟩
  change g⁻¹ * (a • g) = 1
  simp [ActsTrivially] at htriv
  rw [htriv a g]
  simp

