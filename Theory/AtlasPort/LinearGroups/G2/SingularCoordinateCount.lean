module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/SingularCoordinateCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearAlgebra.QuadraticRemainingFiber

@[expose] public section

/-!
# The uniform singular coordinate count for the split octonion model

The trace-zero norm equation is `u · v = t²`, with two three-coordinate blocks.
Negating the second block identifies its fixed-`u` fibres with the previously
proved odd-dimensional quadratic fibres. That proof uses nonzero linear
functional fibres, and is valid in every characteristic; no orthogonal group
order or simplicity statement is used here.
-/

noncomputable section
namespace Atlas.G2
variable (F : Type*) [Field F]

/-- Coordinates `(u,v,t)` for the trace-zero norm equation, including zero. -/
abbrev SingularCoordinates :=
  {p : (Fin 3 → F) × (Fin 3 → F) × F //
    Atlas.DotProduct.functional p.1 p.2.1 = p.2.2 ^ 2}

/-- The explicit sign change identifying the existing quadratic fibre calculation. -/
def singularCoordinatesFiberEquiv : SingularCoordinates F ≃
    Σ u : Fin 3 → F, Atlas.Orthogonal.BRemaining u where
  toFun p := ⟨p.val.1, ⟨(-p.val.2.1,p.val.2.2), by
    rw [map_neg, p.prop]
    exact neg_add_cancel _⟩⟩
  invFun p := ⟨(p.1,-p.2.val.1,p.2.val.2), by
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_right p.2.prop⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    simp

/-- There are `q⁶` singular coordinate vectors, uniformly in every characteristic. -/
theorem card_singularCoordinates [Finite F] :
    Nat.card (SingularCoordinates F) = Nat.card F ^ 6 := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_congr (singularCoordinatesFiberEquiv F), Nat.card_sigma]
  simp_rw [Atlas.Orthogonal.card_remainingB]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin, Nat.cast_id, ← pow_add]

/-- Nonzero solutions of the trace-zero norm equation. -/
abbrev NonzeroSingularCoordinates := {p : SingularCoordinates F // p.val ≠ 0}

/-- Removing the unique zero coordinate vector leaves `q⁶−1` solutions. -/
theorem card_nonzeroSingularCoordinates [Finite F] :
    Nat.card (NonzeroSingularCoordinates F) = Nat.card F ^ 6 - 1 := by
  classical
  let := Fintype.ofFinite F
  let : Unique {p : SingularCoordinates F // p.val = 0} :=
    { default := ⟨⟨0,by simp⟩,rfl⟩
      uniq := fun p => Subtype.ext (Subtype.ext p.prop) }
  have hz : Fintype.card {p : SingularCoordinates F // p.val = 0} = 1 :=
    Fintype.card_unique
  change Nat.card {p : SingularCoordinates F // ¬ p.val = 0} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hz,
    ← Nat.card_eq_fintype_card, card_singularCoordinates]

end Atlas.G2
