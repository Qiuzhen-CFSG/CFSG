/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/LinearAlgebra/AffineEquivParameters.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Parameters of affine automorphisms

Evaluation at zero and the linear part identify affine automorphisms
with translation-linear pairs, yielding their cardinality formula.

Source: Gerald Höhn, ATLAS, `Atlas/LinearAlgebra/AffineEquivParameters.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.LinearAlgebra

variable (F V : Type*) [Field F] [AddCommGroup V] [Module F V]

/-- An affine automorphism is determined by its translation and linear part. -/
def affineEquivParameters : (V ≃ᵃ[F] V) ≃ V × (V ≃ₗ[F] V) where
  toFun a := (a 0,a.linear)
  invFun p := AffineEquiv.ofLinearEquiv p.2 0 p.1
  left_inv a := by
    ext v
    change a.linear (v-0)+a 0=a v
    simpa using (a.map_vadd (0 : V) v).symm
  right_inv p := by
    apply Prod.ext
    · simp
    · rfl

theorem affineEquiv_card : Nat.card (V ≃ᵃ[F] V) = Nat.card V * Nat.card (V ≃ₗ[F] V) := by
  rw [Nat.card_congr (affineEquivParameters F V),Nat.card_prod]

end Atlas.LinearAlgebra
