/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryWalshRank.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.BinaryWalshTranslation
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Ring.Commute

/-!
# Walsh coefficients from polar rank

Rank-nullity computes the radical cardinality. The squared Walsh
identity then gives the exact possible coefficients in dimension four.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryWalshRank.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Rank of the actual polar bilinear map, not a supplied quadratic label. -/
def binaryWalshPolarRank (q : QuadraticMap (ZMod 2) V (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range q.polarBilin)

theorem binaryWalshRadical_finrank (q : QuadraticMap (ZMod 2) V (ZMod 2)) :
    Module.finrank (ZMod 2) (binaryWalshRadical q) =
      Module.finrank (ZMod 2) V - binaryWalshPolarRank q := by
  have h := q.polarBilin.finrank_range_add_finrank_ker
  change binaryWalshPolarRank q + Module.finrank (ZMod 2) (binaryWalshRadical q) =
    Module.finrank (ZMod 2) V at h
  omega

theorem binaryWalshRadical_card (q : QuadraticMap (ZMod 2) V (ZMod 2)) :
    Fintype.card (binaryWalshRadical q) =
      2 ^ (Module.finrank (ZMod 2) V - binaryWalshPolarRank q) := by
  classical
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, binaryWalshRadical_finrank]

/-- The full-rank four-dimensional Walsh coefficients are exactly ±4. -/
theorem binaryWalsh_rank_four_values (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (hd : Module.finrank (ZMod 2) V = 4)
    (hr : binaryWalshPolarRank q = 4) (ha : BinaryWalshCompatible q a) :
    binaryWalsh q a = 4 ∨ binaryWalsh q a = -4 := by
  have h := binaryWalsh_sq_of_compatible q a ha
  rw [binaryWalshRadical_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    hd, hr] at h
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num at h ⊢
  exact h

/-- The nonzero rank-two four-dimensional Walsh coefficients are exactly ±8. -/
theorem binaryWalsh_rank_two_values (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (hd : Module.finrank (ZMod 2) V = 4)
    (hr : binaryWalshPolarRank q = 2) (ha : BinaryWalshCompatible q a) :
    binaryWalsh q a = 8 ∨ binaryWalsh q a = -8 := by
  have h := binaryWalsh_sq_of_compatible q a ha
  rw [binaryWalshRadical_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    hd, hr] at h
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num at h ⊢
  exact h

/-- The nonzero rank-zero four-dimensional Walsh coefficients are exactly ±16. -/
theorem binaryWalsh_rank_zero_values (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (hd : Module.finrank (ZMod 2) V = 4)
    (hr : binaryWalshPolarRank q = 0) (ha : BinaryWalshCompatible q a) :
    binaryWalsh q a = 16 ∨ binaryWalsh q a = -16 := by
  have h := binaryWalsh_sq_of_compatible q a ha
  rw [binaryWalshRadical_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    hd, hr] at h
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num at h ⊢
  exact h

end Atlas.Algebra
