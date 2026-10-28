module
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerRank
public import Theory.SpecificGroups.BinaryLinear.SmallLeviRank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Cubic rank of a binary four-dimensional point stabilizer

The stabilizer of a nonzero natural vector is its line parabolic.
Modulo its actual two-core the two diagonal blocks are GL₁(2) and GL₃(2).
Their orders are 1 and 168, so no elementary abelian group of order nine
can occur. Odd prime rank is unchanged by the two-core quotient.

This is the degree-four obstruction in the repeated-natural branch of
Aschbacher--Smith, 15.2.23(a), printed p.1117.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
namespace BinaryLinear.PointStabilizerRank

private instance {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] : Finite (BinaryLinear.GL V) :=
  Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective

private theorem linearGroup_card_one : Nat.card (LinearGroup 1) = 1 := by
  rw [← Nat.card_congr (matrixEquivLinear 1).toEquiv, Matrix.card_GL_field]
  norm_num

private theorem linearGroup_card_three : Nat.card (LinearGroup 3) = 168 := by
  rw [← Nat.card_congr (matrixEquivLinear 3).toEquiv, Matrix.card_GL_field]
  norm_num
  decide

/-- A nonzero natural point in dimension four has cubic-rank-one stabilizer. -/
theorem natural_four_threeRank_le_one (v : Fin 4 → ZMod 2) (hv : v ≠ 0) :
    primeRank 3 (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) v) ≤ 1 := by
  rw [primeRank_equiv 3 (naturalStabilizerEquiv 4 v), stabilizer_eq_parabolic]
  let W := Submodule.span (ZMod 2) {v}
  have hd : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hv
  have hq : Module.finrank (ZMod 2) ((Fin 4 → ZMod 2) ⧸ W) = 3 := by
    have h := W.finrank_quotient_add_finrank
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  let a : W ≃ₗ[ZMod 2] Space 1 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let b : ((Fin 4 → ZMod 2) ⧸ W) ≃ₗ[ZMod 2] Space 3 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (parabolic W)) pCore_isPGroup,
    primeRank_equiv 3 (quotientTwoCoreEquivOfCoordinates W a b)]
  apply primeRank_le_one_of_square_not_dvd
  rw [Nat.card_prod, linearGroup_card_one, linearGroup_card_three]
  decide

end BinaryLinear.PointStabilizerRank
