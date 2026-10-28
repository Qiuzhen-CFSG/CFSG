module

public import Theory.SpecificGroups.PSL3.SevenAction.NormalForm
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# A nonidentity inner actor in every faithful four-group action on PSL₃(7)

The linear-times-graph normal form puts at least one nonidentity element of
any four-group in the linear conjugation image. Cubing a linear conjugating
matrix and correcting its determinant by a scalar makes its induced cube
inner. A linear involution is therefore inner. Faithfulness makes its inner
representative an actual projective involution, so the canonical involution
lifting and conjugacy calculation identifies it with the standard actor.

The lifting uses SL₃(7) with its center of order three, not a centerless
replacement for the linear cover.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the PSL₃(7)
case in the proof of 15.3.38, printed p.1137; the automorphism coverage is
GLS3, Theorem 2.5.12(a).
-/

public section

open scoped MatrixGroups IsKleinFour
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.SevenAction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem linearConj_scalar (u : (ZMod 7)ˣ) :
    linearConj (ZMod 7) (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := projection_surjective (ZMod 7) y
  change QuotientGroup.mk (linearConjSL (ZMod 7) (GeneralLinearGroup.scalar (Fin 3) u) x) =
    QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

/-- Scalar determinant correction makes the cube of every linear actor inner. -/
theorem linearConj_cube_inner (g : GL (Fin 3) (ZMod 7)) :
    linearConj (ZMod 7) g ^ 3 ∈ MulAut.innerSubgroup Model := by
  let m := GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g)⁻¹ * g ^ 3
  have hm : GeneralLinearGroup.det m = 1 := by
    simp only [m, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow,
      inv_pow, inv_mul_cancel]
  let x := (slEquivDetKernel (ZMod 7)).symm ⟨m, hm⟩
  refine ⟨projection (ZMod 7) x, ?_⟩
  calc
    MulAut.conj (projection (ZMod 7) x) = linearConj (ZMod 7) (SpecialLinearGroup.toGL x) :=
      (linearConj_toGL (ZMod 7) x).symm
    _ = linearConj (ZMod 7) m := by rw [slEquivDetKernel_symm_toGL]
    _ = _ := by
      dsimp only [m]
      rw [map_mul, linearConj_scalar, one_mul, map_pow]

/-- An involution in the linear conjugation image is inner. -/
theorem linearConj_involution_inner (g : GL (Fin 3) (ZMod 7))
    (hg : linearConj (ZMod 7) g ^ 2 = 1) :
    linearConj (ZMod 7) g ∈ MulAut.innerSubgroup Model := by
  simpa only [pow_succ, hg, one_mul] using linearConj_cube_inner g

/-- Every four-group action has a nonidentity actor with no graph factor. -/
theorem four_action_has_linear {A : Type*} [Group A] [IsKleinFour A]
    (ψ : A →* MulAut Model) :
    ∃ a : A, a ≠ 1 ∧ ∃ g : GL (Fin 3) (ZMod 7), ψ a = linearConj (ZMod 7) g := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsKleinFour.card_four]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := A)
    (by simp only [ENat.card_eq_coe_natCard, IsKleinFour.card_four]; decide) 1 a
  have hab : a * b ≠ 1 := by
    intro he
    exact hba ((eq_inv_of_mul_eq_one_right he).trans (IsKleinFour.inv_eq_self a))
  obtain ⟨g, hg | hg⟩ := automorphism_normal_form (ψ a)
  · exact ⟨a, ha, g, hg⟩
  obtain ⟨h, hh | hh⟩ := automorphism_normal_form (ψ b)
  · exact ⟨b, hb, h, hh⟩
  refine ⟨a * b, hab, g * inverseTransposeGL h, ?_⟩
  rw [map_mul, hg, hh, mul_assoc, ← mul_assoc (graph (ZMod 7)),
    graph_linearConj, mul_assoc, ← pow_two, graph_sq, mul_one, ← map_mul]

/-- In a faithful action, some nonidentity actor is conjugate to the standard
inner involution of the actual projective group. -/
theorem four_action_has_inner {A : Type*} [Group A] [IsKleinFour A]
    (ψ : A →* MulAut Model) (hinj : Function.Injective ψ) :
    ∃ a : A, a ≠ 1 ∧ ∃ g : Model,
      ψ a = MulAut.conj g * actor * (MulAut.conj g)⁻¹ := by
  obtain ⟨a, ha, m, hm⟩ := four_action_has_linear ψ
  have hsq : ψ a ^ 2 = 1 := by rw [pow_two, ← map_mul, IsKleinFour.mul_self, map_one]
  have hi : ψ a ∈ MulAut.innerSubgroup Model := by
    rw [hm] at hsq ⊢
    exact linearConj_involution_inner m hsq
  obtain ⟨t, ht⟩ := hi
  let : Group.IsPerfect SL(3, ZMod 7) := Atlas.sl_perfect 3 (by decide)
  have hci : Function.Injective (MulAut.conj : Model →* MulAut Model) :=
    MulAut.conj_injective_of_center_eq_bot
      (Group.IsPerfect.center_quotient_center_eq_bot SL(3, ZMod 7))
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · apply hci
      rw [map_pow, ht, hsq, map_one]
    · intro he
      apply ha
      apply hinj
      rw [← ht, he, map_one, map_one]
  obtain ⟨g, hg⟩ := involution_conjugate t ht2
  refine ⟨a, ha, g, ?_⟩
  rw [← ht, ← hg, map_mul, map_mul, map_inv]
  rfl

end Matrix.PSL3.SevenAction
