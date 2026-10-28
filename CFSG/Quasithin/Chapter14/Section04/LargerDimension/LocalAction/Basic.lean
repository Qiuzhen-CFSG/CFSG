module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupAction.ModelConjugation

/-!
# Residuals and conjugation in the large-dimensional local configuration

The source family consists of actual two-perfect subgroups. Adjoining the
normalizing Sylow two-subgroup therefore recovers each member as the residual
of its whole parabolic. Residual monotonicity then computes the residual of
every intermediate subgroup, without identifying that subgroup with its
residual. We also retain the literal conjugation map on the moved space.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.8 and 14.4.13, printed pp.1009 and 1012.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension
variable {G : Type*} [Group G]

/-- The embedded residual equality has its intrinsic two-perfect meaning. -/
theorem isPPerfect_of_twoResidual_eq {X : Subgroup G}
    (hX : twoResidual X = X) : IsPPerfect 2 X := by
  apply (pResidual_eq_top_iff 2 X).mp
  apply map_injective X.subtype_injective
  simpa only [twoResidual, ← MonoidHom.range_eq_map, range_subtype] using hX

/-- A source family member is the residual of its whole parabolic `XT`. -/
theorem ThreeExtension.residual_join {H T X : Subgroup G}
    (hX : ThreeExtension H T X) (hT : IsPGroup 2 T) :
    twoResidual (X ⊔ T) = X :=
  embedded_pResidual_join_pGroup X T
    (isPPerfect_of_twoResidual_eq hX.residual_eq) hT hX.T_normalizes

/-- Residuals are constant between a two-perfect subgroup and its
normalizing two-group supplement. -/
theorem twoResidual_eq_of_between {E T A : Subgroup G}
    (hE : twoResidual E = E) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (E : Set G)) (hEA : E ≤ A) (hA : A ≤ E ⊔ T) :
    twoResidual A = E := by
  have hj : twoResidual (E ⊔ T) = E := embedded_pResidual_join_pGroup E T
    (isPPerfect_of_twoResidual_eq hE) hT hn
  exact le_antisymm ((embedded_pResidual_mono 2 hA).trans_eq hj)
    (hE ▸ embedded_pResidual_mono 2 hEA)

namespace LocalAction

/-- The whole parabolic over T associated with the source I₂. The
12.8.9(1) product I₂ = O²(P)U becomes I₂ = L₂U in the current notation.
Adjoining T gives L₂T because U ≤ T; no equality I₂ = L₂T is assumed. -/
theorem source_I₂_join_T (I₂ L₂ U T : Subgroup G)
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ T) : I₂ ⊔ T = L₂ ⊔ T := by
  rw [hI, sup_assoc, sup_eq_right.mpr hUT]

/-- Conjugation by the actual ambient actor, restricted to the actual module. -/
noncomputable def conjugation (A W : Subgroup G)
    (h : A ≤ normalizer (W : Set G)) : A →* MulAut W :=
  Theory.GroupAction.ModelConjugation.action A W h (MulEquiv.refl W)

theorem conjugation_apply (A W : Subgroup G)
    (h : A ≤ normalizer (W : Set G)) (a : A) (w : W) :
    (conjugation A W h a w : G) = (a : G) * (w : G) * (a : G)⁻¹ := by rfl

/-- The kernel is the relative centralizer, before any two-core calculation. -/
theorem conjugation_ker (A W : Subgroup G)
    (h : A ≤ normalizer (W : Set G)) :
    (conjugation A W h).ker = (centralizer (W : Set G)).subgroupOf A := by
  exact Theory.GroupAction.ModelConjugation.action_ker A W h (MulEquiv.refl W)

/-- Both extraspecial groups act on the moved space once it contains their
central lines and lies in their intersection. These are the exact inclusions
used at the start of the proof of 14.4.8(2). -/
theorem extraspecial_join_normalizes_movedSpace
    (U Ug Z Zg V₂ X : Subgroup G)
    (hU : ⁅U, U⁆ ≤ Z) (hUg : ⁅Ug, Ug⁆ ≤ Zg)
    (hZ : Z ≤ movedSpace V₂ X) (hZg : Zg ≤ movedSpace V₂ X)
    (hW : movedSpace V₂ X ≤ U ⊓ Ug) :
    U ⊔ Ug ≤ normalizer (movedSpace V₂ X : Set G) := by
  apply sup_le
  · exact le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl (hW.trans inf_le_left)).trans (hU.trans hZ))
  · exact le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl (hW.trans inf_le_right)).trans (hUg.trans hZg))

/-- The literal `I₂ = ⟨U,Uᵍ⟩` conjugation homomorphism supplied by those
extraspecial commutator bounds. Its image still has to be computed. -/
noncomputable def extraspecialJoinAction
    (U Ug Z Zg V₂ X : Subgroup G)
    (hU : ⁅U, U⁆ ≤ Z) (hUg : ⁅Ug, Ug⁆ ≤ Zg)
    (hZ : Z ≤ movedSpace V₂ X) (hZg : Zg ≤ movedSpace V₂ X)
    (hW : movedSpace V₂ X ≤ U ⊓ Ug) :
    (U ⊔ Ug : Subgroup G) →* MulAut (movedSpace V₂ X) :=
  conjugation _ _ (extraspecial_join_normalizes_movedSpace U Ug Z Zg V₂ X
    hU hUg hZ hZg hW)

end LocalAction
end CFSG.Quasithin.Chapter14.Section04.LargerDimension
