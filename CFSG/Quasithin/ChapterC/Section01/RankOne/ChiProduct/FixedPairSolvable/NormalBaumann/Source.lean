module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann.Action
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann.Lift
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.FixedSource

/-!
# The full solvable fixed-pair source in an original minimal parabolic

The normal group E=O²(G)Baum(T) escapes the original fixed control. Its Sylow
is the original Baumann subgroup and its omega-center action is abelian,
including when T permutes two natural factors. Transport the same pair to E
and apply the proved single-action theorem there. Normality of E makes its
actual block subnormal in G, and the alpha bound proves original Thompson
movement and support in the original canonical module.

This proves the paired branch without asserting minimality or Frattini
heredity for an arbitrary cubic-factor preimage.
Source: Aschbacher--Smith C.1.26--28 and 14.1.11, pp.132--134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
open ChapterB GlaubermanNiles SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]

theorem minimal_parabolic_moving_alternatingThree_of_fixed_pair_escape
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hproper : control T D ≠ ⊤) (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) :
    ∃ A : Subgroup G, IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅normalClosure
        (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ∧
      ⁅normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ≠ ⊥ := by
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hU : IsPReduced 2 U := omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let : IsElementaryAbelian 2 U := hU.elementary
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
    apply thompson_moves_of_escape T D ⊤ U le_top le_top (inf_le_left.trans le_normalClosure)
    exact fun hh => hproper (top_unique hh)
  let : Group.IsSolvable G := solvable_of_reduced_minimalParabolic_action T hP U hU hJ
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hsolv
  let E := pResidual 2 G ⊔ baumann (T : Subgroup G)
  let : E.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G)
    (pResidual_sup_sylow_eq_top T)
  obtain ⟨S,hS,hab,hW⟩ := exists_abelian_baumann_action T hP U hU hJ hrank hsolv
  have hfE : generalizedFitting E = pCore 2 E := selected_baumann_fitting
    (T : Subgroup G) (pResidual 2 G) (pResidual_sup_sylow_eq_top T) hfit
  have hout : ¬ E ≤ control T D := by
    intro hh
    apply hproper
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top T]
    exact sup_le (le_sup_left.trans hh)
      ((T : Subgroup G).le_normalizer.trans (normalizer_le_control T D))
  obtain ⟨K,hK,ha,hm,_,hne⟩ := Single.exists_moving_alternatingThree_of_fixed_pair_escape S hfE
    (markedPair T D E S hS) (hD.map (markingEquiv T E S hS).symm)
    (marked_control_ne_top T D E S hS hout)
    ((Theory.GroupTheory.primeRank_le_of_injective 3 E.subtype E.subtype_injective).trans hrank)
    inferInstance hab
  exact ⟨K.map E.subtype,moving_cubic_from_normal_baumann T E S hS U hW K hK ha hm hne⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
