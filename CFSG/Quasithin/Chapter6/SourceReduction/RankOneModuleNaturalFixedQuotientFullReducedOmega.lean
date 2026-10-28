module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFullEnlargement
public import Theory.GroupTheory.ReducedNormal.SimpleCoreOmega

/-!
# The full original reduced subgroup is the two-core omega-center

The normal component L in LT has centerless quasisimple two-core quotient.
Its noncentral reduced subgroup lies inside Ω₁Z(O₂(LT)), so that omega-center
is noncentral as well. The actual normal-kernel theorem makes it reduced,
and maximality identifies it with R₂(LT).

This supplies the enlargement identity used in the Hermitian hyperplane
contradiction in Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The literal full reduced enlargement is the omega-center of the
actual two-core of LT. No module model or omega identity is assumed. -/
theorem reduced_enlargement_eq_omega_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n) :
    reducedSubgroup (L ⊔ (T : Subgroup G)) =
      omegaOneCenterAmbient ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes_L)
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)
  have hzL : center (L ⧸ pCore 2 L) = ⊥ := by
    obtain ⟨F,_,_,hF,⟨eF⟩⟩ := h.quotient_model
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    apply bot_unique
    intro x hx
    exact eF.map_eq_one_iff.mp
      (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot.le ((centerCongr eF) ⟨x,hx⟩).property)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.local_mem.1.prop
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : IsQuasisimple (L ⧸ pCore 2 L) := by
    refine ⟨?_⟩
    apply (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hzL).trans QuotientGroup.quotientBot)).mpr
    obtain ⟨F,_,_,hF,⟨eF⟩⟩ := h.quotient_model
    apply (MulEquiv.isSimpleGroup_congr eF).mpr
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    rw [hF]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) h.n_gt_one).trans' (by decide)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    apply e.map_eq_one_iff.mp
    exact hzL.le (MulEquivClass.apply_mem_center e hb)
  have hp : IsPPerfect 2 B := h.local_mem.2.2.1.of_surjective
    eb.symm.toMonoidHom eb.symm.surjective
  have hB : B.IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : B.Normal).isSubnormal hp
  have hsup : B ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have hRO : reducedTwoSubgroup J ≤ omegaOneCenterAmbient (pCore 2 J) := by
    let : IsElementaryAbelian 2 (reducedTwoSubgroup J) :=
      isPReduced_reducedPSubgroup.elementary
    intro r hr
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨reducedPSubgroup_le_pCore 2 J hr,
        elemPow_eq_one_of_isElementaryAbelian r hr,
        reducedPSubgroup_le_centralizer_pCore 2 J hr⟩
  have hmove : ⁅omegaOneCenterAmbient (pCore 2 J),B⁆ ≠ ⊥ := by
    intro he
    have hm : ⁅reducedTwoSubgroup J,B⁆ = ⊥ :=
      bot_unique ((commutator_mono hRO le_rfl).trans_eq he)
    have hh := congrArg (map J.subtype) hm
    rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
      Subgroup.map_bot] at hh
    apply h.reduced_enlargement_nontrivial
    change ⁅reducedSubgroup J,L⁆ = ⊥
    rwa [reducedSubgroup_eq_map]
  have he := (omegaCenter_reduced_of_simple_component B S hB hz
    T.isPGroup'.comap_subtype hsup hmove).2
  rw [reducedSubgroup_eq_map,←he]
  exact (omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective
    (pCore 2 J)).symm

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
