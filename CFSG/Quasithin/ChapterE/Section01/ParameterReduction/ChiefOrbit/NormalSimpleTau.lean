module

public import Theory.GroupTheory.SylowSubnormalIntersection
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.TauMembers

/-!
# Normal simple locals with a two-group supplement

Conjugation identifies the two-core quotient of HU with an automorphism
subgroup of the simple normal factor H. An actor which does not centralize H
survives the radical, and the automorphism two-rank bounds its quotient rank.
The radical, layer, residual, and Sylow intersection then give the literal E2
member. This is the normalized-factor branch of the paired E.1.11 argument.

Source: Aschbacher–Smith E.1.2 and E.1.11, printed pp.210 and 212–214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit.NormalSimpleTau
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_rank_of_normalized_simple (H U : Subgroup G)
    (hU : IsPGroup 2 U) (hn : U ≤ normalizer H)
    (e : (H ⧸ pCore 2 H) ≃* H)
    (hzH : center H = ⊥)
    {f : ℕ} (hr : primeRank 2 (MulAut H) ≤ f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAJ : A ≤ H ⊔ U)
    (hR : solvableRadical (H ⊔ U : Subgroup G) = pCore 2 (H ⊔ U : Subgroup G)) :
    Group.rank ((A.subgroupOf (H ⊔ U)).map
      (QuotientGroup.mk' (solvableRadical (H ⊔ U : Subgroup G)))) ≤ f := by
  have hz : center (H ⧸ pCore 2 H) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    have h := (Subgroup.centerCongr e ⟨x,hx⟩).property
    change e x ∈ center H at h
    rw [hzH] at h
    simpa only [mem_bot, map_one] using h
  let er := (QuotientGroup.quotientMulEquivOfEq hR).trans
    (pCoreJoinQuotientEquivRange 2 hn hU hz)
  let ι := (MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 hn).range.subtype.comp er.toMonoidHom)
  have hi : Function.Injective ι :=
    (MulAut.congr e).injective.comp (Subtype.val_injective.comp er.injective)
  let a := (A.subgroupOf (H ⊔ U)).map
    (QuotientGroup.mk' (solvableRadical (H ⊔ U : Subgroup G)))
  let := hA
  let : IsElementaryAbelian 2 (A.subgroupOf (H ⊔ U)) := IsElementaryAbelian.subgroupOf hAJ
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (a.map ι) := IsElementaryAbelian.map _
  calc
    Group.rank a = Group.rank (a.map ι) :=
      Group.rank_congr (a.equivMapOfInjective ι hi)
    _ ≤ primeRank 2 (MulAut H) :=
      (a.map ι).rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 _)
    _ ≤ f := hr

/-- A noncentral elementary actor gives the actual E-member. -/
theorem isEMemberAt_of_normalized_simple
    (T : Sylow 2 G) (H U : Subgroup G) [Group.IsPerfect H] [IsSimpleGroup H]
    (hUT : U ≤ (T : Subgroup G)) (hn : U ≤ normalizer H)
    {f : ℕ} (hr : primeRank 2 (MulAut H) ≤ f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAJ : A ≤ H ⊔ U)
    (htau : tau (T : Subgroup G) A ≤ H ⊔ U)
    (hSyl : ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H)
    (hAC : ¬ A ≤ centralizer (H : Set G)) :
    IsEMemberAt f (T : Subgroup G) A (H ⊔ U) := by
  have hcore : pCore 2 H = ⊥ := by
    rcases (inferInstance : (pCore 2 H).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hp : IsPGroup 2 H := by
        have ht : IsPGroup 2 (⊤ : Subgroup H) := h ▸ pCore_isPGroup
        exact ht.of_equiv topEquiv
      let : Group.IsNilpotent H := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable H inferInstance).elim
  have hzH : center H = ⊥ := by
    rcases (inferInstance : (center H).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative H (center_eq_top_iff.mp h)).elim
  let e : (H ⧸ pCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  have hne : ¬ A.subgroupOf (H ⊔ U) ≤ pCore 2 (H ⊔ U : Subgroup G) := by
    intro h
    apply hAC
    intro a ha
    have hk := pCore_le_pCoreJoinAction_kernel 2 hn (h (show
      (⟨a,hAJ ha⟩ : (H ⊔ U : Subgroup G)) ∈ A.subgroupOf (H ⊔ U) from ha))
    apply mem_centralizer_iff.mpr
    intro x hx
    have hxq := DFunLike.congr_fun (show pCoreJoinAction 2 hn ⟨a,hAJ ha⟩ = 1 from hk)
      (QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩)
    rw [pCoreJoinAction_mk] at hxq
    have hinj : Function.Injective (QuotientGroup.mk' (pCore 2 H)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hcore])
    have hval := congrArg Subtype.val (hinj hxq)
    change a * x * a⁻¹ = x at hval
    exact (mul_inv_eq_iff_eq_mul.mp hval).symm
  let J := H ⊔ U
  let D := H.subgroupOf J
  let eD : D ≃* H := subgroupOfEquivOfLe le_sup_left
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le H.le_normalizer hn)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := eD.symm.toMonoidHom) eD.symm.surjective
  let eqD := QuotientGroup.congr (pCore 2 D) (pCore 2 H) eD (pCore_map_iso 2 eD)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := eqD.isSimpleGroup
  have hRD : solvableRadical D = pCore 2 D := radical_eq_core_of_perfect_simple_core_quotient
  let erD := QuotientGroup.quotientMulEquivOfEq hRD
  let : IsSimpleGroup (D ⧸ solvableRadical D) := erD.isSimpleGroup
  have hgen : D ⊔ U.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show H ≤ J from le_sup_left) (show U ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hU : IsPGroup 2 U := T.isPGroup'.to_le hUT
  have hq : IsPGroup 2 (J ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D (U.subgroupOf J) hU.comap_subtype hgen
  have hR : solvableRadical J = pCore 2 J :=
    radical_eq_core_of_normal_two_quotient D (hRD ▸ pCore_isPGroup) hq
  let Q := J ⧸ solvableRadical J
  let q := QuotientGroup.mk' (solvableRadical J)
  let C := D.map q
  let : C.Normal := (inferInstance : D.Normal).map q (QuotientGroup.mk'_surjective _)
  let ec := normalRadicalQuotientEquivImage D
  let : IsSimpleGroup C := ec.symm.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective D)
  have hz : center C = ⊥ := by
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple C := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hqC : IsPGroup 2 (Q ⧸ C) := normal_radical_image_two_quotient D hq
  have hc : IsComponent Q C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  have hl := (SimpleSocle.layer_residuals C hqC).1
  have hcentral := centralizer_eq_bot_of_simple_two_quotient C
    (Group.IsPerfect.not_isMulCommutative C) hqC
    (SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2)
  have ha : (A.subgroupOf J).map q ≠ ⊥ := by
    intro he
    apply hne
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    simpa only [q, QuotientGroup.ker_mk', hR] using hh
  have hclosed : IsTwoClosed (solvableRadical J) := by
    have hp : IsPGroup 2 (solvableRadical J) := hR ▸ pCore_isPGroup
    obtain ⟨S,hS⟩ := (hp.to_subgroup ⊤).exists_le_sylow
    have he : (S : Subgroup (solvableRadical J)) = ⊤ := top_unique hS
    exact ⟨S, he ▸ inferInstance⟩
  apply ValuesEvenClassical.RankOneUpper.isEMemberAt_of_normal_quotient_component
    (T : Subgroup G) A J hA hAT hAJ htau
    (T.exists_subgroupOf_sup_of_normalized H U hUT hn hSyl) hclosed _
    (pResidual_eq_solvableResidual_of_perfect_sup_twoGroup H U hU hn) C hc hl
    (SimpleSocle.commutator_eq C hcentral _ ha)
    (quotient_rank_of_normalized_simple H U hU hn e hzH hr A hA hAJ hR)
  rw [hl]
  exact ⟨inferInstance,hqC⟩


/-- Literal normalized-component application, with its prescribed Sylow. -/
theorem component_tau_join_member (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (htau : tau (T : Subgroup G) A ≤ normalizer (K : Set G))
    (hne : ¬ A ≤ centralizer (K : Set G)) :
    IsEMemberAt f (T : Subgroup G) A (K ⊔ tau (T : Subgroup G) A) := by
  let : IsQuasisimple K := hK.2
  exact isEMemberAt_of_normalized_simple T K (tau (T : Subgroup G) A)
    (tau_le _ _) htau hr A inferInstance hAT
    ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right) le_sup_right
    (T.exists_subgroupOf_eq_of_subnormal K hK.1) hne

end CFSG.Quasithin.ChapterE.ChiefOrbit.NormalSimpleTau
