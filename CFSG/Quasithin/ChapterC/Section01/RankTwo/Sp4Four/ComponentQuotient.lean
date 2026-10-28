module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ThompsonOffender
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# The original component inside the MS quotient

For H=KR with K a C-component and R a two-group, the component is the
actual two-residual and hence normal. Its intrinsic two-core quotient maps
isomorphically to its image in H/O₂(H). When this quotient is simple,
its centralizer in H/O₂(H) is trivial: that centralizer embeds in the
two-group quotient and is killed by O₂(H/O₂(H))=1.

This supplies the ambient-action hypotheses of the FF module classifier,
while preserving the original component and literal quotient map.
Source: the component reduction in MS93 (3.2), and AS C.1.31--32.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

private theorem perfect_twoPerfect {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hn hp
  let := hn
  by_contra hne
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (K ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent

/-- The actual component--two-group product identifies its residual. -/
theorem component_eq_residual (K R : Subgroup H) (hK : K.IsCComponent)
    (hp : IsPGroup 2 R)
    (hprod : ∀ h : H, ∃ k ∈ K, ∃ r ∈ R, k*r=h) : pResidual 2 H = K := by
  let := hK.perfect
  exact pResidual_eq_of_subnormal_product K R hK.subnormal perfect_twoPerfect hp hprod

/-- All ambient simple-component hypotheses for FF recognition, on the
literal image in the original two-core quotient. -/
theorem component_image_structure (K R : Subgroup H) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R)
    (hprod : ∀ h : H, ∃ k ∈ K, ∃ r ∈ R, k*r=h) :
    let B := K.map (QuotientGroup.mk' (pCore 2 H))
    K.Normal ∧ B.Normal ∧ IsSimpleGroup B ∧ IsQuasisimple B ∧
      centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  have hres := component_eq_residual K R hK hp hprod
  let hn : K.Normal := by rw [← hres]; infer_instance
  let hbn : B.Normal := Normal.map hn q (QuotientGroup.mk'_surjective _)
  let e := cComponentTwoCoreQuotientEquiv hK
  let hs : IsSimpleGroup B := e.symm.isSimpleGroup
  let := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective K)
  have ha : ¬ IsMulCommutative B := by
    intro hab
    let := hab
    exact Group.IsPerfect.not_isSolvable B inferInstance
  have hz : center B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center B) inferInstance with h | h
    · exact h
    · exact (ha (center_eq_top_iff.mp h)).elim
  let hq : IsQuasisimple B := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hgen : K ⊔ R = ⊤ := by
    apply top_unique
    intro h _
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod h
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (R.map q) (hp.map q) (by
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  exact ⟨hn,hbn,hs,hq,centralizer_eq_bot_of_simple_two_quotient B ha hquot
    (pCore_quotient_pCore_eq_bot 2)⟩

end CFSG.Quasithin.ChapterC.MSCentralOrbit
