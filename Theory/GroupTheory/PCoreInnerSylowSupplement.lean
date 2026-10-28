module
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PCoreCentralizingSupplement
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# Inner Sylow supplements with arbitrary central quotients

Let a two-subgroup R normalize a finite group J and contain a Sylow of J.
If R acts innerly on J/O₂(J), then R lies in J O₂(JR). The inner image of
the contained Sylow is Sylow in the inner automorphism group. Thus every
R-action has a representative in that Sylow. The remaining element lies
in the two-subgroup of the normal action kernel. Core-centralizer
inheritance absorbs it in O₂(JR), allowing the original quotient center.

The actual SU₃ enlargement in DGS, Groups and Graphs (1985), 6.1,
pp.118--119, uses this lemma with its full cubic scalar center retained.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] (J R : Subgroup G)

/-- A two-group supplement containing a Sylow of J and acting innerly on
J/O₂(J) is absorbed by J and the two-core, even when that quotient has center. -/
theorem le_sup_pCoreIn_of_inner_core_action [Finite (J ⊔ R : Subgroup G)]
    (hn : R ≤ normalizer (J : Set G)) (hp : IsPGroup 2 R)
    (T : Sylow 2 J) (hTR : (T : Subgroup J).map J.subtype ≤ R)
    (hi : ∀ r : R, pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (J ⧸ pCore 2 J)) :
    R ≤ J ⊔ (J ⊔ R : Subgroup G).pCoreIn 2 := by
  let M := J ⊔ R
  let : Finite J := Finite.of_injective (inclusion (show J ≤ M from le_sup_left)) (inclusion_injective _)
  let a := pCoreJoinAction 2 hn
  let f := a.comp (inclusion (show J ≤ M from le_sup_left))
  let ar := a.comp (inclusion (show R ≤ M from le_sup_right))
  have hrange (r : R) : ar r ∈ f.range := by
    obtain ⟨z,hz⟩ := hi r
    obtain ⟨j,hj⟩ := QuotientGroup.mk'_surjective (pCore 2 J) z
    refine ⟨j,?_⟩
    change pCoreJoinAction 2 hn (inclusion le_sup_left j) = ar r
    rw [pCoreJoinAction_on_component,hj]
    exact hz
  let ar' := ar.codRestrict f.range hrange
  let U := T.mapSurjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
  have hU : (U : Subgroup f.range) ≤ ar'.range := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := hx
    let r : R := ⟨t,hTR (mem_map_of_mem J.subtype ht)⟩
    exact ⟨r,Subtype.ext rfl⟩
  have hmax : ar'.range = (U : Subgroup f.range) :=
    U.is_maximal' (hp.of_surjective ar'.rangeRestrict ar'.rangeRestrict_surjective) hU
  have hlift (r : R) : ∃ t : J, t ∈ T ∧ f t = ar r := by
    have hh : ar' r ∈ (U : Subgroup f.range) := hmax ▸ (show ar' r ∈ ar'.range from ⟨r,rfl⟩)
    obtain ⟨t,ht,he⟩ := hh
    exact ⟨t,ht,congrArg Subtype.val he⟩
  let N := J.subgroupOf M
  let C := a.ker
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer (show J ≤ M from le_sup_left)).mpr
    (sup_le J.le_normalizer hn)
  have hgen : N ⊔ R.subgroupOf M = ⊤ := by
    rw [←subgroupOf_sup (show J ≤ M from le_sup_left) (show R ≤ M from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (M ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (R.subgroupOf M) hp.comap_subtype hgen
  have hcomm : ⁅C,N⁆ ≤ N.pCoreIn 2 := by
    apply commutator_le.mpr
    intro c hc y hy
    let j : J := ⟨y,hy⟩
    let q := QuotientGroup.mk' (pCore 2 J)
    have he := DFunLike.congr_fun (show a c = 1 from hc) (q j)
    rw [pCoreJoinAction_mk] at he
    have hk : J.normalizerMonoidHom
        (inclusion (sup_le J.le_normalizer hn) c) j * j⁻¹ ∈ pCore 2 J := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q _ = 1
      rw [map_mul,map_inv]
      change _ * (q j)⁻¹ = 1
      rw [he]
      exact mul_inv_cancel _
    have hm := mem_map_of_mem (inclusion (show J ≤ M from le_sup_left)) hk
    have heq : (pCore 2 J).map (inclusion (show J ≤ M from le_sup_left)) = N.pCoreIn 2 := by
      apply map_injective M.subtype_injective
      rw [map_map]
      change (pCore 2 J).map J.subtype = _
      rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
        2 M.subtype M.subtype_injective, map_subgroupOf_eq_of_le (show J ≤ M from le_sup_left)]
      rfl
    rw [heq] at hm
    exact hm
  have hker : (R.subgroupOf M) ⊓ C ≤ pCore 2 M :=
    twoGroup_le_pCore_of_normal_core_commutator N C _ hquot hcomm
      (hp.comap_subtype.to_le inf_le_left) inf_le_right
  intro r hr
  obtain ⟨t,ht,he⟩ := hlift ⟨r,hr⟩
  let c : M := (inclusion le_sup_left t)⁻¹ * inclusion le_sup_right (⟨r,hr⟩ : R)
  have hc : c ∈ pCore 2 M := by
    apply hker
    refine ⟨R.mul_mem (R.inv_mem (hTR (mem_map_of_mem J.subtype ht))) hr,?_⟩
    change a c = 1
    change a ((inclusion le_sup_left t)⁻¹ * inclusion le_sup_right (⟨r,hr⟩ : R)) = 1
    rw [map_mul,map_inv]
    change (f t)⁻¹ * ar ⟨r,hr⟩ = 1
    rw [he,inv_mul_cancel]
  have hh := (J ⊔ M.pCoreIn 2).mul_mem
    ((le_sup_left : J ≤ J ⊔ M.pCoreIn 2) t.property)
    ((le_sup_right : M.pCoreIn 2 ≤ J ⊔ M.pCoreIn 2) (mem_map_of_mem M.subtype hc))
  change (t:G) * ((t:G)⁻¹ * r) ∈ J ⊔ M.pCoreIn 2 at hh
  simpa only [mul_inv_cancel_left] using hh
end Subgroup
