module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# The ordinary Hall--Janko centralizer

The exhaustive Sylow-overgroup calculation puts a proper overgroup in the
two marked locals. The order-1920 involution centralizer cannot lie in the
order-1152 second local, so it is maximal. The whole Sylow center calculation
and Sylow conjugacy transport this to every two-central involution.

Source: Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097. The unchanged
ATLAS J2G1-p100B0 carrier, data attribution and checked local calculations
are retained in the imported modules.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.LeechRelated.J2.OrdinaryLocal
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.PairNormalizer

theorem center_eq_bot : center Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply NormalizerAction.inner_conj_injective
  apply MulEquiv.ext
  intro y
  change x * y * x⁻¹ = 1 * y * 1⁻¹
  rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  simp

private theorem marked_centralizer_isCoatom : IsCoatom l₁ := by
  have hne : l₁ ≠ ⊤ := by
    intro he
    have hh := FirstParabolic.card_l₁
    rw [he,card_top,FirstParabolic.card_carrier] at hh
    omega
  refine ⟨hne, ?_⟩
  intro U hU
  by_contra hn
  rcases SylowOvergroups.proper_overgroup_le U (SecondParabolic.s_le_l₁.trans hU.le) hn with hc | hp
  · exact hU.ne (le_antisymm hU.le hc)
  · have hd := card_dvd_of_le (hU.le.trans hp)
    rw [FirstParabolic.card_l₁,card_p₂] at hd
    norm_num at hd

theorem twoCentral_centralizer_isCoatom (t : Carrier) (ht : orderOf t = 2)
    (hc : TwoCentral t) : IsCoatom (centralizer ({t} : Set Carrier)) := by
  classical
  obtain ⟨P,hP,hPc⟩ := hc
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier P (SecondParabolic.sylow FirstParabolic.card_l₁)
  let e := MulAut.conj g
  have hPs : ((g • P : Sylow 2 Carrier) : Subgroup Carrier) = s :=
    congrArg (fun Q : Sylow 2 Carrier => (Q : Subgroup Carrier)) hg
  let eP : P ≃* s := (P.equivSMul g).trans (MulEquiv.subgroupCongr hPs)
  have hzt : e t ∈ (center s).map s.subtype := by
    refine ⟨eP ⟨t,hP⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := eP.surjective x
    rw [← eP.map_mul, ← eP.map_mul, mem_center_iff.mp hPc]
  rw [SecondParabolic.center_s] at hzt
  have hz : e t = GeneratorPair.FirstFusion.t := by
    have hcases : e t = 1 ∨ e t = GeneratorPair.FirstFusion.t := by
      rw [mem_zpowers_iff_mem_range_orderOf, SecondParabolic.central_involution_order] at hzt
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hzt
      have hlt := Finset.mem_range.mp hk
      interval_cases k <;> simp_all
    rcases hcases with h1 | he
    · have ht1 := e.map_eq_one_iff.mp h1
      rw [ht1,orderOf_one] at ht
      omega
    · exact he
  apply (e.mapSubgroup.isCoatom_iff _).mp
  have he : (centralizer ({t} : Set Carrier)).map e.toMonoidHom = l₁ := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff]
    change e.symm x * t = t * e.symm x ↔ x ∈ centralizer ({GeneratorPair.FirstFusion.t} : Set Carrier)
    rw [mem_centralizer_singleton_iff]
    rw [← hz]
    constructor
    · intro hh
      have he := congrArg e hh
      simpa only [map_mul,e.apply_symm_apply] using he
    · intro hh
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hh
  change IsCoatom ((centralizer ({t} : Set Carrier)).map e.toMonoidHom)
  rw [he]
  exact marked_centralizer_isCoatom
end Sporadic.LeechRelated.J2.OrdinaryLocal
