module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
/-! # The actual starred source setup for the empty-Gamma branch
The preceding component-generation and maximality source constructs the exact
MathieuSourceSetup used throughout 2.5.7–2.5.13. Its Sylow, local pair,
central mark, and component generation remain the original ambient objects.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {M:Subgroup G}
theorem exists_starred_source_setup
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T₀:Sylow 2 G) (hM:IsMaximalTwoLocal M) (hT₀M:(T₀:Subgroup G)≤M)
    (hunique:∀N:Subgroup G,IsMaximalTwoLocal N→(T₀:Subgroup G)≤N→N=M)
    (hdelta:(delta (Chapter1.He G) M).Nonempty)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅) :
    ∃H L:Subgroup G,∃S:Sylow 2 H,∃z:G,∃_c:MathieuSourceSetup H L M S z,
      H∈gammaStar (Chapter1.He G) M ∧ ¬ClassificationModels.IsBenderModel L ∧
      H=L⊔(S:Subgroup H).map H.subtype := by
  obtain ⟨H,L,S,T,z,x,hstar,d,hL,hb,hgen,_⟩:=exists_star_generated_configuration
    hG localC129Input_knownSimple T₀ hM hT₀M hunique hdelta hempty
  obtain ⟨R,hR⟩:=d.sylow_maximal
  have hTM:(T:Subgroup G)≤M:=hR ▸ map_subtype_le _
  have huniq:∀N:Subgroup G,IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M:=by
    intro N hN hTN
    have hNM:N≤M:=by
      apply core_overgroup_le_of_sylow T₀ hT₀M hunique
        (Chapter1.mem_H_of_isTwoLocal hN.1) (T.subtype hTM)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hTN
    exact le_antisymm hNM (hN.2 hM.1 hNM)
  have hSM:(S:Subgroup H).map H.subtype≤M:=d.lt.le.trans hTM
  obtain ⟨U,HU,hpair,hUS,_⟩:=exists_saturated_pair_aligned d.gamma_zero S hSM
  refine ⟨H,L,S,z,{
    T:=T
    maximal:=hM
    sylow_le:=hTM
    unique:=huniq
    gamma:=d.gamma_zero
    U:=U
    HU:=HU
    pair:=hpair
    base_le:=hUS
    component_le:=hL.1
    component:=hL.2
    sylow_lt:=d.lt
    center_le:=d.center_le
    mem_center:=d.mem_center
    involution:=d.involution },hstar,hb,hgen⟩
/-- Select all original crossing data directly from the empty-Gamma hypotheses. -/
theorem exists_starred_crossing_setup
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T₀:Sylow 2 G) (hM:IsMaximalTwoLocal M) (hT₀M:(T₀:Subgroup G)≤M)
    (hunique:∀N:Subgroup G,IsMaximalTwoLocal N→(T₀:Subgroup G)≤N→N=M)
    (hdelta:(delta (Chapter1.He G) M).Nonempty)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅) :
    ∃H L:Subgroup G,∃S:Sylow 2 H,∃z:G,∃c:MathieuSourceSetup H L M S z,
      H∈gammaStar (Chapter1.He G) M ∧ ¬ClassificationModels.IsBenderModel L ∧
      H=L⊔(S:Subgroup H).map H.subtype ∧ IsSmallRemainingComponent L ∧
      ∃t x:G,orderOf t=2 ∧ t∈twoCore H ∧
        centerIn ((S:Subgroup H).map H.subtype)=zpowers t⊔zpowers z ∧
        x∈c.T ∧ x∉(S:Subgroup H).map H.subtype ∧
        x∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
        x^2∈(S:Subgroup H).map H.subtype ∧ x⁻¹*t*x=t*z := by
  obtain ⟨H,L,S,z,c,hstar,hb,hgen⟩:=
    exists_starred_source_setup hG T₀ hM hT₀M hunique hdelta hempty
  obtain ⟨t,ht,htC,hZ,hcross⟩:=
    MathieuSourceSetup.source_crossing_involution c hG hempty hgen hb
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  exact ⟨H,L,S,z,c,hstar,hb,hgen,
    MathieuSourceSetup.small_remaining_component c hG hempty hgen hb,
    t,x,ht,htC,hZ,hxT,hxS,hxN,hx2,hcross x hxT hxN hxS⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
