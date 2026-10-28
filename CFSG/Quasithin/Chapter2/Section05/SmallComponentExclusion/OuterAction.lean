module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.InnerResidualSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearThreeEightSource
public import Theory.GroupTheory.NormalizerActionFixer
/-!
# The outer action and its actual cyclic-four fixer preimage

A noninner source Sylow action fills Aut(PSL₃(3)), since the inner subgroup
has index two. The actual component action has kernel O₂(H). The local
residual fixer is a two-group, so its preimage, normalized by S, lies in S.
Lifting its outer order-four generator gives C_H(R)=O₂(H)⟨y⟩ on the literal
source carrier and with the original conjugation action.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

omit [Finite G] in
theorem linear_three_source_action_surjective
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (e : K ≃* Matrix.PSL3Three.PSL)
    (hout : ¬ (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G)) :
    Function.Surjective (MathieuSourceSetup.componentAction c) := by
  let α := MathieuSourceSetup.componentAction c
  have hi : (MulAut.innerSubgroup K).index = 2 := by
    have hh := Matrix.PSL3Three.EightGeometry.inner_index_two
    rw [← MulAut.map_innerSubgroup_congr e,
      index_map_of_bijective (MulAut.congr e).bijective] at hh
    exact hh
  have hI : MulAut.innerSubgroup K ≤ α.range := by
    rintro _ ⟨k,rfl⟩
    refine ⟨⟨k,c.component_le k.property⟩,?_⟩
    ext a
    rfl
  obtain ⟨s,hs,hsout⟩ := Set.not_subset.mp hout
  obtain ⟨s,hs,rfl⟩ := hs
  have hsa : α s ∉ MulAut.innerSubgroup K := by
    intro hm
    let n : normalizer (K:Set G) := ⟨s,
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance) s.property⟩
    have hn : n ∈ (MulAut.conj : K →* MulAut K).range.comap K.normalizerMonoidHom := hm
    rw [normalizerMonoidHom_comap_conj_range] at hn
    exact hsout hn
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  intro a _
  by_cases ha : a ∈ MulAut.innerSubgroup K
  · exact hI ha
  · have hm : a * (α s)⁻¹ ∈ MulAut.innerSubgroup K := by
      rw [mul_mem_iff_of_index_two hi]
      simp only [inv_mem_iff,ha,hsa]
    have hh := α.range.mul_mem (hI hm) (show α s ∈ α.range from ⟨s,rfl⟩)
    simpa only [inv_mul_cancel_right] using hh
end CFSG.Quasithin.Chapter2.Section05

namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem normal_component_source_action_ker
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) :
    (MathieuSourceSetup.componentAction c).ker = (twoCore H).subgroupOf H := by
  let Y := (S : Subgroup H).map H.subtype
  have hKN : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance
  have hKY : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans hKN
  have horbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hcore := generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
  rw [horbit] at hcore
  have hCL := normal_component_centralizer_le_source_sylow c hG hempty hgen
  change (K.normalizerMonoidHom.comp (inclusion hKN)).ker = _
  rw [normalizer_action_ker_comap]
  ext x
  constructor
  · intro hx
    have hm : (x : G) ∈ Y ⊓ centralizer (K : Set G) := ⟨hCL ⟨x.property,hx⟩,hx⟩
    exact hcore ▸ hm
  · intro hx
    have hm : (x : G) ∈ Y ⊓ centralizer (K : Set G) := hcore.symm ▸ hx
    exact hm.2

theorem linear_three_residual_centralizer_le_source_sylow
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) (zK : K) (hzK : orderOf zK = 2)
    (hSN : (S : Subgroup H).map H.subtype ≤
      normalizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)) :
    H ⊓ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G) ≤
      (S : Subgroup H).map H.subtype := by
  obtain ⟨a,_,ha,_,hfix⟩ := linear_three_local_residual_fixer K e zK hzK
  change fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) = zpowers a at hfix
  have hp : IsPGroup 2 (fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K)) := by
    rw [hfix]
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers,ha]
    norm_num
  exact normalizer_action_fixer_le_sylow K H (GLTwoThreeLocal.residual zK)
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance) S
    (normal_component_centralizer_le_source_sylow c hG hempty hgen) hp hSN

theorem linear_three_outer_residual_lift
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) (zK : K) (hzK : orderOf zK = 2)
    (hout : ¬ (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G))
    (hSN : (S : Subgroup H).map H.subtype ≤
      normalizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)) :
    let α := MathieuSourceSetup.componentAction c
    ∃ y : H, y ∈ S ∧ (y : G) ∈ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G) ∧
      α y ∉ MulAut.innerSubgroup K ∧ orderOf (α y) = 4 ∧ (α y)^2 = MulAut.conj zK ∧
      H ⊓ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G) =
        twoCore H ⊔ zpowers (y : G) := by
  let α := MathieuSourceSetup.componentAction c
  obtain ⟨a,hao,ha,ha2,hfix⟩ := linear_three_local_residual_fixer K e zK hzK
  change fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) = zpowers a at hfix
  have hpre : (fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K)).comap α =
      (centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)).subgroupOf H :=
    normalizer_action_fixing_comap K H (GLTwoThreeLocal.residual zK)
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  obtain ⟨y,hy⟩ := linear_three_source_action_surjective c e hout a
  have hf : α y ∈ fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) := by
    rw [hy,hfix]
    exact mem_zpowers a
  have hyC : (y : G) ∈ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G) := by
    have hm : y ∈ (fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K)).comap α := hf
    rw [hpre] at hm
    exact hm
  have hyY := linear_three_residual_centralizer_le_source_sylow c hG hempty hgen e zK hzK hSN
    ⟨y.property,hyC⟩
  have hyS : y ∈ S := by
    obtain ⟨s,hs,he⟩ := hyY
    exact H.subtype_injective he ▸ hs
  refine ⟨y,hyS,hyC,hy ▸ hao,hy ▸ ha,hy ▸ ha2,?_⟩
  have hk := normal_component_source_action_ker c hG hempty hgen
  apply le_antisymm
  · intro v hv
    let vH : H := ⟨v,hv.1⟩
    have hvf : α vH ∈ fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) := by
      have hm : vH ∈ (centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)).subgroupOf H := hv.2
      rw [← hpre] at hm
      exact hm
    rw [hfix,mem_zpowers_iff] at hvf
    obtain ⟨n,hn⟩ := hvf
    have hker : vH * y^(-n) ∈ α.ker := by
      change α (vH * y^(-n)) = 1
      rw [map_mul,map_zpow,hy,← hn,zpow_neg,mul_inv_cancel]
    have hvcore : v * (y : G)^(-n) ∈ twoCore H := by
      rw [hk] at hker
      exact hker
    have hm := (twoCore H ⊔ zpowers (y : G)).mul_mem (mem_sup_left hvcore)
      (mem_sup_right (zpow_mem_zpowers (y : G) n))
    simpa only [zpow_neg,inv_mul_cancel_right] using hm
  · apply sup_le
    · intro v hv
      have vh : v ∈ H := pCoreIn_le 2 H hv
      have hker : (⟨v,vh⟩ : H) ∈ α.ker := by rw [hk]; exact hv
      have hf : α ⟨v,vh⟩ ∈ fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) := by
        rw [show α ⟨v,vh⟩ = 1 from hker]
        exact one_mem _
      have hm : (⟨v,vh⟩ : H) ∈ (fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K)).comap α := hf
      rw [hpre] at hm
      exact ⟨vh,hm⟩
    · exact zpowers_le.mpr ⟨y.property,hyC⟩
end CFSG.Quasithin.Chapter2.Section05
