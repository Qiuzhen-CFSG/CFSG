module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.Components
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
/-!
# Component existence from the global Case-I controls

The relative normalizer equality N_{G₁}(Q₁)=M_Z identifies the intrinsic
two-core of that normalizer with Q₁, proving radicality without an extra
hypothesis. Characteristic-normalizer generation restricts along the actual
inclusion G₁→G. Finally C_G(Z₁) lies in N_G(Z₁), so the global simple QTKE
hypothesis supplies its SQTK property whenever Z₁ is a nontrivial two-group.
The last theorem applies these three deductions to the actual component
extraction, retaining only the earlier source odd-core and residual-normalizer
bounds and the original escape of C_M(Z₁).

Source: Aschbacher--Smith 15.1.18(2),(5),(7) and 15.1.19(1),(6),
printed pp.1092--1093. The marked subgroup and all ambient inclusions are literal.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The literal local core is radical in the centralizer under source normalizer control. -/
theorem caseI_intrinsic_core_radical (H M : Subgroup G) (hMH : M ≤ H)
    (hne : M.pCoreIn 2 ≠ ⊥)
    (hn : H ⊓ normalizer (M.pCoreIn 2 : Set G) = M) :
    IsPRadical 2 ((M.pCoreIn 2).subgroupOf H) := by
  have hQH : M.pCoreIn 2 ≤ H := (pCoreIn_le 2 M).trans hMH
  have hnorm : normalizer ((M.pCoreIn 2).subgroupOf H : Set H) = M.subgroupOf H := by
    rw [← subgroupOf_normalizer_eq hQH]
    ext x
    change (x : G) ∈ normalizer (M.pCoreIn 2 : Set G) ↔ (x : G) ∈ M
    constructor
    · intro hx
      exact hn.le ⟨x.property,hx⟩
    · intro hx
      exact (show (x : G) ∈ H ⊓ normalizer (M.pCoreIn 2 : Set G) from hn.symm ▸ hx).2
  refine ⟨?_,?_⟩
  · intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hQH,Subgroup.map_bot] at hh
    exact hne hh
  · change (normalizer ((M.pCoreIn 2).subgroupOf H : Set H)).pCoreIn 2 = _
    rw [hnorm,pCoreIn_subgroupOf 2 M H hMH]

omit [Finite G] in
/-- Global characteristic-normalizer control restricts to the original intersection. -/
theorem caseI_intrinsic_characteristic_control (H Mc Q : Subgroup G)
    (hQH : Q ≤ H) (hc : Q.characteristicNormalizerClosure ≤ Mc) :
    (Q.subgroupOf H).characteristicNormalizerClosure ≤ (H ⊓ Mc).subgroupOf H := by
  intro x hx
  exact ⟨x.property,characteristicNormalizerClosure_subgroupOf_le hQH hc hx⟩

/-- A nontrivial marked two-subgroup makes its centralizer SQTK in the global source group. -/
theorem caseI_centralizer_sqtk {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (Z1 : Subgroup G) (hne : Z1 ≠ ⊥) (hp : IsPGroup 2 Z1) :
    IsSQTK κ (centralizer (Z1 : Set G)) := by
  have hs := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (Z1 : Set G)) from ⟨Z1,hne,hp,rfl⟩)
  have hn : centralizer (Z1 : Set G) ≤ normalizer (Z1 : Set G) :=
    Subgroup.centralizer_le_normalizer _
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hn) (inclusion_injective hn),
    hs.isKGroup.of_injective (inclusion hn) (inclusion_injective hn)⟩

/-- The actual source component is constructed from the global source control. -/
theorem source_caseI_15_1_19_6_of_global_control
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) (M Mc Z1 : Subgroup G)
    (hZne : Z1 ≠ ⊥) (hZtwo : IsPGroup 2 Z1)
    (hQne : (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hn : centralizer (Z1 : Set G) ⊓
      normalizer ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 : Set G) =
        centralizer (Z1 : Set G) ⊓ Mc)
    (ho : pPrimeCore 2 (centralizer (Z1 : Set G)) = ⊥)
    (hescape : ¬ M ⊓ centralizer (Z1 : Set G) ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hres : centralizer (Z1 : Set G) ⊓ normalizer
      ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
        (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤
          centralizer (Z1 : Set G) ⊓ Mc) :
    ∃ L : Subgroup G, L ≤ centralizer (Z1 : Set G) ∧
      (L.subgroupOf (centralizer (Z1 : Set G))).IsCComponent ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧ ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc := by
  apply source_caseI_15_1_19_6 M Mc Z1 (caseI_centralizer_sqtk hG Z1 hZne hZtwo)
  · exact caseI_intrinsic_core_radical _ _ inf_le_left hQne hn
  · exact caseI_intrinsic_characteristic_control _ _ _
      ((pCoreIn_le 2 _).trans inf_le_left) hcontrol
  · exact ho
  · exact hescape
  · exact hres
end CFSG.Quasithin.Chapter15.Section01
