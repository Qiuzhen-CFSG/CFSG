module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.Projections
public import Theory.GroupTheory.ComponentSaturatedRadical
public import Theory.SpecificGroups.PSL3Three.LocalNormalizers
public import Theory.Mathieu.M11.Properties.LocalNormalizers

/-!
# Literal radical normalizers in the small non-Bender components

The original saturated pair gives the exact radical equation for each
component intersection, even if H_U permutes the components. In the
PSL3(3) and M11 cases, the model theorem puts its actual normalizer in He.
The normalizer is embedded through the original component and H inclusions.

Source: Aschbacher--Smith 2.5.3(4), printed p.553. The earlier 2.5.2 model
recognition and inner noncentral projection remain with their source
producer; the radical identity and local characteristic-two condition
proved here are no longer additional inputs.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- Source saturation makes the actual component intersection radical. -/
theorem saturated_component_radical
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D) :
    let R := D ⊓ (twoCore HU).subgroupOf H
    (D ⊓ normalizer (R : Set H)).pCoreIn 2 = R := by
  apply hD.pCoreIn_normalizer_intersection_of_saturation
    (A := HU.subgroupOf H) (isPGroup_pCoreIn 2 HU).comap_subtype
  · intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  · intro P hp hn x hx
    have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
      intro a ha
      exact P.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
    exact hsat _ (map_subtype_le P) (hp.map H.subtype) hna
      (mem_map_of_mem H.subtype hx)

omit [Finite G] in
/-- In either small non-Bender model, the full normalizer of any nontrivial
two-subgroup lies in the genuine local family He, under the original maps. -/
theorem small_component_normalizer_mem_He
    (D : Subgroup H)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (R : Subgroup D) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ((normalizer (R : Set D)).map D.subtype).map H.subtype ∈ Chapter1.He G := by
  have hc : centralizer (pCore 2 (normalizer (R : Set D)) :
      Set (normalizer (R : Set D))) ≤ pCore 2 (normalizer (R : Set D)) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      apply normalizer_core_selfCentralizing_of_equiv e R
      apply Matrix.PSL3Three.normalizer_twoCore_selfCentralizing _ (hp.map _)
      intro hb
      exact hne ((map_eq_bot_iff_of_injective _ e.injective).mp hb)
    · obtain ⟨e⟩ := hm
      apply normalizer_core_selfCentralizing_of_equiv e R
      apply Sporadic.Mathieu.m11_normalizer_twoCore_selfCentralizing _ (hp.map _)
      intro hb
      exact hne ((map_eq_bot_iff_of_injective _ e.injective).mp hb)
  apply Chapter1.mem_He_iff.mpr
  let e := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hc

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
