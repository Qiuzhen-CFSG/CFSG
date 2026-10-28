module
public import Theory.GroupTheory.PCoreCommutator
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure

/-!
# The original star commutator in the orthogonal residual source

The module centralizer is normal in M and lies in M ∩ Mc. Its commutator
with the latter group's two-core therefore lies in O₂(M). Normal closure
propagates this to the actual Y = O²(⟨O₂(M ∩ Mc)^M⟩). Passing through the
literal quotient M/O₂(M) proves the first clause of 14.1.17(3) used in
15.3.7, with no star-centralization input.

Source: Aschbacher--Smith 14.1.17(3) and 15.3.7, printed pp.980,1122.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G]

/-- The original module centralizer commutes with the actual intersection core modulo O₂(M). -/
theorem source_intersection_core_commutator (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ⁅d.actor.ker, ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M := by
  let H := (M ⊓ Mc).subgroupOf M
  have hCH : d.actor.ker ≤ H := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (V : Set G) := by
      rw [d.ker_actor] at hx
      exact hx
    exact ⟨x.property,hC ⟨x.property,hxC⟩⟩
  have he : H.pCoreIn 2 = ((M ⊓ Mc).pCoreIn 2).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_pCoreIn_of_injective 2 H M.subtype M.subtype_injective,
      show H.map M.subtype = M ⊓ Mc from map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
  exact he ▸ commutator_pCoreIn_le_of_normal (p := 2) d.actor.ker H hCH

/-- The literal first clause of 14.1.17(3), including the source normal-closure residual. -/
theorem source_star_centralizes (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) ≤
      centralizer ((ThreeAlternatives.star M (residualY M Mc) ⊔
        ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) :
          Subgroup (ThreeAlternatives.StarGroup M)) : Set (ThreeAlternatives.StarGroup M)) := by
  have hcomm := source_intersection_core_commutator M Mc V d hC
  have hcommY := residualY_commutator_le M Mc d.actor.ker (pCore 2 M) hcomm
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = d.actor.ker := by
    rw [d.ker_actor]
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.property,h⟩⟩
  have lift (X : Subgroup M) (hX : ⁅d.actor.ker,X⁆ ≤ pCore 2 M) :
      d.actor.ker.map (QuotientGroup.mk' (pCore 2 M)) ≤
        centralizer (X.map (QuotientGroup.mk' (pCore 2 M)) : Set (ThreeAlternatives.StarGroup M)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hX
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply le_centralizer_iff.mpr
    simpa only [ThreeAlternatives.star,hCeq] using lift _ hcommY
  · apply le_centralizer_iff.mpr
    simpa only [ThreeAlternatives.star,hCeq] using lift _ hcomm

end CFSG.Quasithin.Chapter15.Section03
