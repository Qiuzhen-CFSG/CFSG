module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# The literal prefix of original 15.1.20

The source component selected in 15.1.19 is retained as a subgroup of the
original ambient group.  This file records the parts of 15.1.20 which are
independent of the later C.2.7 marked catalogue: the local-family definition
already makes `S ∩ L` Sylow in `L`, source 14.1.6 excludes `L ≤ M` whenever
`L` is also an original local component, and the ordinary-component center is
`O₂(L)` under the source odd-core hypothesis.

The remaining Borel, parabolic, fixed-vector and centralizer alternatives of
15.1.20 use C.2.7(3), while the current C.2.7 source extraction deliberately
ends at its kernel/offender and B.5 moved-section conclusions.  No such
alternative is asserted here without that missing producer.

Source: Aschbacher--Smith 15.1.20, printed pp.1094--1097, together with
14.1.6 and the index-two local-family argument of Chapter 1, Section 1.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1
namespace ComponentModels

universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- A selected C-component of an actual two-local overgroup enters the
literal local family with the same ambient subgroup and Sylow map. -/
theorem source20_mem_L_of_cComponent {S H L : Subgroup G}
    (hH : H ∈ Chapter1.H G)
    (hS : IsSylowIn 2 S H)
    (hLH : L ≤ H)
    (hLc : (L.subgroupOf H).IsCComponent) :
    L ∈ Chapter1.L G S := by
  exact Chapter1.mem_L_of_cComponent hH hS hLH hLc

/-- The literal `S_L = S ∩ L` is Sylow in every member of `L(G,S)`. -/
theorem source20_sylow_intersection {S L : Subgroup G}
    (hL : L ∈ Chapter1.L G S) :
    IsSylowIn 2 (S ⊓ L) L := by
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hL.2.1 le_sup_left hL.1.subnormal

omit [Finite G] in
/--
An outside component also has normalizer outside the selected maximal local
subgroup.  This is the elementary normalizer consequence used before the
Baumann and minimal-parabolic steps in 15.1.20.
-/
theorem source20_normalizer_not_le_M {M L : Subgroup G}
    (hLout : ¬ L ≤ M) :
    ¬ normalizer (L : Set G) ≤ M := by
  intro hNM
  apply hLout
  exact le_normalizer.trans hNM

/--
For an ordinary component, trivial ambient `O_{2'}` descends to the component
and identifies its center with `O₂(L)`.  The final conjunct records the source
statement that this center is a 2-group.
-/
theorem source20_component_center_eq_pCore
    {G1 : Type u} [Group G1] [Finite G1] {L : Subgroup G1}
    (hL : IsComponent G1 L)
    (hodd : pPrimeCore 2 G1 = ⊥) :
    center L = pCore 2 L ∧ IsPGroup 2 (center L) := by
  let _ : IsQuasisimple L := hL.2
  have hoddL : pPrimeCore 2 L = ⊥ :=
    Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd L hL.1
  have hcenter : center L = pCore 2 L :=
    IsQuasisimple.center_eq_pCore hoddL
  refine ⟨hcenter, ?_⟩
  rw [hcenter]
  exact pCore_isPGroup

end ComponentModels
end CFSG.Quasithin.Chapter15.Section01
