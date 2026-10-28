module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsRankTwo
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsRee
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsBinary

/-!
# The characteristic-two moved-component obstruction

All eight rank-two Theorem C constructors, PSL₄(2), PSL₅(2), and A₈ have
at most one C-component in every overgroup of a full Sylow two-subgroup.
The calculations use the actual parabolic Levi quotients and genuine model
isomorphisms. Applying uniqueness to the original overcomponent's radical
quotient contradicts the moved normalized remaining-simple obstruction.
This supplies the even-family input to the source 1.2.8 maximality assembly.

Source: Aschbacher--Smith A.3.12, printed pp.47--48, and 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

/-- Every constructor of the source rank-two list has unique C-components
in every overgroup of a full Sylow two-subgroup. -/
theorem rank_two_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : LocalModels.RankTwoTheoremC G) : SylowOvergroupComponentUnique G := by
  cases hm with
  | linear n hn iso => exact linear_three_even_sylow_overgroup_component_unique hn iso
  | symplectic n hn iso => exact symplectic_even_sylow_overgroup_component_unique hn iso
  | g2 n hn iso => exact g2_even_sylow_overgroup_component_unique hn iso
  | triality n hn iso => exact triality_even_sylow_overgroup_component_unique hn iso
  | ree m hm iso => exact ree_sylow_overgroup_component_unique hm iso
  | symplectic_derived iso => exact binary_symplectic_derived_sylow_overgroup_component_unique iso
  | g2_derived iso => exact binary_g2_derived_sylow_overgroup_component_unique iso
  | tits iso => exact tits_sylow_overgroup_component_unique iso

/-- Exactly the even model alternatives assigned to the moved-chain calculation. -/
@[expose] def EvenModel (G : Type*) [Group G] : Prop :=
  LocalModels.RankTwoTheoremC G ∨
  (ClassicalGroup.IsPSL G 4 2 ∨ ClassicalGroup.IsPSL G 5 2) ∨
  LocalModels.IsAlternating G 8

/-- The higher characteristic-two model calculation, including A₈ via the
actual exceptional isomorphism with PSL₄(2). -/
theorem even_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : EvenModel G) : SylowOvergroupComponentUnique G := by
  rcases hm with hm | (hm | hm) | hm
  · exact rank_two_sylow_overgroup_component_unique hm
  · exact binary_higher_linear_sylow_overgroup_component_unique (Or.inl rfl) hm
  · exact binary_higher_linear_sylow_overgroup_component_unique (Or.inr rfl) hm
  · exact alternating_eight_sylow_overgroup_component_unique hm

/-- Application to the literal radical quotient in the moved normalized
remaining-simple-quotient obstruction. No embedding or normalizer callback
is supplied: the concrete Levi calculations discharge uniqueness. -/
theorem moved_normalized_not_even_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    ¬ EvenModel (C ⧸ solvableRadical C) := by
  obtain ⟨hs,_,_,hu⟩ := moved_normalized_remaining_simple_quotient
    hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact fun hmodel => hu (even_sylow_overgroup_component_unique hmodel)

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
