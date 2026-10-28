module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySmallModels
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups

/-!+# The small characteristic-two carriers in the moved-component restriction

Proper overgroups of a full Sylow two-subgroup are solvable in PSL₃(2),
PSp₄(2)′, G₂(2)′ and the Tits group. The actual binary symplectic derived
carrier is transported through its exceptional isomorphism with A₆.
Consequently these groups have at most one C-component in every Sylow
overgroup. The final application excludes each carrier on the literal
radical quotient of the normalized overcomponent.

Source: Aschbacher--Smith, A.3.12, printed pp.47--48, and 1.2.8(1), p.506.
The imported ATLAS calculations retain their attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

/-- The small carriers, with their actual isomorphisms. -/
@[expose] def SmallEvenModel (G : Type*) [Group G] : Prop :=
  ClassicalGroup.IsPSL G 3 2 ∨
  Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
  Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (G ≃* Tits.ParrottGroup)

/-- The binary linear rank-two endpoint. -/
theorem binary_linear_three_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G] (hm : ClassicalGroup.IsPSL G 3 2) :
    SylowOvergroupComponentUnique G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    (SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF))

/-- The genuine derived symplectic carrier, through PSp₄(2)′ ≅ A₆. -/
theorem binary_symplectic_derived_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  exact small_alternating_sylow_overgroup_component_unique (Or.inr
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)

/-- Proper full-Sylow overgroups of the genuine G₂(2)′ carrier are solvable. -/
theorem binary_g2_derived_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  exact SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    (SolvableSylowOvergroups.of_equiv e Atlas.G2.binaryDerived_solvableSylowOvergroups)

/-- The Tits row uses the actual Parrott group. -/
theorem tits_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Tits.ParrottGroup)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  exact SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    (SolvableSylowOvergroups.of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups)

/-- Assembly of the four small characteristic-two rows. -/
theorem small_even_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G] (hm : SmallEvenModel G) :
    SylowOvergroupComponentUnique G := by
  rcases hm with hm | hm | hm | hm
  · exact binary_linear_three_sylow_overgroup_component_unique hm
  · exact binary_symplectic_derived_sylow_overgroup_component_unique hm
  · exact binary_g2_derived_sylow_overgroup_component_unique hm
  · exact tits_sylow_overgroup_component_unique hm

/-- The original normalized overcomponent's radical quotient cannot be one
of these four carriers when the smaller local component is moved. -/
theorem moved_normalized_not_small_even_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    ¬ SmallEvenModel (C ⧸ solvableRadical C) := by
  obtain ⟨hs,_,_,hu⟩ := moved_normalized_remaining_simple_quotient
    hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact fun hmodel => hu (small_even_sylow_overgroup_component_unique hmodel)

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
