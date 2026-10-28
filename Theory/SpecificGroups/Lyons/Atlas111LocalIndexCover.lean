module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexSetup
public import Theory.SpecificGroups.Lyons.GebhardtPresentation
public import Theory.GroupTheory.GeneratorCosetCoverTransport

/-!
# Transfer of the Gebhardt coset cover to the concrete Lyons matrices

A coset cover for the four-generator subgroup of Gebhardt's five-generator
presentation gives the concrete cover, provided the presentation maps onto the
fixed matrix group and its first four generators land in the literal ATLAS
`max1Program` subgroup. Subgroup inclusion suffices; neither an isomorphism nor
the order of either group is required.

The transfer maps representatives and subgroup witnesses, using ambient
generation to handle both ATLAS generators and their inverses. The abstract
cover and the matrix realization remain independent construction obligations;
this file proves their assembly and does not assert an unconditional bound.

Source: V. Gebhardt, Experimental Mathematics 9 (2000), 333–338, Section 3B;
see `GebhardtPresentation` for the literal relations and source conventions.
-/

namespace Lyons.OrderCertificate

/-- Membership of the two ATLAS generators in the image proves surjectivity. -/
public theorem gebhardtHom_surjective (f : Gebhardt.Presentation →* LyonsGroup)
    (ha : generatorA ∈ f.range) (hb : generatorB ∈ f.range) :
    Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← closure_generators]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · exact Set.mem_singleton_iff.mp hx ▸ hb

/-- Assemble a concrete cover from the abstract cover and the matrix realization. -/
public def localIndexCoverOfGebhardt
    (C : Subgroup.GeneratorCosetCover Gebhardt.localSubgroup Gebhardt.generator
      (Fin 8835156))
    (f : Gebhardt.Presentation →* LyonsGroup) (hf : Function.Surjective f)
    (hlocal : ∀ i : Gebhardt.Alphabet, i.val < 4 → f (Gebhardt.generator i) ∈ localSubgroup) :
    Subgroup.GeneratorCosetCover localSubgroup indexGenerator (Fin 8835156) :=
  C.mapSurjective Gebhardt.closure_range_generator f hf localSubgroup
    (Gebhardt.localSubgroup_map_le f localSubgroup hlocal) indexGenerator

/-- The two independent certificates imply the requested concrete upper bound. -/
public theorem localIndex_le_of_gebhardt
    (C : Subgroup.GeneratorCosetCover Gebhardt.localSubgroup Gebhardt.generator
      (Fin 8835156))
    (f : Gebhardt.Presentation →* LyonsGroup) (hf : Function.Surjective f)
    (hlocal : ∀ i : Gebhardt.Alphabet, i.val < 4 → f (Gebhardt.generator i) ∈ localSubgroup) :
    localSubgroup.index ≤ 8835156 :=
  localIndex_le_of_cover (localIndexCoverOfGebhardt C f hf hlocal)

end Lyons.OrderCertificate
