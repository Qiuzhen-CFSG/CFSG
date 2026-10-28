module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators
public import Theory.AtlasPort.Janko2.Conway.IcosianOrder


/-!
# Comparing the permutation and icosian Hall--Janko groups

The certified five-relator ATLAS presentation gives a map from the literal
degree-100 carrier to the actual projective icosian group. The concrete
icosian pair generates the whole sign quotient, so the map is surjective.
The independently proved orders, both 604800, make it an isomorphism.
The images of the two published generators are retained.

The conditional constructions are retained, and `comparison` supplies both
inputs from the independent presentation and root-orbit certificates.
Thus `nonempty_icosianComparison` has no additional premises. The 315-point
root action is used to prove generation of the icosian group; it is not
identified with the degree-100 permutation action.

Source: ATLAS presentation `J2G1-P2`; Aschbacher, *Sporadic Groups* (1994),
Section 47, especially 47.10, pp.266–267. The comparison is needed to
transport the literal D₁₀-centralizer A₅ in Lemma 49.5, pp.283–284;
`IcosianComparison.Application` specializes that existing consumer.
The imported icosian construction retains Gerald Höhn's ATLAS attribution
and license; neither concrete carrier is redefined here.
-/

@[expose] public section

open Atlas.Conway
namespace Sporadic.LeechRelated.J2.IcosianComparison
open G2FourModule.Embedding.InnerRealization

/-- Identify the presented group with the permutation carrier, given exactness. -/
noncomputable def permutationEquiv (hp : Function.Injective Presentation.toCarrier) :
    Presentation.UniversalGroup ≃* Carrier :=
  MulEquiv.ofBijective Presentation.toCarrier ⟨hp, Presentation.toCarrier_surjective⟩

/-- Evaluate all five relators in the sign quotient and descend along exactness. -/
noncomputable def homOfRelations (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y) :
    Carrier →* IcosianProjectiveModel :=
  (Presentation.toGroup x y h).comp (permutationEquiv hp).symm.toMonoidHom

@[simp] theorem homOfRelations_a (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y) :
    homOfRelations hp x y h GeneratorPair.a = x := by
  change Presentation.toGroup x y h ((permutationEquiv hp).symm GeneratorPair.a) = x
  rw [← Presentation.toCarrier_zero]
  change Presentation.toGroup x y h
    ((permutationEquiv hp).symm (permutationEquiv hp (PresentedGroup.of 0))) = x
  rw [MulEquiv.symm_apply_apply, Presentation.toGroup_zero]

@[simp] theorem homOfRelations_b (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y) :
    homOfRelations hp x y h GeneratorPair.b = y := by
  change Presentation.toGroup x y h ((permutationEquiv hp).symm GeneratorPair.b) = y
  rw [← Presentation.toCarrier_one]
  change Presentation.toGroup x y h
    ((permutationEquiv hp).symm (permutationEquiv hp (PresentedGroup.of 1))) = y
  rw [MulEquiv.symm_apply_apply, Presentation.toGroup_one]

/-- Generation of the entire quotient makes the descended map surjective. -/
theorem homOfRelations_surjective (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y)
    (hg : Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤) :
    Function.Surjective (homOfRelations hp x y h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hg]
  apply (Subgroup.closure_le _).mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with hz | hz
  · exact ⟨GeneratorPair.a, (homOfRelations_a hp x y h).trans hz.symm⟩
  · rw [Set.mem_singleton_iff] at hz
    exact ⟨GeneratorPair.b, (homOfRelations_b hp x y h).trans hz.symm⟩

/-- The two established order calculations turn the surjection into an equivalence. -/
noncomputable def comparisonOfGeneratingPair
    (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y)
    (hg : Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤) :
    Carrier ≃* IcosianProjectiveModel :=
  MulEquiv.ofBijective (homOfRelations hp x y h)
    ((homOfRelations_surjective hp x y h hg).bijective_of_nat_card_le (by
      rw [ExceptionalParabolics.FirstParabolic.card_carrier, icosianProjective_order]))


@[simp] theorem comparisonOfGeneratingPair_a
    (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y)
    (hg : Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤) :
    comparisonOfGeneratingPair hp x y h hg GeneratorPair.a = x :=
  homOfRelations_a hp x y h

@[simp] theorem comparisonOfGeneratingPair_b
    (hp : Function.Injective Presentation.toCarrier)
    (x y : IcosianProjectiveModel) (h : Presentation.Relations x y)
    (hg : Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤) :
    comparisonOfGeneratingPair hp x y h hg GeneratorPair.b = y :=
  homOfRelations_b hp x y h

/-- Conditional assembly from presentation exactness and an icosian generating pair. -/
theorem nonempty_icosianComparison_of_generatingPair
    (hp : Function.Injective Presentation.toCarrier)
    (hpair : ∃ x y : IcosianProjectiveModel, Presentation.Relations x y ∧
      Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤) :
    Nonempty (Carrier ≃* IcosianProjectiveModel) := by
  obtain ⟨x, y, h, hg⟩ := hpair
  exact ⟨comparisonOfGeneratingPair hp x y h hg⟩

/-- The fixed equivalence between the actual permutation carrier and sign quotient. -/
noncomputable def comparison : Carrier ≃* IcosianProjectiveModel :=
  comparisonOfGeneratingPair PresentationExact.toCarrier_injective
    Generators.x Generators.y Generators.relations Generators.closure_pair_eq_top

@[simp] theorem comparison_a : comparison GeneratorPair.a = Generators.x :=
  comparisonOfGeneratingPair_a _ _ _ _ _

@[simp] theorem comparison_b : comparison GeneratorPair.b = Generators.y :=
  comparisonOfGeneratingPair_b _ _ _ _ _

/-- The two concrete Hall--Janko models are unconditionally multiplicatively equivalent. -/
theorem nonempty_icosianComparison : Nonempty (Carrier ≃* IcosianProjectiveModel) :=
  ⟨comparison⟩

end Sporadic.LeechRelated.J2.IcosianComparison
