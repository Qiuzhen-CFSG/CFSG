module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Quotient

/-!
# A presentation cover of the actual max2 quotient

Evaluation of the two generators gives a surjection onto H/N whenever the
29 explicit relators lie in N. Thus a finite presentation bound controls the
actual relative quotient. All premises remain explicit until the matrix and
finite-presentation certificates discharge them. See `Presentation.Data` for
the ATLAS provenance and word convention.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation

/-- The ordered pair of concrete local generators. -/
def localGenerators : Bool → localSubgroup
  | false => subgroupX
  | true => subgroupY

/-- Evaluate an abstract relator in the actual matrix subgroup, before quotienting. -/
def localRelator (i : Fin 29) : localSubgroup :=
  FreeGroup.lift (localGenerators) (relatorWord i)

/-- The quotient images of the same ordered pair. -/
def quotientGenerators (b : Bool) : LocalNormalClosureQuotient :=
  QuotientGroup.mk' (localNormalClosure) (localGenerators b)

theorem localGenerators_generate :
    Subgroup.closure (Set.range (localGenerators)) = ⊤ := by
  have hr : Set.range (localGenerators) = {subgroupX, subgroupY} := by
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [localGenerators]
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [hr, local_generators_generate]

theorem quotientGenerators_generate :
    Subgroup.closure (Set.range (quotientGenerators)) = ⊤ := by
  have hr : Set.range (quotientGenerators) =
      (QuotientGroup.mk' (localNormalClosure)) '' Set.range (localGenerators) :=
    (Set.range_comp _ _).trans rfl
  rw [hr, ← MonoidHom.map_closure, localGenerators_generate]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- Relator membership is exactly the relation required by the universal property. -/
theorem quotient_relator_eq_one
    (hrel : ∀ i, localRelator i ∈ localNormalClosure)
    (r : FreeGroup Bool) (hr : r ∈ Set.range relatorWord) :
    FreeGroup.lift (quotientGenerators) r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  have he := FreeGroup.lift_unique
    ((QuotientGroup.mk' (localNormalClosure)).comp
      (FreeGroup.lift (localGenerators)))
    (f := quotientGenerators) (by intro b; simp [quotientGenerators])
    (x := relatorWord i)
  rw [← he]
  exact (QuotientGroup.eq_one_iff _).mpr (hrel i)

/-- The homomorphism from the candidate presentation to the actual quotient. -/
def presentationToQuotient
    (hrel : ∀ i, localRelator i ∈ localNormalClosure) :
    Group →* LocalNormalClosureQuotient :=
  PresentedGroup.toGroup (quotient_relator_eq_one hrel)

@[simp] theorem presentationToQuotient_of
    (hrel : ∀ i, localRelator i ∈ localNormalClosure) (b : Bool) :
    presentationToQuotient hrel (PresentedGroup.of b) =
      quotientGenerators b := PresentedGroup.toGroup.of _

theorem presentationToQuotient_surjective
    (hrel : ∀ i, localRelator i ∈ localNormalClosure) :
    Function.Surjective (presentationToQuotient hrel) := by
  rw [← MonoidHom.range_eq_top, ← top_le_iff,
    ← quotientGenerators_generate, Subgroup.closure_le]
  rintro _ ⟨b, rfl⟩
  exact ⟨PresentedGroup.of b, presentationToQuotient_of hrel b⟩

/-- A finite presentation bound and certified relator membership bound H/N. -/
theorem quotient_card_le_of_relators
    (hrel : ∀ i, localRelator i ∈ localNormalClosure)
    (hbound : Finite Group ∧ Nat.card Group ≤ 2661120) :
    Nat.card LocalNormalClosureQuotient ≤ 2661120 := by
  let := hbound.1
  exact (Nat.card_le_card_of_surjective _
    (presentationToQuotient_surjective hrel)).trans hbound.2

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation
