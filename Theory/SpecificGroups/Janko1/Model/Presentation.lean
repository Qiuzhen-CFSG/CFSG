module

public import Theory.SpecificGroups.Janko1.Model.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.FinCases

/-!
# The ATLAS presentation mapped onto the J₁ matrix model

The five defining words of `J1G1-P1` give a presented group, and the explicit
matrix identities give a surjection from it to `Janko1.Model`. Surjectivity
uses the proved generation of the matrix model. No injectivity, order bound,
or simplicity is assumed here.

Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, *ATLAS of Finite Group
Representations*, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J1G1-P1
(retrieved 3 October 2026). This is the full five-relator presentation on that
page, as distinct from its separate four-order standard-generator test.
-/

namespace Janko1

/-- The five words of the ATLAS presentation, evaluated in any group. -/
@[expose] public def atlasWord {H : Type*} [Group H] (x y : H) : Fin 5 → H :=
  ![x ^ 2, y ^ 3, (x * y) ^ 7,
    (x * y * (x * y * x * y⁻¹) ^ 3) ^ 5,
    (x * y * (x * y * x * y⁻¹) ^ 6 * x * y * x * y * (x * y⁻¹) ^ 2) ^ 2]

private theorem map_atlasWord {H K : Type*} [Group H] [Group K]
    (f : H →* K) (x y : H) (i : Fin 5) :
    f (atlasWord x y i) = atlasWord (f x) (f y) i := by
  fin_cases i <;> simp [atlasWord]

/-- The five defining relators, on the generators `false` and `true`. -/
@[expose] public def atlasRelator : Fin 5 → FreeGroup Bool :=
  atlasWord (FreeGroup.of false) (FreeGroup.of true)

/-- The group defined by the full ATLAS presentation. -/
@[expose] public def AtlasPresentation := PresentedGroup (Set.range atlasRelator)
  deriving Group

/-- Its two canonical generators. -/
@[expose] public def presentationGenerator (i : Bool) : AtlasPresentation :=
  PresentedGroup.of i

/-- The corresponding elements of the matrix model. -/
@[expose] public def modelGenerator : Bool → Model
  | false => a
  | true => b

/-- Every defining relator vanishes in the matrix model. -/
public theorem atlasRelator_eval (i : Fin 5) :
    FreeGroup.lift modelGenerator (atlasRelator i) = 1 := by
  rw [atlasRelator, map_atlasWord, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  change atlasWord a b i = 1
  fin_cases i
  · exact a_pow_two
  · exact b_pow_three
  · exact ab_pow_seven
  · exact atlas_relator_four
  · exact atlas_relator_five

/-- The source presentation therefore has a canonical map to the concrete model. -/
@[expose] public def presentationToModel : AtlasPresentation →* Model :=
  PresentedGroup.toGroup (f := modelGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact atlasRelator_eval i)

@[simp] public theorem presentationToModel_generator (i : Bool) :
    presentationToModel (presentationGenerator i) = modelGenerator i :=
  PresentedGroup.toGroup.of _

/-- The matrix model is a quotient of the full sourced presentation. -/
public theorem presentationToModel_surjective : Function.Surjective presentationToModel := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← closure_pair_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨presentationGenerator false, presentationToModel_generator false⟩
  · rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨presentationGenerator true, presentationToModel_generator true⟩

/-- The universal source group itself satisfies its defining relators. -/
public theorem atlasPresentation_relator (i : Fin 5) :
    PresentedGroup.mk (Set.range atlasRelator) (atlasRelator i) = 1 :=
  PresentedGroup.one_of_mem ⟨i, rfl⟩

end Janko1
