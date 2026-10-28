module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.NormalGeneration
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Group

/-!
# An explicit involutory marking of the O'Nan matrix model

The four conjugates `B^i A B^(-i)`, for `0 ≤ i < 4`, generate the fixed
projective matrix carrier. The original A is the zeroth conjugate, and B is
the product of eleven consecutive conjugates, with the indices read modulo
four. This follows from `B^4 = (AB)^11 = 1`, without an order or simplicity
assumption. Both changes of generators are explicit free-group words.

The matrix relations are certified in `ProjectiveSimplicity.Relations`, using
the ATLAS matrices attributed in `refs/original/onan/README.md`. This module
supplies a marking only: it does not assert that any finite list of relators
presents O'Nan's group. In particular it does not identify the candidate
presentations in Soicher's 1985 thesis with the matrix model.
-/

namespace ONan.Presentation

/-- The original two generators, with `false` naming A and `true` naming B. -/
@[expose] public def standardGenerator : Bool → Model
  | false => generatorA
  | true => generatorB

/-- The four proposed involutions as concrete words in the original generators. -/
@[expose] public def involutionWord (i : Fin 4) : FreeGroup Bool :=
  FreeGroup.of true ^ i.val * FreeGroup.of false * (FreeGroup.of true ^ i.val)⁻¹

/-- The actual conjugate involutions in the fixed projective matrix model. -/
@[expose] public def involutionGenerator (i : Fin 4) : Model :=
  generatorB ^ i.val * generatorA * (generatorB ^ i.val)⁻¹

/-- Evaluation of the explicit words gives the marked matrix elements. -/
public theorem involutionWord_evaluation (i : Fin 4) :
    FreeGroup.lift standardGenerator (involutionWord i) = involutionGenerator i := by
  simp [involutionWord, involutionGenerator, standardGenerator]

/-- Every marked element has square one. -/
public theorem involutionGenerator_pow_two (i : Fin 4) : involutionGenerator i ^ 2 = 1 := by
  rw [involutionGenerator, conj_pow, generatorA_pow_two]
  simp

/-- All four marked elements are nonidentity involutions. -/
public theorem orderOf_involutionGenerator (i : Fin 4) : orderOf (involutionGenerator i) = 2 := by
  apply orderOf_eq_prime (involutionGenerator_pow_two i)
  intro h
  have ha : generatorA = 1 := by
    simpa [involutionGenerator, mul_assoc] using
      congrArg (fun x => (generatorB ^ i.val)⁻¹ * x * generatorB ^ i.val) h
  exact generatorA_mul_generatorB_ne (by simp [ha])

/-- The original A expressed in the four-letter alphabet. -/
@[expose] public def originalAWord : FreeGroup (Fin 4) := FreeGroup.of 0

/-- The original B expressed in the four-letter alphabet. -/
@[expose] public def originalBWord : FreeGroup (Fin 4) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 3) ^ 2 *
    FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2

/-- Word evaluation for the four explicitly marked involutions. -/
@[expose] public def involutionEvaluation : FreeGroup (Fin 4) →* Model :=
  FreeGroup.lift involutionGenerator

/-- The zeroth conjugate recovers the original A. -/
public theorem originalAWord_evaluation : involutionEvaluation originalAWord = generatorA := by
  simp [involutionEvaluation, originalAWord, involutionGenerator]

private theorem recover_second {G : Type*} [Group G] (a b : G) (hb : b ^ 4 = 1)
    (hab : (a * b) ^ 11 = 1) :
    (a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹) *
      (b ^ 3 * a * (b ^ 3)⁻¹)) ^ 2 *
      a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹) = b := by
  have hfour : a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹) *
      (b ^ 3 * a * (b ^ 3)⁻¹) = (a * b) ^ 4 := by
    calc
      _ = (a * b) ^ 4 * (b ^ 4)⁻¹ := by
        simp only [pow_succ, pow_zero]
        group
      _ = _ := by rw [hb, inv_one, mul_one]
  rw [hfour]
  calc
    _ = (a * b) ^ 11 * (b ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero]
        group
    _ = b := by
      rw [hab, one_mul]
      apply inv_eq_of_mul_eq_one_left
      simpa only [← pow_succ'] using hb

/-- Eleven explicitly marked involutions recover the original B. -/
public theorem originalBWord_evaluation : involutionEvaluation originalBWord = generatorB := by
  simpa [involutionEvaluation, originalBWord, involutionGenerator] using
    recover_second generatorA generatorB generatorB_pow_four generatorAB_pow_eleven

/-- The concrete four-involution marking is surjective at the level of words. -/
public theorem involutionEvaluation_surjective : Function.Surjective involutionEvaluation := by
  apply MonoidHom.range_eq_top.mp
  apply subgroup_eq_top_of_generators_mem
  · exact ⟨originalAWord, originalAWord_evaluation⟩
  · exact ⟨originalBWord, originalBWord_evaluation⟩

/-- The four involutions generate the actual matrix model. -/
public theorem closure_involutionGenerator :
    Subgroup.closure (Set.range involutionGenerator) = ⊤ :=
  FreeGroup.lift_surjective_iff_closure_range_eq_top.mp involutionEvaluation_surjective

end ONan.Presentation
