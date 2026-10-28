module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Checked
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Shape
import Mathlib.Tactic.FinCases

/-!
# A certified 48-coset cover of the thirty-relator presentation

The certificate introduces a third letter with value `y⁴`. Its first thirty
relations are exactly the defining relations, and its last relation is the
identity `y⁴ (y⁴)⁻¹ = 1`. Its subgroup loops are `x` and `y⁴`.
The generic coset-word soundness theorem then turns the 8,000 checked deductions
into actual subgroup-witness equations for all 288 signed transitions. Restricting
to the original generators gives a 48-coset cover, without assuming finiteness.

Source: the exact words of `AtlasBoundThirtyPresentation` and the reproducible
proof producer and kernel certificate in `AtlasBoundThirtySource/`. The numerical
GAP index is discovery data only; all deductions used here are checked in Lean.
-/

namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

private def generator : Fin 3 → BoundThirtyPresentation := fun i =>
  match i.val with
  | 0 => boundThirtyGenerator false
  | 1 => boundThirtyGenerator true
  | _ => boundThirtyGenerator true ^ 4

private theorem relator_model (i : Fin 31) : eval generator (relatorFin i) = 1 := by
  fin_cases i
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 0
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 1
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 2
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 3
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 4
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 5
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 6
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 7
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 8
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 9
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 10
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 11
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 12
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 13
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 14
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 15
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 16
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 17
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 18
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 19
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 20
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 21
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 22
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 23
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 24
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 25
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 26
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 27
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 28
  · simpa [eval, FreeGroup.lift_mk, generator, relatorFin, boundThirtyRelator,
      boundThirtyWord, boundLetters] using boundThirty_relator_eq_one 29
  · simp [eval, FreeGroup.lift_mk, generator, relatorFin, pow_succ, mul_assoc]

private theorem valid : Valid context boundThirtyMiddle generator (definitions.repr generator) := by
  apply definitions.valid
  · intro a ha
    simp only [decide_eq_true_eq] at ha
    rcases ha with rfl | rfl
    · exact boundThirtyMiddleWord_mem false
    · exact boundThirtyMiddleWord_mem true
  · intro r
    dsimp [relatorWords]
    split
    · exact relator_model _
    · exact eval_nil _

private def cover : Subgroup.GeneratorCosetCover boundThirtyMiddle generator (Fin 48) :=
  coverOfFacts facts survivor 0 (by change definitions.repr generator 0 = 1; simp)
    dest output hshape (fun i a => all_hold valid _ (hlt i a))

end G2Five.AtlasPresentation.ThirtyCertificate

namespace G2Five.AtlasPresentation

/-- A cover of the abstract presentation by 48 cosets of `⟨x,y⁴⟩`.
Every transition is an equality in the presented group. -/
public def boundThirtyMiddleCover :
    Subgroup.GeneratorCosetCover boundThirtyMiddle boundThirtyGenerator (Fin 48) where
  repr := ThirtyCertificate.cover.repr
  initial := ThirtyCertificate.cover.initial
  initial_eq := ThirtyCertificate.cover.initial_eq
  step i a := by
    cases a
    · exact ThirtyCertificate.cover.step i 0
    · exact ThirtyCertificate.cover.step i 1
  inv_step i a := by
    cases a
    · exact ThirtyCertificate.cover.inv_step i 0
    · exact ThirtyCertificate.cover.inv_step i 1

end G2Five.AtlasPresentation
