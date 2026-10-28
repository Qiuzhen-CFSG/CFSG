module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.CommutatorIdentities.Action
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.CommutatorIdentities.Certificate.Context
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Interpreting the commutator certificate

All relators of the permutation action follow from the seven central source
words, the three already proved involution identities, and the definitions of
four stabilizer generators. No relation in a concrete matrix group is used.
Source: ATLAS S62G1-P1.M; reproduction and attribution in `source/README.md`.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.CommutatorIdentities
open Subgroup.CosetWordCertificate Certificate
open scoped IsMulCommutative

private theorem commutator_one {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    sourceCommutator x y = 1 := by
  dsimp [sourceCommutator]
  calc
    _ = x⁻¹ * (y⁻¹ * x) * y := by group
    _ = x⁻¹ * (x * y⁻¹) * y := by rw [h.inv_right.eq.symm]
    _ = 1 := by group

private theorem original_0 : eval traceGenerator (originals 0) = 1 := by
  change eval traceGenerator [(0, true), (0, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 0

private theorem original_1 : eval traceGenerator (originals 1) = 1 := by
  change eval traceGenerator [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 1

private theorem original_2 : eval traceGenerator (originals 2) = 1 := by
  change eval traceGenerator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 2

private theorem original_3 : eval traceGenerator (originals 3) = 1 := by
  change eval traceGenerator [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 3

private theorem original_4 : eval traceGenerator (originals 4) = 1 := by
  change eval traceGenerator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 4

private theorem original_5 : eval traceGenerator (originals 5) = 1 := by
  change eval traceGenerator [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 5

private theorem original_6 : eval traceGenerator (originals 6) = 1 := by
  change eval traceGenerator [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
    pow_succ, mul_assoc] using conjugation_word 6

private theorem original_7 : eval traceGenerator (originals 7) = 1 := by
  change eval traceGenerator [(2, true), (2, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, pow_two] using
    congrArg translation centralRelator_four_sq

private theorem original_8 : eval traceGenerator (originals 8) = 1 := by
  change eval traceGenerator [(0, false), (2, false), (0, true), (2, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute a (centralRelator 4))

private theorem original_9 : eval traceGenerator (originals 9) = 1 := by
  change eval traceGenerator [(1, false), (2, false), (1, true), (2, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute b (centralRelator 4))

private theorem original_10 : eval traceGenerator (originals 10) = 1 := by
  change eval traceGenerator [(3, true), (3, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, pow_two] using
    congrArg translation centralRelator_five_sq

private theorem original_11 : eval traceGenerator (originals 11) = 1 := by
  change eval traceGenerator [(0, false), (3, false), (0, true), (3, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute a (centralRelator 5))

private theorem original_12 : eval traceGenerator (originals 12) = 1 := by
  change eval traceGenerator [(1, false), (3, false), (1, true), (3, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute b (centralRelator 5))

private theorem original_13 : eval traceGenerator (originals 13) = 1 := by
  change eval traceGenerator [(2, false), (3, false), (2, true), (3, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one ((Commute.all (centralRelator 4) (centralRelator 5)).map translation)

private theorem original_14 : eval traceGenerator (originals 14) = 1 := by
  change eval traceGenerator [(4, true), (4, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, pow_two] using
    congrArg translation centralRelator_six_sq

private theorem original_15 : eval traceGenerator (originals 15) = 1 := by
  change eval traceGenerator [(0, false), (4, false), (0, true), (4, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute a (centralRelator 6))

private theorem original_16 : eval traceGenerator (originals 16) = 1 := by
  change eval traceGenerator [(1, false), (4, false), (1, true), (4, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one (translation_commute b (centralRelator 6))

private theorem original_17 : eval traceGenerator (originals 17) = 1 := by
  change eval traceGenerator [(2, false), (4, false), (2, true), (4, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one ((Commute.all (centralRelator 4) (centralRelator 6)).map translation)

private theorem original_18 : eval traceGenerator (originals 18) = 1 := by
  change eval traceGenerator [(3, false), (4, false), (3, true), (4, true)] = 1
  simpa [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator, mul_assoc] using
    commutator_one ((Commute.all (centralRelator 5) (centralRelator 6)).map translation)

private theorem original_19 : eval traceGenerator (originals 19) = 1 := by
  change eval traceGenerator [(1, true), (0, true), (1, false), (0, true), (1, true), (3, true), (5, false)] = 1
  simp [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator,
    map_mul, map_inv, pow_succ, mul_assoc]

private theorem original_20 : eval traceGenerator (originals 20) = 1 := by
  change eval traceGenerator [(1, false), (1, false), (0, true), (1, true), (1, true), (4, true), (6, false)] = 1
  simp [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator,
    map_mul, map_inv, pow_succ, mul_assoc]

private theorem original_21 : eval traceGenerator (originals 21) = 1 := by
  change eval traceGenerator [(1, true), (1, true), (0, true), (1, false), (1, false), (4, true), (7, false)] = 1
  simp [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator,
    map_mul, map_inv, pow_succ, mul_assoc]

private theorem original_22 : eval traceGenerator (originals 22) = 1 := by
  change eval traceGenerator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (8, false)] = 1
  simp [eval, FreeGroup.lift_mk, traceGenerator, sourceCommutator,
    map_mul, map_inv, pow_succ, mul_assoc]

private theorem original_eval (i : Fin 23) : eval traceGenerator (originals i) = 1 := by
  fin_cases i
  · exact original_0
  · exact original_1
  · exact original_2
  · exact original_3
  · exact original_4
  · exact original_5
  · exact original_6
  · exact original_7
  · exact original_8
  · exact original_9
  · exact original_10
  · exact original_11
  · exact original_12
  · exact original_13
  · exact original_14
  · exact original_15
  · exact original_16
  · exact original_17
  · exact original_18
  · exact original_19
  · exact original_20
  · exact original_21
  · exact original_22

private def variant (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  (if inv then FreeGroup.invRev w else w).rotate offset

private theorem eval_variant (w : Word Nat) (hw : eval traceGenerator w = 1)
    (inv : Bool) (offset : Nat) : eval traceGenerator (variant w inv offset) = 1 := by
  have h : eval traceGenerator (if inv then FreeGroup.invRev w else w) = 1 := by
    cases inv <;> simp [hw, eval_invRev]
  simpa [eval, FreeGroup.lift_mk, variant, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one
      (by simpa [eval, FreeGroup.lift_mk] using h) offset

set_option maxRecDepth 10000 in
private theorem variants_exact : ∀ i : Fin 206,
    relatorTable i.val = variant (originals (variantTable i.val).1)
      (variantTable i.val).2.1 (variantTable i.val).2.2 := by decide +kernel

private theorem relator_ok (r : Nat) : eval traceGenerator (relatorWords r) = 1 := by
  let i : Fin 206 := ⟨min r 205, by omega⟩
  rw [relatorWords, variants_exact i]
  exact eval_variant _ (original_eval _) _ _

/-- The certificate acts on the literal free central extension. -/
theorem certificate_valid :
    Valid context stabilizer traceGenerator (definitions.repr traceGenerator) := by
  apply definitions.valid
  · intro a ha
    simp only [Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with (((rfl | rfl) | rfl) | rfl) | rfl
    · simpa only [eval_letter, if_true] using generator_zero_mem
    · simpa only [eval_letter, if_true] using generator_five_mem
    · simpa only [eval_letter, if_true] using generator_six_mem
    · simpa only [eval_letter, if_true] using generator_seven_mem
    · simpa only [eval_letter, if_true] using generator_eight_mem
  · exact relator_ok

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.CommutatorIdentities
