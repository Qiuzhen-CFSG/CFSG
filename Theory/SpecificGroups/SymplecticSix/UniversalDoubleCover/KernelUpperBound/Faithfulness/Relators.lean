module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Setup
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Certificate.Context

/-!
# Interpretation of the 36-coset trace in the abstract presentation

The eight original loops are precisely the seven ATLAS words and c = bab³.
All other loops are inverse or cyclic rotations. The subgroup facts refer
only to the literal subgroup ⟨a, bab³⟩. No matrix identity is used to prove
an equation in the abstract presented group.

Source: ATLAS `S62G1-P1.M`; certificate provenance is in `source/README.md`.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness
open Subgroup.CosetWordCertificate Certificate

private theorem original_eval (i : Fin 8) : eval traceGenerator (originals i) = 1 := by
  fin_cases i
  · change eval traceGenerator [(0, true), (0, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 0
  · change eval traceGenerator [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 1
  · change eval traceGenerator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 2
  · change eval traceGenerator [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 3
  · change eval traceGenerator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 4
  · change eval traceGenerator [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 5
  · change eval traceGenerator [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, traceGenerator, word, sourceCommutator,
      pow_succ, mul_assoc] using relator_eval 6
  · change eval traceGenerator [(1, true), (0, true), (1, true), (1, true), (1, true), (2, false)] = 1
    simp [eval, FreeGroup.lift_mk, traceGenerator, s8Generator, pow_succ, mul_assoc]

set_option maxRecDepth 10000 in
private theorem variants_exact : ∀ i : Fin 70,
    relatorTable i.val = variant (originals (variantTable i.val).1)
      (variantTable i.val).2.1 (variantTable i.val).2.2 := by decide +kernel

private theorem relator_ok (r : Nat) : eval traceGenerator (relatorWords r) = 1 := by
  let i : Fin 70 := ⟨min r 69, by omega⟩
  rw [relatorWords, variants_exact i]
  exact eval_variant _ (original_eval _) _ _

/-- Every deduction is interpreted in the group defined by the seven source words. -/
theorem certificate_valid :
    Valid context s8Subgroup traceGenerator (definitions.repr traceGenerator) := by
  apply definitions.valid
  · intro a ha
    simp only [Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with rfl | rfl
    · simpa [eval_letter, traceGenerator, s8Generator] using s8Generator_mem false
    · simpa [eval_letter, traceGenerator] using s8Generator_mem true
  · exact relator_ok

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness
