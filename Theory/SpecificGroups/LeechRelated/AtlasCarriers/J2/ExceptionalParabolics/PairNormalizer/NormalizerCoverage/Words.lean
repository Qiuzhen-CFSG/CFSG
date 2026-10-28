module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage.Checks
public import Theory.GroupTheory.PresentedGroupBounds
import Mathlib.Tactic.FinCases

/-!
# A right-coset cover by the concrete J₂ candidate

All representatives and transition factors are actual words in the original
ATLAS carrier. The factor words belong to the shared candidate. The checked
transitions therefore give a cover of the whole carrier by right cosets of
that subgroup, using the original generating pair and its inverse alphabet.
Source: ATLAS J2G1-p100B0; GLS3 Table 5.3g. The finite witnesses and their
reproduction script are in this module's directory.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
open Theory.GroupTheory GeneratorPair GeneratorPair.FirstFusion Seed Data

/-- The six radical generators followed by the three shared normalizer generators. -/
private def factorGenerator : Fin 9 → Carrier :=
  ![q₂Generator 0, q₂Generator 1, q₂Generator 2, q₂Generator 3,
    q₂Generator 4, q₂Generator 5,
    normalizerGenerator 0, normalizerGenerator 1, normalizerGenerator 2]

private theorem factorGenerator_inclusion (i : Fin 9) :
    inclusion (factorGenerator i) = factorGeneratorTable i := by
  fin_cases i
  · exact q₂Generator_inclusion 0
  · exact q₂Generator_inclusion 1
  · exact q₂Generator_inclusion 2
  · exact q₂Generator_inclusion 3
  · exact q₂Generator_inclusion 4
  · exact q₂Generator_inclusion 5
  · exact sGenerator_inclusion 3
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private theorem factorGenerator_mem (i : Fin 9) : factorGenerator i ∈ candidate := by
  have hq (j : Fin 6) : q₂Generator j ∈ candidate :=
    q₂_le_candidate (Subgroup.subset_closure ⟨j, rfl⟩)
  fin_cases i <;>
    simp only [factorGenerator, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact hq 0
  · exact hq 1
  · exact hq 2
  · exact hq 3
  · exact hq 4
  · exact hq 5
  · exact normalizerGenerator_mem_candidate 0
  · exact normalizerGenerator_mem_candidate 1
  · exact normalizerGenerator_mem_candidate 2

/-- Actual words accounting for all transition factors. -/
private def factorElement (i : Fin 64) : Carrier := evalWord factorGenerator (factorWord i)

private theorem factorElement_mem (i : Fin 64) : factorElement i ∈ candidate := by
  have hw (w : List (Fin 9)) : evalWord factorGenerator w ∈ candidate := by
    induction w with
    | nil => exact candidate.one_mem
    | cons j w ih => exact candidate.mul_mem (factorGenerator_mem j) ih
  exact hw _

private theorem factorElement_spec (i : Fin 64) (p : Fin 100) :
    inclusion (factorElement i) p = factorMap i p := by
  have hw (w : List (Fin 9)) :
      inclusion (evalWord factorGenerator w) = evalWord factorGeneratorTable w := by
    induction w with
    | nil => exact map_one inclusion
    | cons j w ih => rw [evalWord, map_mul, factorGenerator_inclusion, ih, evalWord]
  exact congrArg (fun f : Equiv.Perm (Fin 100) => f p) (hw (factorWord i)) |>.trans
    (factor_word_check i p)

/-- The proposed right-coset representatives, as elements of the actual carrier. -/
@[expose] def repr (i : Fin 525) : Carrier := evalWord letter (reprWord i)

theorem repr_zero : repr 0 = 1 := rfl

theorem repr_spec (i : Fin 525) (p : Fin 100) : inclusion (repr i) p = reprMap i p := by
  have aux : ∀ (n : Nat) (i : Fin 525), i.val = n → ∀ p : Fin 100,
      inclusion (repr i) p = reprMap i p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi p
      by_cases hz : i = 0
      · subst i
        simpa only [repr_zero, map_one, Equiv.Perm.one_apply] using (repr_zero_check p).symm
      obtain ⟨hlt, hw⟩ := word_tree_check i hz
      have hp := ih (parent i).val (hi ▸ hlt) (parent i) rfl
      have hr : repr i = repr (parent i) * letter (parentLetter i) := by
        simp only [repr, hw, evalWord_append, evalWord, mul_one]
      rw [hr, map_mul, inclusion_letter]
      change inclusion (repr (parent i)) (permLetter (parentLetter i) p) = _
      rw [hp]
      exact (repr_tree_check i hz p).symm
  exact aux i.val i rfl p

private theorem repr_step (i : Fin 525) (j : Fin 3) :
    repr i * letter j = factorElement (factor i j) * repr (next i j) := by
  apply inclusion_injective
  apply Equiv.ext
  intro p
  simp only [map_mul, inclusion_letter, Equiv.Perm.mul_apply,
    repr_spec, factorElement_spec]
  exact transition_check i j p

/-- A certified right-coset cover; its factors are proved members of `candidate`. -/
private def cosetCover : Subgroup.GeneratorCosetCover candidate letter (Fin 525) where
  repr := repr
  initial := 0
  initial_eq := repr_zero
  step i j := ⟨⟨factorElement (factor i j), factorElement_mem _⟩, next i j, repr_step i j⟩
  inv_step i j := by
    rw [← letter_inv]
    exact ⟨⟨factorElement (factor i (invLetter j)), factorElement_mem _⟩,
      next i (invLetter j), repr_step i (invLetter j)⟩

theorem covers (x : Carrier) : ∃ h : candidate, ∃ i : Fin 525, x = h.val * repr i :=
  cosetCover.covers letter_generates x

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
