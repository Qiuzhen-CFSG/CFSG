module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Formal

/-!
# Soundness of the remaining ambient transition checks

The Boolean check compares the two short positive words using the staged
full-degree tables. Formal tree and padding entries have already been proved;
`EssentialChecks` contains only the remaining 167 equations. Every such
equation must hold at every one of the 306936 ambient letters.

`stepIdentities_of_compared_candidates_of_checks` in the assembly module
consumes these checks together with `TableAgreement`. Neither finite premise
is supplied by this soundness module. Source: ATLAS F24G1-p306936B0,
GLS3 Table 5.3v, and `LastFour/source/schreier.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
open Certificate

/-- Test the literal product convention on a bounded ambient label. -/
def stepTest (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i)) (x : Nat) : Bool :=
  rawGenerator i.castSucc a (rawEvaluate i.castSucc (representativeWord i j) (x % 306936)) ==
    rawEvaluate i.castSucc (representativeWord i (transitionIndex i a j))
      (rawEvaluate i.succ (factorWord i a j) (x % 306936))

/-- The genuinely numerical entries, checked on the whole ambient set. -/
def EssentialChecks : Prop := ∀ i a j, formalEntry i a j = false →
  ∀ x : Fin 306936, stepTest i a j x.val = true

/-- Four balanced intervals suffice for a single full-degree transition. -/
theorem stepTest_of_intervals (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i))
    (h₀ : checkPow (stepTest i a j) 0 18 = true)
    (h₁ : checkPow (stepTest i a j) 262144 15 = true)
    (h₂ : checkPow (stepTest i a j) 294912 13 = true)
    (h₃ : checkPow (stepTest i a j) 303104 12 = true) :
    ∀ x : Fin 306936, stepTest i a j x.val = true :=
  FirstFourModel.covered_checks _ h₀ h₁ h₂ h₃

/-- A numerical transition gives equality in the literal original carrier. -/
theorem step_of_table_checks
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm) (hg : TableAgreement)
    (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i))
    (h : ∀ x : Fin 306936, stepTest i a j x.val = true) :
    LastFour.generator i.castSucc a * representative i j =
      representative i (transitionIndex i a j) * factor i a j := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hx := h x
  simp only [stepTest, Nat.mod_eq_of_lt x.isLt, beq_iff_eq] at hx
  change ((LastFour.generator i.castSucc a).val ((representative i j).val x)).val =
    ((representative i (transitionIndex i a j)).val ((factor i a j).val x)).val
  rw [generator_val_of_compared_candidates ha hb, hg]
  change rawGenerator i.castSucc a (((LastFour.evaluate i.castSucc
    (representativeWord i j)).val x).val) =
      ((LastFour.evaluate i.castSucc (representativeWord i (transitionIndex i a j))).val
        ((LastFour.evaluate i.succ (factorWord i a j)).val x)).val
  rw [evaluate_apply_of_tableAgreement ha hb hg,
    evaluate_apply_of_tableAgreement ha hb hg,
    evaluate_apply_of_tableAgreement ha hb hg]
  exact hx

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
