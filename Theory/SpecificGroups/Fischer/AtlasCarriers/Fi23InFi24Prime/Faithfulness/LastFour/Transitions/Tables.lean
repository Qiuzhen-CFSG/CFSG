module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word26
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word29
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word32
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word35
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word38
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word41
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word44
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word47
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables.Word50
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.WordModel

/-!
# Shared numerical interface for the final-four certificates

Ten full-degree tables represent the genuine generators of the last four
stages; the remaining entries are identities. `TableAgreement` asks for the
exact interpretation of all ten tables as the original polymorphic words in
`FirstFour.Model`. It is an explicit finite-computation obligation, not an
assumption of faithfulness or stabilizer recognition.

A positive-word evaluator uses one lookup per letter. Its correctness proof
ensures transition certificates never have to expand the nested original
words at each of the 306936 ambient points.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; reproducible witnesses in
`Transitions/source/generate_tables.py` and `LastFour/source/schreier.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
open Tables

/-- Full-degree numerical generators with literal identity padding. -/
def rawGenerator : Fin 5 → Fin 4 → Nat → Nat
  | 0 => ![raw23, raw26, raw29, raw32]
  | 1 => ![raw35, raw38, raw41, fun x => x % 306936]
  | 2 => ![raw44, raw47, fun x => x % 306936, fun x => x % 306936]
  | 3 => ![raw50, fun x => x % 306936, fun x => x % 306936, fun x => x % 306936]
  | 4 => ![fun x => x % 306936, fun x => x % 306936,
            fun x => x % 306936, fun x => x % 306936]

theorem rawGenerator_lt (i : Fin 5) (a : Fin 4) (x : Nat) :
    rawGenerator i a x < 306936 := by
  fin_cases i <;> fin_cases a <;> exact Nat.mod_lt _ (by decide)

/-- Each proposed table is a bounded function, before any permutation claim. -/
def image (i : Fin 5) (a : Fin 4) (x : Fin 306936) : Fin 306936 :=
  ⟨rawGenerator i a x.val, rawGenerator_lt i a x.val⟩

/-- Required identification with every literal full-degree model word. -/
def TableAgreement : Prop := ∀ i a (x : Fin 306936),
  (modelGenerator i a x).val = rawGenerator i a x.val

/-- Identity padding is automatic; only the ten genuine word tables need certificates. -/
theorem tableAgreement_of_word_checks
    (h23 : ∀ x : Fin 306936,
      (FirstFourModel.Word.word23 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw23 x.val)
    (h26 : ∀ x : Fin 306936,
      (FirstFourModel.Word.word26 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw26 x.val)
    (h29 : ∀ x : Fin 306936,
      (FirstFourModel.Word.word29 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw29 x.val)
    (h32 : ∀ x : Fin 306936,
      (FirstFourModel.Word.word32 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw32 x.val)
    (h35 : ∀ x : Fin 306936,
      (Word.word35 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw35 x.val)
    (h38 : ∀ x : Fin 306936,
      (Word.word38 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw38 x.val)
    (h41 : ∀ x : Fin 306936,
      (Word.word41 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw41 x.val)
    (h44 : ∀ x : Fin 306936,
      (Word.word44 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw44 x.val)
    (h47 : ∀ x : Fin 306936,
      (Word.word47 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw47 x.val)
    (h50 : ∀ x : Fin 306936,
      (Word.word50 FirstFourModel.aPerm FirstFourModel.bPerm x).val = raw50 x.val)
    : TableAgreement := by
  intro i a
  fin_cases i <;> fin_cases a
  · exact h23
  · exact h26
  · exact h29
  · exact h32
  · exact h35
  · exact h38
  · exact h41
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · exact h44
  · exact h47
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · exact h50
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · intro x
    exact (Nat.mod_eq_of_lt x.isLt).symm

/-- Left-action evaluation; the rightmost letter acts first. -/
def rawEvaluate (i : Fin 5) : List (Fin 4) → Nat → Nat
  | [], x => x
  | a :: w, x => rawGenerator i a (rawEvaluate i w x)

/-- The word evaluator preserves the exact permutation semantics. -/
theorem modelEvaluate_apply_of_tableAgreement (h : TableAgreement)
    (i : Fin 5) (w : List (Fin 4)) (x : Fin 306936) :
    (modelEvaluate i w x).val = rawEvaluate i w x.val := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (modelGenerator i a (modelEvaluate i w x)).val =
      rawGenerator i a (rawEvaluate i w x.val)
    rw [h, ih]

/-- Actual carrier words have the numerical action after both comparisons. -/
theorem evaluate_apply_of_tableAgreement
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm) (h : TableAgreement)
    (i : Fin 5) (w : List (Fin 4)) (x : Fin 306936) :
    ((LastFour.evaluate i w).val x).val = rawEvaluate i w x.val := by
  rw [evaluate_val_of_compared_candidates ha hb]
  exact modelEvaluate_apply_of_tableAgreement h i w x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
