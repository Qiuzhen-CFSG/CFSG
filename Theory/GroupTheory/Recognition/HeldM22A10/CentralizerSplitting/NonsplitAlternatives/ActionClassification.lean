module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Faithfulness
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices

/-!
# Classification of binary S₄ actions with two-element fixed spaces

A two-element Sylow fixed space forces the action to be faithful. After an
actual change of binary basis, the S₃ normalization fixes the action
of `(0 1 2)` and gives one of two actions of `(0 1)`. A finite classification
of the remaining double-transposition matrix then gives four action alternatives.
The assembly transports both fixed-space hypotheses and composes the resulting
basis changes, preserving the same S₄ labels throughout.

`action_cases_of_fixed_card` discharges the two premises of the conditional
reduction using the proved S₃ normalization and exhaustive matrix certificates.
Its only hypotheses are the two fixed-space orders. This is the finite action
classification step toward Huppert–Blackburn, *Finite Groups III*, XII.1.18(b),
p.314; extension splitting and ambient group recognition remain separate
obligations. No complement or additional faithfulness hypothesis is used.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open LocalModelDichotomy

/-- Reduce the four-action conclusion to S₃ normalization and the classification
of actions already in those coordinates. The two additional premises are
discharged in `action_cases_of_fixed_card`. -/
public theorem action_cases_of_s3_reductions
    (α : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, α s v = v} = 2)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, α (s : SymmetricFour) v = v} = 2)
    (hnormalize : Function.Injective α → ∃ e : MulAut BinaryFour,
      changeBasis α e threeCycle = permutationAction threeCycle ∧
      (changeBasis α e transposition = permutationAction transposition ∨
        changeBasis α e transposition = twistedAction transposition))
    (hclassify : ∀ β : SymmetricFour →* MulAut BinaryFour,
      Nat.card {v : BinaryFour // ∀ s : SymmetricFour, β s v = v} = 2 →
      Nat.card {v : BinaryFour // ∀ s : P, β (s : SymmetricFour) v = v} = 2 →
      β threeCycle = permutationAction threeCycle →
      (β transposition = permutationAction transposition ∨
        β transposition = twistedAction transposition) →
      ActionEquivalent β permutationAction ∨ ActionEquivalent β twistedAction ∨
        ActionEquivalent β twelveOrbitAction ∨ ActionEquivalent β sixOrbitAction) :
    ActionEquivalent α permutationAction ∨ ActionEquivalent α twistedAction ∨
      ActionEquivalent α twelveOrbitAction ∨ ActionEquivalent α sixOrbitAction := by
  obtain ⟨e, hethree, hetwo⟩ := hnormalize (action_injective_of_sylow_fixed_card α P hP)
  have he := equivalent_changeBasis α e
  have hfixed' := (he.fixed_card_eq (fun s : SymmetricFour => s)).symm.trans hfixed
  have hP' := (he.fixed_card_eq (fun s : P => (s : SymmetricFour))).symm.trans hP
  rcases hclassify (changeBasis α e) hfixed' hP' hethree hetwo with h | h | h | h
  · exact Or.inl (he.trans h)
  · exact Or.inr (Or.inl (he.trans h))
  · exact Or.inr (Or.inr (Or.inl (he.trans h)))
  · exact Or.inr (Or.inr (Or.inr (he.trans h)))

/-- A binary S₄ action whose full and Sylow fixed spaces both have order two
is equivalent to one of the four explicit actions, through an actual change
of binary basis preserving every S₄ label. -/
public theorem action_cases_of_fixed_card
    (α : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, α s v = v} = 2)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, α (s : SymmetricFour) v = v} = 2) :
    ActionEquivalent α permutationAction ∨ ActionEquivalent α twistedAction ∨
      ActionEquivalent α twelveOrbitAction ∨ ActionEquivalent α sixOrbitAction := by
  exact action_cases_of_s3_reductions α P hfixed hP
    (fun hinj => exists_s3_normalization α hinj hfixed)
    (fun β => action_cases_of_normalized β P)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
