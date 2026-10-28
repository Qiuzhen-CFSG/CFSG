module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices.Enumeration
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices.FixedSpaces
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices.Models
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
/-!
# Classification of binary S₄ actions in normalized S₃ coordinates

Fix the action of `(0 1 2)` to be the permutation matrix and the action of
`(0 1)` to be either the permutation matrix or its parity twist. The S₄
relations constrain the remaining double-transposition matrix. Both supplied
fixed-space orders transfer to finite column counts, using genuine Sylow
conjugacy. The exhaustive certificates leave seven matrices, whose actual
changes of basis give the four published action alternatives with unchanged
S₄ labels.

This proves the independent normalized-action helper used in the local
argument for Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314. The
S₃ normalization and the group-recognition theorem belong to their respective
assembly owners; neither is assumed as a conclusion here.
-/
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
private theorem permutation_x : columns (permutationAction threeCycle) = x := by
  apply lin_injective
  funext v
  rw [lin_columns]
  exact (show ∀ v, permutationAction threeCycle v = lin x v by decide +kernel) v
private theorem permutation_xi : columns (permutationAction threeCycle⁻¹) = xi := by
  apply lin_injective
  funext v
  rw [lin_columns]
  exact (show ∀ v, permutationAction threeCycle⁻¹ v = lin xi v by decide +kernel) v
private theorem permutation_t : columns (permutationAction transposition) = t := by
  apply lin_injective
  funext v
  rw [lin_columns]
  exact (show ∀ v, permutationAction transposition v = lin t v by decide +kernel) v
private theorem twisted_t : columns (twistedAction transposition) = u := by
  apply lin_injective
  funext v
  rw [lin_columns]
  exact (show ∀ v, twistedAction transposition v = lin u v by decide +kernel) v
private theorem matrix_conditions (β : SymmetricFour →* MulAut BinaryFour)
    (P : Sylow 2 SymmetricFour) (T : Cols)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, β s v = v} = 2)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, β (s : SymmetricFour) v = v} = 2)
    (hx : columns (β threeCycle) = x) (hxi : columns (β threeCycle⁻¹) = xi)
    (ht : columns (β transposition) = T) :
    let k := columns (β doubleTransposition)
    rels T k ∧ fixedCount x T k = 2 ∧ fixedCount T k (comp x (comp k xi)) = 2 := by
  dsimp only
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have h : β doubleTransposition * β doubleTransposition = 1 := by
      rw [← map_mul, ← pow_two, doubleTransposition_square, map_one]
    simpa only [columns_mul, columns_one] using congrArg columns h
  · have h := congrArg (fun s => columns (β s)) transposition_commutes_double
    simpa only [map_mul, columns_mul, ht] using h
  · have hrel : doubleTransposition * (threeCycle * (doubleTransposition * threeCycle⁻¹)) =
        threeCycle⁻¹ * (doubleTransposition * threeCycle) := by decide +kernel
    have h := congrArg (fun s => columns (β s)) hrel
    simpa only [map_mul, columns_mul, hx, hxi] using h
  · rw [fixedCount_eq, ← hx, ← ht]
    simp only [lin_columns]
    exact (full_fixed_card β).trans hfixed
  · have hl : columns (β otherDouble) = comp x (comp (columns (β doubleTransposition)) xi) := by
      unfold otherDouble
      rw [mul_assoc]
      simp only [map_mul, columns_mul, hx, hxi]
    rw [fixedCount_eq, ← ht, ← hl]
    simp only [lin_columns]
    exact (sylow_fixed_card β P).trans hP
/-- Two-element full and Sylow fixed spaces leave exactly the four action
alternatives after the explicitly supplied S₃ normalization. -/
public theorem action_cases_of_normalized
    (β : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, β s v = v} = 2)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, β (s : SymmetricFour) v = v} = 2)
    (hthree : β threeCycle = permutationAction threeCycle)
    (htwo : β transposition = permutationAction transposition ∨
      β transposition = twistedAction transposition) :
    ActionEquivalent β permutationAction ∨ ActionEquivalent β twistedAction ∨
      ActionEquivalent β twelveOrbitAction ∨ ActionEquivalent β sixOrbitAction := by
  have hx : columns (β threeCycle) = x := by rw [hthree, permutation_x]
  have hxi : columns (β threeCycle⁻¹) = xi := by
    rw [map_inv, hthree, ← map_inv, permutation_xi]
  rcases htwo with ht | ht
  · have ht' : columns (β transposition) = t := by rw [ht, permutation_t]
    obtain ⟨hr, hf, hs⟩ := matrix_conditions β P t hfixed hP hx hxi ht'
    rcases ordinary_cases (columns (β doubleTransposition)) hr hf hs with hk | hk | hk
    · exact Or.inl (equivalent_row β 0 hx ht' hk)
    · exact Or.inl (equivalent_row β 1 hx ht' hk)
    · exact Or.inl (equivalent_row β 2 hx ht' hk)
  · have ht' : columns (β transposition) = u := by rw [ht, twisted_t]
    obtain ⟨hr, hf, hs⟩ := matrix_conditions β P u hfixed hP hx hxi ht'
    rcases twisted_cases (columns (β doubleTransposition)) hr hf hs with hk | hk | hk | hk
    · exact Or.inr (Or.inl (equivalent_row β 3 hx ht' hk))
    · exact Or.inr (Or.inr (Or.inl (equivalent_row β 4 hx ht' hk)))
    · exact Or.inr (Or.inr (Or.inl (equivalent_row β 5 hx ht' hk)))
    · exact Or.inr (Or.inr (Or.inr (equivalent_row β 6 hx ht' hk)))
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
