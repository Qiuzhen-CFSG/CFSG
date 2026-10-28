module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthMultiplicity.Support

/-!
# Gram restrictions on the double constituent

Orthogonality makes both constituents of the nonunit fourth induction absent
from the first induction. Unit coordinates in the other three rows leave two
choices per row. The second row either has the first source pattern, or the
third and fifth rows are forced to the last source pattern. Three short integer
linear combinations exclude all remaining cases: after removing the principal
and the two selected coordinates their squared norms would be negative.

The involution-column lemma recovers actual signed character values from these
coordinates. No degree, order, or identification is assumed.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, pp.12–13. The Gram inequalities replace the
middle branch's longer support and Sylow-two argument.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy SignedAnalysis.DecompositionSupports
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SignedAnalysis.FourthMultiplicity
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} {E : IntegralExpansion I}

public theorem row_unit {n : ℕ} (F : Frame E n) (L : LocalAnalysisData D k)
    (hI : HasSuzukiPairings I) (i : Fin 5) (hi : i ≠ 3) (r : Fin n) :
    F.coeff i r = 0 ∨ F.coeff i r = 1 ∨ F.coeff i r = -1 := by
  have hu : E.coefficient i (F.index r) = 0 ∨ E.coefficient i (F.index r) = 1 ∨
      E.coefficient i (F.index r) = -1 := by
    by_cases h : i < 3
    · exact E.first_three_unit i h _
    · have he : i = 4 := by omega
      subst i
      exact E.fifth_unit D k L I hI _
  rcases F.sign_eq r with hs | hs <;> rcases hu with h | h | h <;>
    simp [Frame.coeff, hs, h]

public theorem involution_column {n : ℕ} (F : Frame E n) (r : Fin n) :
    F.family.term r D.z =
      ((7 * F.coeff 0 r - 6 * F.coeff 1 r + F.coeff 2 r +
        8 * F.coeff 3 r + 3 * F.coeff 4 r : ℤ) : ℂ) := by
  have h := E.columns (F.index r) 0
  simp only [specialRepresentative, Matrix.cons_val_zero, CaseII.into_z_zero,
    columnValue] at h
  have h' := congrArg (fun z : ℂ => (F.sign r : ℂ) * z) h
  change F.family.term r D.z = _ at h'
  rw [h']
  simp only [Frame.coeff, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

public theorem fourth_gram (F : Frame E 2)
    (he : I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1) (i : Fin 5) :
    F.coeff i 0 + 2 * F.coeff i 1 = exceptionalGram i 3 := by
  have h := I.gram i 3
  change scalarProduct G (I.induced i) (I.induced 3) = _ at h
  rw [he, scalarProduct_add_right, scalarProduct_smul_right,
    F.multiplicity, F.multiplicity] at h
  norm_num only [star_ofNat] at h
  have h' : ((F.coeff i 0 + 2 * F.coeff i 1 : ℤ) : ℂ) =
      (exceptionalGram i 3 : ℂ) := by push_cast; linear_combination h
  exact_mod_cast h'

public theorem first_absent (F : Frame E 2) (L : LocalAnalysisData D k)
    (hI : HasSuzukiPairings I)
    (he : I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1) :
    F.coeff 0 = ![0,0] := by
  have h : F.coeff 0 0 + 2 * F.coeff 0 1 = 0 := fourth_gram F he 0
  have hu0 := row_unit F L hI 0 (by decide) 0
  have hu1 := row_unit F L hI 0 (by decide) 1
  have hz : F.coeff 0 0 = 0 ∧ F.coeff 0 1 = 0 := by omega
  ext r
  fin_cases r <;> simp [hz.1, hz.2]

private theorem pair_one (a : Fin 2 → ℤ)
    (hu : ∀ r, a r = 0 ∨ a r = 1 ∨ a r = -1) (h : a 0 + 2 * a 1 = 1) :
    a = ![-1,1] ∨ a = ![1,0] := by
  have h0 := hu 0
  have h1 := hu 1
  have he : (a 0 = -1 ∧ a 1 = 1) ∨ (a 0 = 1 ∧ a 1 = 0) := by omega
  rcases he with he | he
  · left; ext r; fin_cases r <;> simp [he.1, he.2]
  · right; ext r; fin_cases r <;> simp [he.1, he.2]

private theorem pair_neg_one (a : Fin 2 → ℤ)
    (hu : ∀ r, a r = 0 ∨ a r = 1 ∨ a r = -1) (h : a 0 + 2 * a 1 = -1) :
    a = ![1,-1] ∨ a = ![-1,0] := by
  have h0 := hu 0
  have h1 := hu 1
  have he : (a 0 = 1 ∧ a 1 = -1) ∨ (a 0 = -1 ∧ a 1 = 0) := by omega
  rcases he with he | he
  · left; ext r; fin_cases r <;> simp [he.1, he.2]
  · right; ext r; fin_cases r <;> simp [he.1, he.2]

public theorem remaining_patterns (F : Frame E 2) (L : LocalAnalysisData D k)
    (hI : HasSuzukiPairings I)
    (he : I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1) :
    F.coeff 1 = ![-1,1] ∨
      (F.coeff 1 = ![1,0] ∧ F.coeff 2 = ![-1,1] ∧ F.coeff 4 = ![1,-1]) := by
  have h0 := first_absent F L hI he
  have h1 := pair_one (F.coeff 1) (row_unit F L hI 1 (by decide)) (fourth_gram F he 1)
  have h2 := pair_one (F.coeff 2) (row_unit F L hI 2 (by decide)) (fourth_gram F he 2)
  have h4 := pair_neg_one (F.coeff 4) (row_unit F L hI 4 (by decide)) (fourth_gram F he 4)
  rcases h1 with h1 | h1
  · exact Or.inl h1
  right
  rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
  · exact ⟨h1, h2, h4⟩
  · have hb := combination_norm_le F ![0,-1,1,0,1]
    norm_num [h0, h1, h2, h4, exceptionalCoefficients, exceptionalGram,
      Fin.sum_univ_succ, Fin.reduceFinMk] at hb
    change 1 + ((-1 + (-1 + F.coeff 4 0)) ^ 2 + (1 + F.coeff 4 1) ^ 2) ≤ 8 at hb
    norm_num [h4] at hb
  · have hb := combination_norm_le F ![-1,1,2,0,1]
    norm_num [h0, h1, h2, h4, exceptionalCoefficients, exceptionalGram,
      Fin.sum_univ_succ, Fin.reduceFinMk] at hb
    change 4 + ((1 + (2 + F.coeff 4 0)) ^ 2 + F.coeff 4 1 ^ 2) ≤ 19 at hb
    norm_num [h4] at hb
  · have hb := combination_norm_le F ![-1,2,1,0,-1]
    norm_num [h0, h1, h2, h4, exceptionalCoefficients, exceptionalGram,
      Fin.sum_univ_succ, Fin.reduceFinMk] at hb
    change 1 + ((2 + (1 + -F.coeff 4 0)) ^ 2 + F.coeff 4 1 ^ 2) ≤ 16 at hb
    norm_num [h4] at hb

end SignedAnalysis.FourthMultiplicity
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
