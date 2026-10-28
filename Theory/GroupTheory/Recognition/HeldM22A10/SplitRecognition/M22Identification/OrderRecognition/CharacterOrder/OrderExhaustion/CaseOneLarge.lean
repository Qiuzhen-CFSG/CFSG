module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneLarge.Rows
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneLarge.Arithmetic

/-!
# Every large-ratio branch of Janko's first decomposition

For X₂, Z₁ and Z₂, actual character orthogonality and the exceptional Gram
matrix fix the initial multiplicities and the sums of the final two signed
columns. Their actual degrees divide the group order, satisfy the Sylow
restriction congruence, and obey the third Suzuki equation.

The arithmetic development proves that these constraints are incompatible
with any of the three ratios exceeding one quarter. It covers every sign,
all 36 pairs of final-column patterns, and all selected constituents. The
integer system used in the proof is constructed here from the supplied
characters and local data; the theorem has no additional arithmetic premise.
The requested order conclusion follows in every large-ratio branch.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15. The source prints only one example;
the complete elimination is supplied in the descendant modules.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy CaseOneLarge
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- The actual characters supply every premise of the exhaustive integer argument. -/
private def largeCaseData (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6)
    (hr : 1/4 < involutionRatio I (F.irreducible 1) ∨
      1/4 < involutionRatio I (F.irreducible 5) ∨
      1/4 < involutionRatio I (F.irreducible 6)) : LargeCaseData (Nat.card G : ℤ) where
  degree := signedDegree F
  fourth := fun j => signedMultiplicity I F j 3
  fifth := fun j => signedMultiplicity I F j 4
  fourth_bounds := fun j => signedMultiplicity_bounds I hu F j 3
  fifth_bounds := fun j => signedMultiplicity_bounds I hu F j 4
  fourth_sum := (signedMultiplicity_sums I F h3).1
  fifth_sum := (signedMultiplicity_sums I F h3).2
  degree_ne_zero := signedDegree_ne_zero F
  degree_sum := signedDegree_sum I F h3
  degree_dvd := signedDegree_dvd F
  degree_congruence := signedDegree_congruence D k L I F h1 h2 h3
  large := by
    have ht (j : Fin 3) : tripleValue
        (fun j => signedMultiplicity I F j 3) (fun j => signedMultiplicity I F j 4) j =
        signedValue I F j := (signedValue_columns I F h1 h2 h3 j).symm
    rcases hr with h | h | h
    · refine ⟨0, ?_⟩
      rw [ht]
      exact large_signedDegree I F 0 (by simpa [selected] using h)
    · refine ⟨1, ?_⟩
      rw [ht]
      exact large_signedDegree I F 1 (by simpa [selected] using h)
    · refine ⟨2, ?_⟩
      rw [ht]
      exact large_signedDegree I F 2 (by simpa [selected] using h)
  suzuki := by
    have ht : tripleValue (fun j => signedMultiplicity I F j 3)
        (fun j => signedMultiplicity I F j 4) = signedValue I F := by
      funext j
      exact (signedValue_columns I F h1 h2 h3 j).symm
    rw [ht]
    exact signed_suzuki_polynomial D k L I hI F h3

/-- Janko's first decomposition has the Mathieu order in every large-ratio branch. -/
public theorem card_eq_443520_caseOne_large [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6)
    (hr : 1/4 < involutionRatio I (F.irreducible 1) ∨
      1/4 < involutionRatio I (F.irreducible 5) ∨
      1/4 < involutionRatio I (F.irreducible 6)) : Nat.card G = 443520 := by
  obtain ⟨h, hp, hg, htwo, hthree⟩ := exists_order_cofactor D k L
  have hg' : (Nat.card G : ℤ) = 40320*(h : ℤ) := by exact_mod_cast hg
  have hdiv : (Nat.card G : ℤ) / 40320 = h := by omega
  have htwo' : ¬ (2 : ℤ) ∣ (Nat.card G : ℤ) / 40320 := by
    rw [hdiv]; exact_mod_cast htwo
  have hthree' : ¬ (3 : ℤ) ∣ (Nat.card G : ℤ) / 40320 := by
    rw [hdiv]; exact_mod_cast hthree
  exact False.elim (largeCaseData_impossible (Nat.card G)
    (largeCaseData D k L I hI hu F h1 h2 h3 hr)
    (by exact_mod_cast Nat.card_pos (α := G)) ⟨h, hg'⟩ htwo' hthree')

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
