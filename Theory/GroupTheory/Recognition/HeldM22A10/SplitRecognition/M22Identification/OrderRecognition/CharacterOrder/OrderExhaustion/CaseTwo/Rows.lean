module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints

/-!
# Signed character constraints for Janko's second decomposition

Orthogonality identifies the first three exceptional multiplicities of all six
characters. Multiplying each row by its character sign gives fixed initial
columns, integral signed degrees and values, and unit final multiplicities.
Restriction to the actual Sylow two-group gives the signed degree congruence.

The third decomposition has coefficients `s₀, -s₃, s₅`. Evaluation at the
identity and involution and the Suzuki formula give three exact equations.
Clearing nonzero degrees produces an integer identity. The small-ratio
inequalities then imply the inclusive cofactor bound `h ≤ 55`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

open scoped BigOperators
open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

private theorem scalar_irreducible {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) :
    scalarProduct G χ ψ = if χ = ψ then 1 else 0 := by
  classical
  have hc : scalarProduct G χ ψ = characterProduct G χ ψ := by
    obtain ⟨n, ρ, _, rfl⟩ := hψ
    simp only [scalarProduct, characterProduct,
      Representation.representation_character_inv_eq_star_character]
  rw [hc]
  split_ifs with h
  · subst ψ
    exact irreducibleCharacter_self hχ
  · exact irreducibleCharacters_orthogonal hχ hψ h

private theorem signed_scalar {n : ℕ} (F : SignedFamily G n) (i j : Fin n) :
    scalarProduct G (F.term i) (F.character j) = if i = j then (F.sign i : ℂ) else 0 := by
  classical
  simp only [SignedFamily.term, scalarProduct_smul_left,
    scalar_irreducible (F.irreducible i) (F.irreducible j), F.injective.eq_iff]
  split_ifs <;> simp

private theorem principal_scalar {n : ℕ} (F : SignedFamily G n) (j : Fin n) :
    scalarProduct G 1 (F.character j) = 0 := by
  rw [scalar_irreducible isIrreducibleCharacter_one (F.irreducible j),
    if_neg (Ne.symm (F.nonprincipal j))]

/-- The fixed first three columns after normalizing each character by its sign. -/
@[expose] public def caseTwoBase : Fin 6 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![1, 0, 0], ![1, 0, 0], ![0, 1, -1], ![0, 1, 0], ![0, 0, 1]]

/-- The actual degree multiplied by the family sign. -/
@[expose] public def caseTwoSignedDegree (F : SignedFamily G 6) (j : Fin 6) : ℤ :=
  F.sign j * (F.irreducible j).degree

/-- The actual integral involution value multiplied by the family sign. -/
@[expose] public def caseTwoSignedValue {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6) (j : Fin 6) : ℤ :=
  F.sign j * involutionValue I (F.irreducible j)

/-- An actual exceptional multiplicity multiplied by the family sign. -/
@[expose] public def caseTwoSignedMultiplicity {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6) (j : Fin 6) (i : Fin 5) : ℤ :=
  F.sign j * multiplicities I (F.irreducible j) i

/-- Orthogonality recovers the fixed columns from the three supplied decompositions. -/
public theorem caseTwo_base_multiplicities {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5)
    (j : Fin 6) (i : Fin 3) :
    caseTwoSignedMultiplicity I F j i.castSucc.castSucc = caseTwoBase j i := by
  have he (r : Fin 5) := multiplicities_scalarProduct I (F.irreducible j) r
  have h0 := he 0
  have h1' := he 1
  have h2' := he 2
  rw [h1] at h0
  rw [h2] at h1'
  rw [h3] at h2'
  simp only [scalarProduct_add_left, scalarProduct_sub_left, signed_scalar, principal_scalar] at h0 h1' h2'
  have hm : multiplicities I (F.irreducible j) i.castSucc.castSucc =
      F.sign j * caseTwoBase j i := by
    fin_cases j <;> fin_cases i <;> norm_num [caseTwoBase, Fin.ext_iff] at h0 h1' h2' ⊢ <;>
      first | exact_mod_cast h0.symm | exact_mod_cast h1'.symm | exact_mod_cast h2'.symm
  have hs : F.sign j * F.sign j = 1 := by
    rcases F.sign_eq j with hs | hs <;> simp [hs]
  rw [caseTwoSignedMultiplicity, hm, ← mul_assoc, hs, one_mul]


/-- Signed unit multiplicities still lie between minus one and one. -/
public theorem caseTwo_signedMultiplicity_unit {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6) (j : Fin 6) (i : Fin 5) :
    caseTwoSignedMultiplicity I F j i ∈ ([-1, 0, 1] : List ℤ) := by
  rcases F.sign_eq j with hs | hs <;>
    rcases multiplicities_unit I hu (F.irreducible j) i with hc | hc | hc <;>
    simp [caseTwoSignedMultiplicity, hs, hc]

/-- Signed degrees remain nonzero divisors of the group order. -/
public theorem caseTwo_signedDegree_dvd (F : SignedFamily G 6) (j : Fin 6) :
    caseTwoSignedDegree F j ≠ 0 ∧ caseTwoSignedDegree F j ∣ (Nat.card G : ℤ) := by
  have hp := (F.irreducible j).degree_pos
  have hd := (F.irreducible j).degree_dvd_card
  rcases F.sign_eq j with hs | hs <;>
    simp only [caseTwoSignedDegree, hs, one_mul, neg_one_mul, neg_ne_zero, neg_dvd] <;>
    exact_mod_cast (show (F.irreducible j).degree ≠ 0 ∧ (F.irreducible j).degree ∣ Nat.card G
      from ⟨hp.ne', hd⟩)

omit [Finite G] in
/-- The signed degree has the actual degree as its absolute value. -/
public theorem caseTwo_signedDegree_natAbs (F : SignedFamily G 6) (j : Fin 6) :
    (caseTwoSignedDegree F j).natAbs = (F.irreducible j).degree := by
  rcases F.sign_eq j with hs | hs <;> simp [caseTwoSignedDegree, hs]

/-- Normalize all five integer columns by the sign of the irreducible. -/
public theorem caseTwo_signedValue_formula {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (F : SignedFamily G 6) (j : Fin 6) :
    caseTwoSignedValue I F j = 7 * caseTwoSignedMultiplicity I F j 0 -
      6 * caseTwoSignedMultiplicity I F j 1 + caseTwoSignedMultiplicity I F j 2 +
      8 * caseTwoSignedMultiplicity I F j 3 + 3 * caseTwoSignedMultiplicity I F j 4 := by
  simp only [caseTwoSignedValue, involutionValue, columnValue, Matrix.cons_val_zero,
    caseTwoSignedMultiplicity]
  ring

/-- Restriction to the Sylow two-group also gives a congruence for signed degrees. -/
public theorem caseTwo_signedDegree_congruence {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (F : SignedFamily G 6) (j : Fin 6) :
    (128 : ℤ) ∣ caseTwoSignedDegree F j + 153 * caseTwoSignedMultiplicity I F j 0 -
      202 * caseTwoSignedMultiplicity I F j 1 + 127 * caseTwoSignedMultiplicity I F j 2 +
      280 * caseTwoSignedMultiplicity I F j 3 + 45 * caseTwoSignedMultiplicity I F j 4 := by
  have hd := degree_congruence_mod128 D k L I (F.irreducible j)
    (multiplicities I (F.irreducible j)) (multiplicities_values I (F.irreducible j))
  simp only [caseTwoSignedDegree, caseTwoSignedMultiplicity]
  convert dvd_mul_of_dvd_right hd (F.sign j) using 1 <;> first | rfl | ring

/-- The signs used for involution values give the same signed Suzuki summands. -/
public theorem caseTwo_signedRatio {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (F : SignedFamily G 6) (j : Fin 6) :
    (caseTwoSignedValue I F j : ℚ)^2 / caseTwoSignedDegree F j =
      (F.sign j : ℚ) * involutionRatio I (F.irreducible j) := by
  rcases F.sign_eq j with hs | hs <;>
    simp [caseTwoSignedValue, caseTwoSignedDegree, involutionRatio, hs, div_neg]

/-- Evaluating the third decomposition at the identity retains the minus sign. -/
public theorem caseTwo_third_degree {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    1 + caseTwoSignedDegree F 0 - caseTwoSignedDegree F 3 + caseTwoSignedDegree F 5 = 0 := by
  have hh := congrFun h3 1
  rw [show I.induced 2 1 = 0 from I.degree_zero 2] at hh
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
    smul_eq_mul, (F.irreducible _).degree_eq] at hh
  simp only [caseTwoSignedDegree]
  exact_mod_cast hh.symm

/-- Evaluating the third decomposition at the involution gives the value relation. -/
public theorem caseTwo_third_value {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    1 + caseTwoSignedValue I F 0 - caseTwoSignedValue I F 3 + caseTwoSignedValue I F 5 = 16 := by
  have hh := congrFun h3 D.z
  have hz : I.induced 2 D.z = 16 := by
    simpa [SpecialInductionData.induced, specialRepresentative, CaseII.into_z_zero,
      exceptionalValues] using I.values 2 0
  rw [hz] at hh
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
    smul_eq_mul, involutionValue_eq I (F.irreducible _)] at hh
  simp only [caseTwoSignedValue]
  exact_mod_cast hh.symm

/-- The third Suzuki identity in case (2), including the negative middle coefficient. -/
public theorem caseTwo_third_suzuki (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    (Nat.card G : ℚ) / 147456 *
      (1 + (F.sign 0 : ℚ) * involutionRatio I (F.irreducible 0) -
        (F.sign 3 : ℚ) * involutionRatio I (F.irreducible 3) +
        (F.sign 5 : ℚ) * involutionRatio I (F.irreducible 5)) = 91 / 12 := by
  let χ : Fin 4 → ClassFunction G := ![1, F.character 0, F.character 3, F.character 5]
  have hc : ∀ i, IsIrreducibleCharacter (χ i) := by
    intro i
    fin_cases i
    · exact isIrreducibleCharacter_one
    · exact F.irreducible 0
    · exact F.irreducible 3
    · exact F.irreducible 5
  have he : I.induced 2 = ∑ i : Fin 4,
      (![1, F.sign 0, -F.sign 3, F.sign 5] i : ℂ) • χ i := by
    simpa [χ, Fin.sum_univ_succ, SignedFamily.term, sub_eq_add_neg, add_assoc] using h3
  have hh := suzukiOrder_identity D k L I hI χ hc
    (fun i => (![1, F.sign 0, -F.sign 3, F.sign 5] i : ℂ)) 2 he
  simp only [Fin.sum_univ_succ, χ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Pi.one_apply, Int.cast_one, one_pow, mul_one, div_one, pairingConstants] at hh
  simp_rw [involutionValue_eq I (F.irreducible _), (F.irreducible _).degree_eq] at hh
  apply Rat.cast_injective (α := ℂ)
  push_cast
  simpa [involutionRatio, mul_div_assoc, sub_eq_add_neg, add_assoc, neg_div] using hh

/-- Clear the actual nonzero degrees in the third Suzuki equation. -/
public theorem caseTwo_third_suzuki_int (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    let x := caseTwoSignedDegree F 0
    let y := caseTwoSignedDegree F 3
    let z := caseTwoSignedDegree F 5
    let a := caseTwoSignedValue I F 0
    let b := caseTwoSignedValue I F 3
    let c := caseTwoSignedValue I F 5
    (Nat.card G : ℤ) * (x*y*z + a^2*y*z - b^2*x*z + c^2*x*y) = 1118208*x*y*z := by
  dsimp only
  have hh := caseTwo_third_suzuki D k L I hI F h3
  rw [← caseTwo_signedRatio I F 0, ← caseTwo_signedRatio I F 3,
    ← caseTwo_signedRatio I F 5] at hh
  have hx : (caseTwoSignedDegree F 0 : ℚ) ≠ 0 := by
    exact_mod_cast (caseTwo_signedDegree_dvd F 0).1
  have hy : (caseTwoSignedDegree F 3 : ℚ) ≠ 0 := by
    exact_mod_cast (caseTwo_signedDegree_dvd F 3).1
  have hz : (caseTwoSignedDegree F 5 : ℚ) ≠ 0 := by
    exact_mod_cast (caseTwo_signedDegree_dvd F 5).1
  field_simp at hh
  have hi : (Nat.card G : ℚ) *
      ((caseTwoSignedDegree F 0 : ℚ) * caseTwoSignedDegree F 3 * caseTwoSignedDegree F 5 +
      (caseTwoSignedValue I F 0 : ℚ)^2 * caseTwoSignedDegree F 3 * caseTwoSignedDegree F 5 -
      (caseTwoSignedValue I F 3 : ℚ)^2 * caseTwoSignedDegree F 0 * caseTwoSignedDegree F 5 +
      (caseTwoSignedValue I F 5 : ℚ)^2 * caseTwoSignedDegree F 0 * caseTwoSignedDegree F 3) =
      1118208 * caseTwoSignedDegree F 0 * caseTwoSignedDegree F 3 * caseTwoSignedDegree F 5 := by
    nlinarith [hh]
  exact_mod_cast hi



/-- The first two degree-zero relations, with signed degrees. -/
public theorem caseTwo_first_two_degrees {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4) :
    caseTwoSignedDegree F 0 + caseTwoSignedDegree F 1 + caseTwoSignedDegree F 2 = 0 ∧
    caseTwoSignedDegree F 0 + caseTwoSignedDegree F 3 + caseTwoSignedDegree F 4 = 0 := by
  have hz1 := congrFun h1 1
  have hz2 := congrFun h2 1
  rw [show I.induced 0 1 = 0 from I.degree_zero 0] at hz1
  rw [show I.induced 1 1 = 0 from I.degree_zero 1] at hz2
  simp only [Pi.add_apply, SignedFamily.term, Pi.smul_apply, smul_eq_mul,
    (F.irreducible _).degree_eq] at hz1 hz2
  simp only [caseTwoSignedDegree]
  exact ⟨by exact_mod_cast hz1.symm, by exact_mod_cast hz2.symm⟩

/-- The first two involution-value relations, with the same family signs. -/
public theorem caseTwo_first_two_values {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4) :
    caseTwoSignedValue I F 0 + caseTwoSignedValue I F 1 + caseTwoSignedValue I F 2 = 16 ∧
    caseTwoSignedValue I F 0 + caseTwoSignedValue I F 3 + caseTwoSignedValue I F 4 = 0 := by
  have hz1 := congrFun h1 D.z
  have hz2 := congrFun h2 D.z
  have hv0 : I.induced 0 D.z = 16 := by
    simpa [SpecialInductionData.induced, specialRepresentative, CaseII.into_z_zero,
      exceptionalValues] using I.values 0 0
  have hv1 : I.induced 1 D.z = 0 := by
    simpa [SpecialInductionData.induced, specialRepresentative, CaseII.into_z_zero,
      exceptionalValues] using I.values 1 0
  rw [hv0] at hz1
  rw [hv1] at hz2
  simp only [Pi.add_apply, SignedFamily.term, Pi.smul_apply, smul_eq_mul,
    involutionValue_eq I (F.irreducible _)] at hz1 hz2
  simp only [caseTwoSignedValue]
  exact ⟨by exact_mod_cast hz1.symm, by exact_mod_cast hz2.symm⟩

/-- The first rational Suzuki identity for the second decomposition. -/
public theorem caseTwo_first_suzuki (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2) :
    (Nat.card G : ℚ) / 147456 *
      ((F.sign 0 : ℚ) * involutionRatio I (F.irreducible 0) +
        (F.sign 1 : ℚ) * involutionRatio I (F.irreducible 1) +
        (F.sign 2 : ℚ) * involutionRatio I (F.irreducible 2)) = 31/12 := by
  let χ : Fin 3 → ClassFunction G := ![F.character 0, F.character 1, F.character 2]
  have hc : ∀ i, IsIrreducibleCharacter (χ i) := by
    intro i
    fin_cases i
    · exact F.irreducible 0
    · exact F.irreducible 1
    · exact F.irreducible 2
  have he : I.induced 0 = ∑ i : Fin 3,
      (![F.sign 0, F.sign 1, F.sign 2] i : ℂ) • χ i := by
    simpa [χ, Fin.sum_univ_succ, SignedFamily.term, add_assoc] using h1
  simpa [χ, Fin.sum_univ_succ, pairingConstants, add_assoc] using
    suzukiOrder_identity_rat D k L I hI χ hc ![F.sign 0, F.sign 1, F.sign 2] 0 he

/-- The second rational Suzuki identity for the second decomposition. -/
public theorem caseTwo_second_suzuki (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4) :
    (Nat.card G : ℚ) / 147456 *
      ((F.sign 0 : ℚ) * involutionRatio I (F.irreducible 0) +
        (F.sign 3 : ℚ) * involutionRatio I (F.irreducible 3) +
        (F.sign 4 : ℚ) * involutionRatio I (F.irreducible 4)) = -1 := by
  let χ : Fin 3 → ClassFunction G := ![F.character 0, F.character 3, F.character 4]
  have hc : ∀ i, IsIrreducibleCharacter (χ i) := by
    intro i
    fin_cases i
    · exact F.irreducible 0
    · exact F.irreducible 3
    · exact F.irreducible 4
  have he : I.induced 1 = ∑ i : Fin 3,
      (![F.sign 0, F.sign 3, F.sign 4] i : ℂ) • χ i := by
    simpa [χ, Fin.sum_univ_succ, SignedFamily.term, add_assoc] using h2
  simpa [χ, Fin.sum_univ_succ, pairingConstants, add_assoc] using
    suzukiOrder_identity_rat D k L I hI χ hc ![F.sign 0, F.sign 3, F.sign 4] 1 he

/-- The three small-ratio inequalities in case (2) imply the inclusive cofactor bound. -/
public theorem caseTwo_smallRatio_cofactor (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5)
    (h0 : involutionRatio I (F.irreducible 0) ≤ 1 / 4)
    (h3r : involutionRatio I (F.irreducible 3) ≤ 1 / 4)
    (h5 : involutionRatio I (F.irreducible 5) ≤ 1 / 4) :
    ∃ h : ℕ, 0 < h ∧ Nat.card G = 40320 * h ∧ ¬ 2 ∣ h ∧ ¬ 3 ∣ h ∧ h ≤ 55 := by
  obtain ⟨h, hp, he, htwo, hthree⟩ := exists_order_cofactor D k L
  refine ⟨h, hp, he, htwo, hthree, ?_⟩
  have h0' := involutionRatio_lt_of_le L I (F.irreducible 0) h0
  have h3' := involutionRatio_lt_of_le L I (F.irreducible 3) h3r
  have h5' := involutionRatio_lt_of_le L I (F.irreducible 5) h5
  have p0 := involutionRatio_nonneg I (F.irreducible 0)
  have p3 := involutionRatio_nonneg I (F.irreducible 3)
  have p5 := involutionRatio_nonneg I (F.irreducible 5)
  have hn0 : (1 : ℤ) ≤ (F.irreducible 0).degree := by exact_mod_cast (F.irreducible 0).degree_pos
  have hn3 : (1 : ℤ) ≤ (F.irreducible 3).degree := by exact_mod_cast (F.irreducible 3).degree_pos
  have hn5 : (1 : ℤ) ≤ (F.irreducible 5).degree := by exact_mod_cast (F.irreducible 5).degree_pos
  have hz := caseTwo_third_degree I F h3
  simp only [caseTwoSignedDegree] at hz
  have hs : (1 / 2 : ℚ) <
      1 + (F.sign 0 : ℚ) * involutionRatio I (F.irreducible 0) -
        (F.sign 3 : ℚ) * involutionRatio I (F.irreducible 3) +
        (F.sign 5 : ℚ) * involutionRatio I (F.irreducible 5) := by
    rcases F.sign_eq 0 with s0 | s0 <;> rcases F.sign_eq 3 with s3 | s3 <;>
      rcases F.sign_eq 5 with s5 | s5 <;>
      simp only [s0, s3, s5, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hz ⊢ <;>
      linarith
  exact cofactor_le55_of_suzuki_sum _ h _ hs he (caseTwo_third_suzuki D k L I hI F h3)

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
