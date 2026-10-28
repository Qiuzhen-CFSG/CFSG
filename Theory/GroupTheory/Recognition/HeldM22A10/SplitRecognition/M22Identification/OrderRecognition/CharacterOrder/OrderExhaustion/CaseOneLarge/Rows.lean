module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints

/-!
# Signed rows in the first large-ratio decomposition

The three selected irreducibles are X₂, Z₁ and Z₂. Orthogonality fixes their
first three exceptional multiplicities; the Gram matrix fixes the sums of
the last two columns. Signing their actual degrees and values preserves degree
divisibility and turns the third Suzuki identity into an integer equation.
The Sylow restriction congruence retains every choice of the two free columns.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15. Adapted from the saved first attempt
in workspace a7afbd55db8d4d22803132676c1985c0; every proof is rechecked here.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy
namespace CaseOneLarge
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

private theorem scalarProduct_eq_characterProduct (f : ClassFunction G)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G f χ = characterProduct G f χ := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  simp only [scalarProduct, characterProduct,
    Representation.representation_character_inv_eq_star_character]

private theorem family_scalar (F : SignedFamily G 7) (i j : Fin 7) :
    scalarProduct G (F.term i) (F.character j) = if i = j then (F.sign i : ℂ) else 0 := by
  rw [SignedFamily.term, scalarProduct_smul_left,
    scalarProduct_eq_characterProduct _ (F.irreducible j)]
  by_cases h : i = j
  · subst j
    simp [irreducibleCharacter_self (F.irreducible i)]
  · simp [h, irreducibleCharacters_orthogonal (F.irreducible i) (F.irreducible j)
      (fun he => h (F.injective he))]

private theorem principal_scalar (F : SignedFamily G 7) (j : Fin 7) :
    scalarProduct G 1 (F.character j) = 0 := by
  rw [scalarProduct_eq_characterProduct _ (F.irreducible j)]
  exact irreducibleCharacters_orthogonal isIrreducibleCharacter_one
    (F.irreducible j) (F.nonprincipal j).symm

@[expose] public def selected (j : Fin 3) : Fin 7 :=
  if j = 0 then 1 else if j = 1 then 5 else 6

@[expose] public def signedDegree (F : SignedFamily G 7) (j : Fin 3) : ℤ :=
  F.sign (selected j) * (F.irreducible (selected j)).degree

@[expose] public def signedMultiplicity {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7) (j : Fin 3) (r : Fin 5) : ℤ :=
  F.sign (selected j) * multiplicities I (F.irreducible (selected j)) r

omit [Finite G] in
private theorem sign_sq (F : SignedFamily G 7) (j : Fin 7) : F.sign j * F.sign j = 1 := by
  rcases F.sign_eq j with h | h <;> simp [h]

public theorem firstThree {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) (j : Fin 3) :
    signedMultiplicity I F j 0 = (if j = 0 then 1 else 0) ∧
    signedMultiplicity I F j 1 = 0 ∧ signedMultiplicity I F j 2 = 1 := by
  have ha := congrArg (fun f => scalarProduct G f (F.character (selected j))) h1
  have hb := congrArg (fun f => scalarProduct G f (F.character (selected j))) h2
  have hc := congrArg (fun f => scalarProduct G f (F.character (selected j))) h3
  simp only [scalarProduct_add_left, family_scalar, principal_scalar,
    multiplicities_scalarProduct I (F.irreducible (selected j)), zero_add] at ha hb hc
  have ha' : multiplicities I (F.irreducible (selected j)) 0 =
      (if (0 : Fin 7) = selected j then F.sign 0 else 0) +
      (if (1 : Fin 7) = selected j then F.sign 1 else 0) +
      (if (2 : Fin 7) = selected j then F.sign 2 else 0) := by exact_mod_cast ha
  have hb' : multiplicities I (F.irreducible (selected j)) 1 =
      (if (0 : Fin 7) = selected j then F.sign 0 else 0) +
      (if (3 : Fin 7) = selected j then F.sign 3 else 0) +
      (if (4 : Fin 7) = selected j then F.sign 4 else 0) := by exact_mod_cast hb
  have hc' : multiplicities I (F.irreducible (selected j)) 2 =
      (if (1 : Fin 7) = selected j then F.sign 1 else 0) +
      (if (5 : Fin 7) = selected j then F.sign 5 else 0) +
      (if (6 : Fin 7) = selected j then F.sign 6 else 0) := by exact_mod_cast hc
  simp only [signedMultiplicity, ha', hb', hc']
  fin_cases j <;> simp [selected, sign_sq]

public theorem signedMultiplicity_bounds {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 7) (j : Fin 3) (r : Fin 5) :
    -1 ≤ signedMultiplicity I F j r ∧ signedMultiplicity I F j r ≤ 1 := by
  rcases F.sign_eq (selected j) with hs | hs <;>
    rcases multiplicities_unit I hu (F.irreducible (selected j)) r with hm | hm | hm <;>
    simp [signedMultiplicity, hs, hm]

public theorem signedMultiplicity_sums {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (F : SignedFamily G 7)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) :
    (∑ j, signedMultiplicity I F j 3) = 1 ∧
    (∑ j, signedMultiplicity I F j 4) = -1 := by
  have h (r : Fin 5) :
      scalarProduct G (I.induced r) 1 +
        (multiplicities I (F.irreducible 1) r : ℂ) * F.sign 1 +
        (multiplicities I (F.irreducible 5) r : ℂ) * F.sign 5 +
        (multiplicities I (F.irreducible 6) r : ℂ) * F.sign 6 = exceptionalGram r 2 := by
    have hh := I.gram r 2
    change scalarProduct G (I.induced r) (I.induced 2) = _ at hh
    rw [h3] at hh
    simpa only [scalarProduct_add_right, SignedFamily.term, scalarProduct_smul_right,
      multiplicities_scalarProduct I (F.irreducible 1),
      multiplicities_scalarProduct I (F.irreducible 5),
      multiplicities_scalarProduct I (F.irreducible 6), star_intCast] using hh
  have ha := h 3
  have hb := h 4
  have hp (r : Fin 5) : scalarProduct G (I.induced r) 1 = exceptionalCoefficients r 0 :=
    I.principal_multiplicity r
  rw [hp] at ha hb
  have hp3 : exceptionalCoefficients 3 0 = 0 := by decide +kernel
  have hp4 : exceptionalCoefficients 4 0 = 0 := by decide +kernel
  have hg3 : exceptionalGram 3 2 = 1 := by decide +kernel
  have hg4 : exceptionalGram 4 2 = -1 := by decide +kernel
  simp only [hp3, hg3, Int.cast_zero, Int.cast_one, zero_add] at ha
  simp only [hp4, hg4, Int.cast_zero, Int.cast_neg, Int.cast_one, zero_add] at hb
  constructor
  · have hi : F.sign 1 * multiplicities I (F.irreducible 1) 3 +
        F.sign 5 * multiplicities I (F.irreducible 5) 3 +
        F.sign 6 * multiplicities I (F.irreducible 6) 3 = 1 := by
      exact_mod_cast (show (F.sign 1 : ℂ) * multiplicities I (F.irreducible 1) 3 +
        (F.sign 5 : ℂ) * multiplicities I (F.irreducible 5) 3 +
        (F.sign 6 : ℂ) * multiplicities I (F.irreducible 6) 3 = 1 by
        simpa only [mul_comm] using ha)
    simpa [Fin.sum_univ_succ, selected, signedMultiplicity, add_assoc] using hi
  · have hi : F.sign 1 * multiplicities I (F.irreducible 1) 4 +
        F.sign 5 * multiplicities I (F.irreducible 5) 4 +
        F.sign 6 * multiplicities I (F.irreducible 6) 4 = -1 := by
      exact_mod_cast (show (F.sign 1 : ℂ) * multiplicities I (F.irreducible 1) 4 +
        (F.sign 5 : ℂ) * multiplicities I (F.irreducible 5) 4 +
        (F.sign 6 : ℂ) * multiplicities I (F.irreducible 6) 4 = -1 by
        simpa only [mul_comm] using hb)
    simpa [Fin.sum_univ_succ, selected, signedMultiplicity, add_assoc] using hi

omit [Finite G] in
/-- The signed degree retains the positive degree as its absolute value. -/
public theorem signedDegree_natAbs (F : SignedFamily G 7) (j : Fin 3) :
    (signedDegree F j).natAbs = (F.irreducible (selected j)).degree := by
  rcases F.sign_eq (selected j) with h | h <;> simp [signedDegree, h]

omit [Finite G] in
public theorem signedDegree_ne_zero (F : SignedFamily G 7) (j : Fin 3) :
    signedDegree F j ≠ 0 := by
  have h := (F.irreducible (selected j)).degree_pos
  have he := signedDegree_natAbs F j
  intro hz
  rw [hz] at he
  simp only [Int.natAbs_zero] at he
  omega

public theorem signedDegree_dvd (F : SignedFamily G 7) (j : Fin 3) :
    signedDegree F j ∣ (Nat.card G : ℤ) := by
  have hd : ((F.irreducible (selected j)).degree : ℤ) ∣ (Nat.card G : ℤ) := by
    exact_mod_cast (F.irreducible (selected j)).degree_dvd_card
  rcases F.sign_eq (selected j) with h | h <;> simpa [signedDegree, h] using hd

public theorem signedDegree_sum {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) :
    (∑ j, signedDegree F j) = -1 := by
  have h := congrFun h3 1
  have hz : I.induced 2 1 = 0 := I.degree_zero 2
  rw [hz] at h
  simp only [Pi.add_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
    smul_eq_mul, (F.irreducible _).degree_eq] at h
  have hi : (0 : ℤ) = 1 + F.sign 1 * (F.irreducible 1).degree +
      F.sign 5 * (F.irreducible 5).degree + F.sign 6 * (F.irreducible 6).degree := by
    exact_mod_cast h
  simp [Fin.sum_univ_succ, signedDegree, selected]
  linarith

@[expose] public def signedValue {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7) (j : Fin 3) : ℤ :=
  F.sign (selected j) * involutionValue I (F.irreducible (selected j))

public theorem signedValue_columns {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) (j : Fin 3) :
    signedValue I F j = (if j = 0 then 8 else 1) +
      8 * signedMultiplicity I F j 3 + 3 * signedMultiplicity I F j 4 := by
  obtain ⟨h0, h1', h2'⟩ := firstThree I F h1 h2 h3 j
  have he : signedValue I F j = 7 * signedMultiplicity I F j 0 -
      6 * signedMultiplicity I F j 1 + signedMultiplicity I F j 2 +
      8 * signedMultiplicity I F j 3 + 3 * signedMultiplicity I F j 4 := by
    simp only [signedValue, signedMultiplicity, involutionValue, columnValue,
      Matrix.cons_val_zero]
    ring
  rw [he, h0, h1', h2']
  split_ifs <;> ring

public theorem signedDegree_congruence (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) (j : Fin 3) :
    (128 : ℤ) ∣ signedDegree F j + (if j = 0 then 280 else 127) +
      280 * signedMultiplicity I F j 3 + 45 * signedMultiplicity I F j 4 := by
  obtain ⟨h0, h1', h2'⟩ := firstThree I F h1 h2 h3 j
  have hm := degree_congruence_mod128 D k L I (F.irreducible (selected j))
    (multiplicities I (F.irreducible (selected j)))
    (multiplicities_values I (F.irreducible (selected j)))
  have hs := dvd_mul_of_dvd_right hm (F.sign (selected j))
  have he : F.sign (selected j) *
      ((F.irreducible (selected j)).degree +
        153 * multiplicities I (F.irreducible (selected j)) 0 -
        202 * multiplicities I (F.irreducible (selected j)) 1 +
        127 * multiplicities I (F.irreducible (selected j)) 2 +
        280 * multiplicities I (F.irreducible (selected j)) 3 +
        45 * multiplicities I (F.irreducible (selected j)) 4) =
      signedDegree F j + 153 * signedMultiplicity I F j 0 -
        202 * signedMultiplicity I F j 1 + 127 * signedMultiplicity I F j 2 +
        280 * signedMultiplicity I F j 3 + 45 * signedMultiplicity I F j 4 := by
    simp only [signedDegree, signedMultiplicity]
    ring
  rw [he, h0, h1', h2'] at hs
  obtain ⟨q, hq⟩ := hs
  refine ⟨q, ?_⟩
  split_ifs at hq ⊢ <;> nlinarith [hq]

public theorem signed_ratio {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7) (j : Fin 3) :
    (signedValue I F j : ℚ) ^ 2 / signedDegree F j =
      (F.sign (selected j) : ℚ) * involutionRatio I (F.irreducible (selected j)) := by
  rcases F.sign_eq (selected j) with h | h <;>
    simp [signedValue, signedDegree, involutionRatio, h, div_neg]

public theorem large_signedDegree {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 7) (j : Fin 3)
    (hr : 1 / 4 < involutionRatio I (F.irreducible (selected j))) :
    (signedDegree F j).natAbs < 4 * (signedValue I F j).natAbs ^ 2 := by
  have hp : (0 : ℚ) < (F.irreducible (selected j)).degree := by
    exact_mod_cast (F.irreducible (selected j)).degree_pos
  have he := (lt_div_iff₀ hp).mp hr
  have hd : ((F.irreducible (selected j)).degree : ℚ) <
      4 * (involutionValue I (F.irreducible (selected j)) : ℚ) ^ 2 := by
    linarith
  rw [signedDegree_natAbs]
  have hab : (signedValue I F j).natAbs =
      (involutionValue I (F.irreducible (selected j))).natAbs := by
    rcases F.sign_eq (selected j) with h | h <;> simp [signedValue, h]
  rw [hab]
  have hi : ((F.irreducible (selected j)).degree : ℤ) <
      4 * involutionValue I (F.irreducible (selected j)) ^ 2 := by exact_mod_cast hd
  rw [← Nat.cast_lt (α := ℤ)]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.natCast_natAbs, sq_abs] using hi

/-- Clearing the three genuine positive degrees in the third Suzuki identity. -/
public theorem signed_suzuki_polynomial (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 7)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) :
    (Nat.card G : ℤ) *
      (signedDegree F 0 * signedDegree F 1 * signedDegree F 2 +
       signedValue I F 0 ^ 2 * signedDegree F 1 * signedDegree F 2 +
       signedValue I F 1 ^ 2 * signedDegree F 0 * signedDegree F 2 +
       signedValue I F 2 ^ 2 * signedDegree F 0 * signedDegree F 1) =
      1118208 * signedDegree F 0 * signedDegree F 1 * signedDegree F 2 := by
  have hs := caseOne_third_suzuki D k L I hI F h3
  have hh : (Nat.card G : ℚ) / 147456 *
      (1 + (signedValue I F 0 : ℚ) ^ 2 / signedDegree F 0 +
        (signedValue I F 1 : ℚ) ^ 2 / signedDegree F 1 +
        (signedValue I F 2 : ℚ) ^ 2 / signedDegree F 2) = 91 / 12 := by
    simpa [signed_ratio, selected] using hs
  have hn (j : Fin 3) : (signedDegree F j : ℚ) ≠ 0 := by
    exact_mod_cast signedDegree_ne_zero F j
  have he : (Nat.card G : ℚ) *
      ((signedDegree F 0 : ℚ) * signedDegree F 1 * signedDegree F 2 +
       (signedValue I F 0 : ℚ) ^ 2 * signedDegree F 1 * signedDegree F 2 +
       (signedValue I F 1 : ℚ) ^ 2 * signedDegree F 0 * signedDegree F 2 +
       (signedValue I F 2 : ℚ) ^ 2 * signedDegree F 0 * signedDegree F 1) =
      1118208 * signedDegree F 0 * signedDegree F 1 * signedDegree F 2 := by
    field_simp [hn] at hh
    nlinarith [hh]
  exact_mod_cast he

end
end CaseOneLarge
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
