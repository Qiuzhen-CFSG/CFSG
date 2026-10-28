module
public import ABG.Recognition.ThreeDegreeTwoCharacter
public import ABG.Recognition.ThreeBorelPermutationCharacter
public import ABG.Recognition.ThreeFaithfulCharacters
public import Theory.SpecificGroups.GL2.ThreeClassFunctions

/-!
# The complete GL₂(3) table and Wong's supported character lattice

All eight rows are characters of the actual matrix group, constructed from
linear characters, induction, and determinant twists. Their values and the
eight conjugacy classes establish completeness. The three equations for
vanishing off the roots of the central involution give Wong's five integral
generators. Their Gram matrix and the resulting vanishing criterion are
computed using the conjugacy-class scalar-product formula.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2 (1964), Table 1 p.97 and equation (2) p.98,
DOI:10.1017/S1446788700022771.
-/

open Matrix Matrix.GeneralLinearGroup BenderGlauberman
open scoped BigOperators
namespace ABG
noncomputable section
local notation "G" => GL (Fin 2) (ZMod 3)

/-- Wong's row φ₃ is the determinant twist of the degree-three Borel row. -/
public def glTwoThreeBorelTwistCharacter : ClassFunction G :=
  glTwoThreeDeterminantCharacter * glTwoThreeBorelPermutationCharacter

public theorem glTwoThreeBorelTwistCharacter_irreducible :
    IsIrreducibleCharacter glTwoThreeBorelTwistCharacter :=
  isIrreducibleCharacter_mul_linear glTwoThreeDeterminantCharacter_isLinear
    glTwoThreeBorelPermutationCharacter_irreducible

public theorem glTwoThreeBorelTwistCharacter_values (i : Fin 8) :
    glTwoThreeBorelTwistCharacter (threeClassRepr i) = ![3,3,-1,0,0,-1,1,1] i := by
  change glTwoThreeDeterminantCharacter (threeClassRepr i) *
    glTwoThreeBorelPermutationCharacter (threeClassRepr i) = _
  rw [glTwoThreeDeterminantCharacter_values, glTwoThreeBorelPermutationCharacter_values]
  fin_cases i <;> norm_num

/-- The eight actual irreducible characters in Wong's indexing φ₀,…,φ₇. -/
@[expose] public def glTwoThreeCharacter (i : Fin 8) : ClassFunction G :=
  ![1, glTwoThreeDeterminantCharacter, glTwoThreeDegreeTwoCharacter,
    glTwoThreeBorelTwistCharacter, glTwoThreeBorelPermutationCharacter,
    glTwoThreeDegreeFourCharacter, glTwoThreeFaithfulCharacter,
    glTwoThreeFaithfulTwistCharacter] i

public theorem glTwoThreeCharacter_irreducible (i : Fin 8) :
    IsIrreducibleCharacter (glTwoThreeCharacter i) := by
  fin_cases i
  · exact isLinearCharacter_one.1
  · exact glTwoThreeDeterminantCharacter_isLinear.1
  · exact glTwoThreeDegreeTwoCharacter_irreducible
  · exact glTwoThreeBorelTwistCharacter_irreducible
  · exact glTwoThreeBorelPermutationCharacter_irreducible
  · exact glTwoThreeDegreeFourCharacter_irreducible
  · exact glTwoThreeFaithfulCharacter_irreducible
  · exact glTwoThreeFaithfulTwistCharacter_irreducible

/-- Wong's Table 1, with the chosen algebraic square root of -2. -/
@[expose] public def glTwoThreeCharacterTable : Matrix (Fin 8) (Fin 8) ℂ :=
  ![![1,1,1,1,1,1,1,1], ![1,1,1,1,1,-1,-1,-1], ![2,2,2,-1,-1,0,0,0],
    ![3,3,-1,0,0,-1,1,1], ![3,3,-1,0,0,1,-1,-1], ![4,-4,0,1,-1,0,0,0],
    ![2,-2,0,-1,1,0,glTwoThreeOmega,-glTwoThreeOmega],
    ![2,-2,0,-1,1,0,-glTwoThreeOmega,glTwoThreeOmega]]

public theorem glTwoThreeCharacter_values (i j : Fin 8) :
    glTwoThreeCharacter i (threeClassRepr j) = glTwoThreeCharacterTable i j := by
  fin_cases i
  · fin_cases j <;> rfl
  · exact glTwoThreeDeterminantCharacter_values j
  · exact glTwoThreeDegreeTwoCharacter_values j
  · exact glTwoThreeBorelTwistCharacter_values j
  · exact glTwoThreeBorelPermutationCharacter_values j
  · exact glTwoThreeDegreeFourCharacter_values j
  · exact glTwoThreeFaithfulCharacter_values j
  · exact glTwoThreeFaithfulTwistCharacter_values j

private theorem row_class (i : Fin 8) : IsClassFunction (glTwoThreeCharacter i) :=
  irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i)

public theorem glTwoThreeCharacter_orthonormal (i j : Fin 8) :
    scalarProduct G (glTwoThreeCharacter i) (glTwoThreeCharacter j) = if i = j then 1 else 0 := by
  rw [three_scalarProduct _ _ (row_class i) (row_class j)]
  simp_rw [glTwoThreeCharacter_values]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, glTwoThreeCharacterTable, glTwoThreeOmega_star,
      ← pow_two, glTwoThreeOmega_sq] <;>
    simp only [starRingEnd_apply, star_ofNat, glTwoThreeOmega_star] <;>
    ring_nf <;> norm_num [glTwoThreeOmega_sq]

public theorem glTwoThreeCharacter_injective : Function.Injective glTwoThreeCharacter := by
  intro i j h
  by_contra hij
  have hsp := glTwoThreeCharacter_orthonormal i j
  rw [if_neg hij, h, glTwoThreeCharacter_orthonormal] at hsp
  norm_num at hsp

private def conjEquiv : Fin 8 ≃ ConjClasses G := Equiv.ofBijective
  (fun i => ConjClasses.mk (threeClassRepr i)) (by
    constructor
    · intro i j h
      have hij := ConjClasses.mk_eq_mk_iff_isConj.mp h
      obtain ⟨k, hk, hu⟩ := three_conjugacy_data.1 (threeClassRepr i)
      exact (hu i (IsConj.refl _)).trans (hu j hij).symm
    · intro c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 g
      exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi.symm⟩)

/-- Every irreducible character of the matrix group occurs exactly once. -/
public theorem glTwoThreeCharacter_complete {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : ∃! i : Fin 8, glTwoThreeCharacter i = χ := by
  classical
  let f : Fin 8 → IrrBG19 G := fun i => ⟨glTwoThreeCharacter i, glTwoThreeCharacter_irreducible i⟩
  have hinj : Function.Injective f := fun _ _ h =>
    glTwoThreeCharacter_injective (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin 8) = Fintype.card (IrrBG19 G) := by
    rw [fintype_card_irr_eq_conjClassesBG19, ← Nat.card_congr conjEquiv, Nat.card_eq_fintype_card]
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).2
  obtain ⟨i, hi⟩ := hsurj ⟨χ, hχ⟩
  refine ⟨i, congrArg Subtype.val hi, ?_⟩
  intro j hj
  exact glTwoThreeCharacter_injective (hj.trans (congrArg Subtype.val hi).symm)

private def irrEquiv : Fin 8 ≃ IrrBG19 G := Equiv.ofBijective
  (fun i => ⟨glTwoThreeCharacter i, glTwoThreeCharacter_irreducible i⟩) (by
    constructor
    · intro i j h
      exact glTwoThreeCharacter_injective (congrArg Subtype.val h)
    · intro χ
      obtain ⟨i, hi, _⟩ := glTwoThreeCharacter_complete χ.property
      exact ⟨i, Subtype.ext hi⟩)

/-- Every generalized character has integral coefficients in the displayed table. -/
public theorem glTwoThreeCharacter_integral_expansion {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) :
    ∃ n : Fin 8 → ℤ, f = ∑ i, (n i : ℂ) • glTwoThreeCharacter i := by
  have hint (i : Fin 8) : ∃ n : ℤ, scalarProduct G f (glTwoThreeCharacter i) = (n : ℂ) := by
    obtain ⟨n, hn⟩ := multiplicity_int (glTwoThreeCharacter_irreducible i) f hf
    refine ⟨n, ?_⟩
    rw [← scalarProduct_conj, hn, star_intCast]
  choose n hn using hint
  refine ⟨n, ?_⟩
  funext g
  rw [classFunction_eq_sum_irr_coeffs hf g]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hn] using
    (Fintype.sum_equiv irrEquiv
      (fun i => scalarProduct G f (glTwoThreeCharacter i) * glTwoThreeCharacter i g)
      (fun χ => scalarProduct G f χ.val * χ.val g) (fun _ => rfl)).symm

/-- The roots of the central involution in the actual matrix group. -/
@[expose] public def glTwoThreeRootSupport : Set G :=
  {g | threeCentral ∈ Subgroup.zpowers g}

public theorem glTwoThreeRootSupport_class (j : Fin 8) :
    threeClassRepr j ∈ glTwoThreeRootSupport ↔ j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 :=
  three_conjugacy_data.2.2.2 j

public theorem glTwoThree_supported_iff {f : ClassFunction G} (hf : IsClassFunction f) :
    supportedOn f glTwoThreeRootSupport ↔
      f (threeClassRepr 0) = 0 ∧ f (threeClassRepr 3) = 0 ∧ f (threeClassRepr 5) = 0 := by
  constructor
  · intro h
    exact ⟨h _ (by rw [glTwoThreeRootSupport_class]; decide),
      h _ (by rw [glTwoThreeRootSupport_class]; decide),
      h _ (by rw [glTwoThreeRootSupport_class]; decide)⟩
  · rintro ⟨h0, h3, h5⟩ g hg
    have hn : threeClassRepr (threeClassIndex g) ∉ glTwoThreeRootSupport := by
      exact fun h => hg ((threeCentral_mem_zpowers_isConj (three_isConj_classIndex g)).mpr h)
    rw [glTwoThreeRootSupport_class] at hn
    rw [three_classFunction_apply f hf]
    generalize threeClassIndex g = i at *
    fin_cases i <;> simp_all

/-- Wong's five generalized characters Φ₁,…,Φ₅ (indexed here by Fin 5). -/
@[expose] public def glTwoThreeSupportedGenerator (k : Fin 5) : ClassFunction G :=
  ![glTwoThreeCharacter 0 + glTwoThreeCharacter 2 - glTwoThreeCharacter 4,
    glTwoThreeCharacter 2 - glTwoThreeCharacter 6,
    glTwoThreeCharacter 6 - glTwoThreeCharacter 7,
    glTwoThreeCharacter 1 + glTwoThreeCharacter 4 - glTwoThreeCharacter 5,
    glTwoThreeCharacter 1 + glTwoThreeCharacter 2 - glTwoThreeCharacter 3] k

public theorem glTwoThreeSupportedGenerator_generalized (k : Fin 5) :
    IsGeneralizedCharacter (glTwoThreeSupportedGenerator k) := by
  have hc (i : Fin 8) := isCharacter_of_isIrreducibleCharacter (glTwoThreeCharacter_irreducible i)
  fin_cases k
  · exact ⟨_, _, isCharacter_add (hc 0) (hc 2), hc 4, rfl⟩
  · exact ⟨_, _, hc 2, hc 6, rfl⟩
  · exact ⟨_, _, hc 6, hc 7, rfl⟩
  · exact ⟨_, _, isCharacter_add (hc 1) (hc 4), hc 5, rfl⟩
  · exact ⟨_, _, isCharacter_add (hc 1) (hc 2), hc 3, rfl⟩

private theorem generator_class (k : Fin 5) : IsClassFunction (glTwoThreeSupportedGenerator k) :=
  isClassFunction_of_isGeneralizedCharacter (glTwoThreeSupportedGenerator_generalized k)

public theorem glTwoThreeSupportedGenerator_values (k : Fin 5) (j : Fin 8) :
    glTwoThreeSupportedGenerator k (threeClassRepr j) =
    ![![0,0,4,0,0,0,2,2], ![0,4,2,0,-2,0,-glTwoThreeOmega,glTwoThreeOmega],
      ![0,0,0,0,0,0,2*glTwoThreeOmega,-2*glTwoThreeOmega],
      ![0,8,0,0,2,0,-2,-2], ![0,0,4,0,0,0,-2,-2]] k j := by
  fin_cases k <;>
    simp only [glTwoThreeSupportedGenerator, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.reduceFinMk, Pi.add_apply, Pi.sub_apply]
  all_goals rw [glTwoThreeCharacter_values, glTwoThreeCharacter_values]
  all_goals try rw [glTwoThreeCharacter_values]
  all_goals fin_cases j <;>
    dsimp only [glTwoThreeCharacterTable, Matrix.cons_val, Fin.reduceFinMk] <;>
    simp only [Matrix.cons_val] <;> ring

public theorem glTwoThreeSupportedGenerator_supported (k : Fin 5) :
    supportedOn (glTwoThreeSupportedGenerator k) glTwoThreeRootSupport := by
  rw [glTwoThree_supported_iff (generator_class k)]
  simp only [glTwoThreeSupportedGenerator_values]
  fin_cases k <;> dsimp only [Matrix.cons_val, Fin.reduceFinMk] <;>
    simp only [Matrix.cons_val] <;> norm_num

/-- The Gram matrix of Wong's five integral generators. -/
public theorem glTwoThreeSupportedGenerator_gram (k l : Fin 5) :
    scalarProduct G (glTwoThreeSupportedGenerator k) (glTwoThreeSupportedGenerator l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l := by
  rw [three_scalarProduct _ _ (generator_class k) (generator_class l)]
  simp_rw [glTwoThreeSupportedGenerator_values]
  fin_cases k <;> fin_cases l <;>
    norm_num [Fin.sum_univ_succ, glTwoThreeOmega_star,
      ← pow_two, glTwoThreeOmega_sq] <;>
    simp only [starRingEnd_apply, star_ofNat, glTwoThreeOmega_star] <;>
    ring_nf <;> norm_num [glTwoThreeOmega_sq]

/-- Vanishing on the three complementary classes solves the integral lattice equations. -/
public theorem glTwoThree_supported_expansion {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (hs : supportedOn f glTwoThreeRootSupport) :
    ∃ m : Fin 5 → ℤ, f = ∑ k, (m k : ℂ) • glTwoThreeSupportedGenerator k := by
  obtain ⟨n, hn⟩ := glTwoThreeCharacter_integral_expansion hf
  obtain ⟨h0, h3, h5⟩ :=
    (glTwoThree_supported_iff (isClassFunction_of_isGeneralizedCharacter hf)).mp hs
  rw [hn] at h0 h3 h5
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, glTwoThreeCharacter_values] at h0 h3 h5
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h0 h3 h5
  dsimp only [glTwoThreeCharacterTable, Matrix.cons_val, Fin.succ, Fin.reduceFinMk] at h0 h3 h5
  simp only [Matrix.cons_val] at h0 h3 h5
  norm_num at h0 h3 h5
  simp only [Fin.reduceFinMk, Matrix.cons_val] at h0 h3 h5
  have e0 : n 0 + n 1 + 2*n 2 + 3*n 3 + 3*n 4 + 4*n 5 + 2*n 6 + 2*n 7 = 0 := by
    exact_mod_cast (show (n 0 : ℂ) + n 1 + 2*n 2 + 3*n 3 + 3*n 4 + 4*n 5 + 2*n 6 + 2*n 7 = 0 by
      linear_combination h0)
  have e3 : n 0 + n 1 - n 2 + n 5 - n 6 - n 7 = 0 := by
    exact_mod_cast (show (n 0 : ℂ) + n 1 - n 2 + n 5 - n 6 - n 7 = 0 by linear_combination h3)
  have e5 : n 0 - n 1 - n 3 + n 4 = 0 := by
    exact_mod_cast (show (n 0 : ℂ) - n 1 - n 3 + n 4 = 0 by linear_combination h5)
  have hn1 : n 1 = -n 5 - n 3 := by omega
  have hn2 : n 2 = n 0 - n 6 - n 7 - n 3 := by omega
  have hn4 : n 4 = -n 0 - n 5 := by omega
  refine ⟨![n 0, -n 6 - n 7, -n 7, -n 5, -n 3], ?_⟩
  rw [hn]
  funext g
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [glTwoThreeSupportedGenerator, Matrix.cons_val, Fin.succ, Fin.reduceFinMk]
  norm_num only
  simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply, Pi.sub_apply, Int.cast_neg, Int.cast_sub,
    add_zero]
  rw [hn1, hn2, hn4]
  push_cast
  ring

private theorem generalized_add {f h : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (hh : IsGeneralizedCharacter h) :
    IsGeneralizedCharacter (f + h) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hf
  obtain ⟨c, d, hc, hd, rfl⟩ := hh
  exact ⟨a+c, b+d, isCharacter_add ha hc, isCharacter_add hb hd, by funext g; simp; ring⟩

private theorem char_nat_mul (n : ℕ) {f : ClassFunction G} (hf : IsCharacter f) :
    IsCharacter ((n : ℂ) • f) := by
  induction n with
  | zero => simpa using (show IsCharacter (0 : ClassFunction G) from isCharacter_zero)
  | succ n ih =>
    convert isCharacter_add ih hf using 1
    ext g
    simp [Nat.cast_add, add_mul]

private theorem generalized_int_mul (n : ℤ) {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) : IsGeneralizedCharacter ((n : ℂ) • f) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hf
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact ⟨(k : ℂ) • a, (k : ℂ) • b, char_nat_mul k ha, char_nat_mul k hb, by
      simp [smul_sub]⟩
  · exact ⟨(k : ℂ) • b, (k : ℂ) • a, char_nat_mul k hb, char_nat_mul k ha, by
      funext g; simp; ring⟩

/-- Every integral combination is a generalized character supported on the root set. -/
public theorem glTwoThreeSupportedGenerator_combination (m : Fin 5 → ℤ) :
    IsGeneralizedCharacter (∑ k, (m k : ℂ) • glTwoThreeSupportedGenerator k) ∧
    supportedOn (∑ k, (m k : ℂ) • glTwoThreeSupportedGenerator k) glTwoThreeRootSupport := by
  constructor
  · have hsum (s : Finset (Fin 5)) :
        IsGeneralizedCharacter (∑ k ∈ s, (m k : ℂ) • glTwoThreeSupportedGenerator k) := by
      classical
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨0, 0, isCharacter_zero, isCharacter_zero, by simp⟩
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact generalized_add
          (generalized_int_mul _ (glTwoThreeSupportedGenerator_generalized a)) ih
    exact hsum Finset.univ
  · intro g hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [glTwoThreeSupportedGenerator_supported k g hg, mul_zero]

/-- Wong's equation (2): the supported generalized-character lattice is exactly
 the integer span of Φ₁,…,Φ₅. -/
public theorem glTwoThree_supported_lattice (f : ClassFunction G) :
    (IsGeneralizedCharacter f ∧ supportedOn f glTwoThreeRootSupport) ↔
      ∃ m : Fin 5 → ℤ, f = ∑ k, (m k : ℂ) • glTwoThreeSupportedGenerator k := by
  constructor
  · rintro ⟨hf, hs⟩
    exact glTwoThree_supported_expansion hf hs
  · rintro ⟨m, rfl⟩
    exact glTwoThreeSupportedGenerator_combination m

/-- A class function orthogonal to Wong's five generators vanishes on every root
of the central involution. No characterhood hypothesis is needed. -/
public theorem glTwoThree_orthogonal_vanishes {f : ClassFunction G}
    (hf : IsClassFunction f)
    (ho : ∀ k : Fin 5, scalarProduct G f (glTwoThreeSupportedGenerator k) = 0) :
    ∀ g ∈ glTwoThreeRootSupport, f g = 0 := by
  have he (k : Fin 5) :
      (∑ j : Fin 8, (![1,1,6,8,8,12,6,6] j : ℂ) *
        (f (threeClassRepr j) * star (glTwoThreeSupportedGenerator k (threeClassRepr j)))) = 0 := by
    have h := ho k
    rw [three_scalarProduct _ _ hf (generator_class k)] at h
    exact (div_eq_zero_iff).mp h |>.resolve_right (by norm_num)
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have h4 := he 4
  simp only [glTwoThreeSupportedGenerator_values, Fin.sum_univ_succ, Fin.sum_univ_zero]
    at h0 h1 h2 h3 h4
  dsimp only [Matrix.cons_val, Fin.succ, Fin.reduceFinMk] at h0 h1 h2 h3 h4
  simp only [Matrix.cons_val] at h0 h1 h2 h3 h4
  norm_num [glTwoThreeOmega_star] at h0 h1 h2 h3 h4
  simp only [Fin.reduceFinMk] at h0 h1 h2 h3 h4
  have hv : f (threeClassRepr 2) = 0 := by
    linear_combination (1 / 48 : ℂ) * (h0 + h4)
  have hwne : glTwoThreeOmega ≠ 0 := by
    intro h
    have hh := glTwoThreeOmega_sq
    norm_num [h] at hh
  have hd : glTwoThreeOmega * (f (threeClassRepr 6) - f (threeClassRepr 7)) = 0 := by
    linear_combination (-1 / 12 : ℂ) * h2
  have hd' := (mul_eq_zero.mp hd).resolve_left hwne
  have hx : f (threeClassRepr 6) = 0 := by
    linear_combination (1 / 48 : ℂ) * (h0 - h4) + (1 / 2 : ℂ) * hd'
  have hy : f (threeClassRepr 7) = 0 := by
    linear_combination (1 / 48 : ℂ) * (h0 - h4) - (1 / 2 : ℂ) * hd'
  rw [hv] at h1
  rw [hx, hy] at h1 h3
  have hu : f (threeClassRepr 1) = 0 := by
    linear_combination (1 / 12 : ℂ) * (h1 + h3)
  have hw : f (threeClassRepr 4) = 0 := by
    linear_combination (1 / 16 : ℂ) * h3 - (1 / 2 : ℂ) * hu
  intro g hg
  have hm := (threeCentral_mem_zpowers_isConj (three_isConj_classIndex g)).mp hg
  have hi := (glTwoThreeRootSupport_class (threeClassIndex g)).mp hm
  rw [three_classFunction_apply f hf]
  rcases hi with hi | hi | hi | hi | hi <;> rw [hi] <;> assumption

end
end ABG
