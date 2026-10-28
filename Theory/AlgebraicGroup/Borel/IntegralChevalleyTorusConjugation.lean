module

public import Theory.AlgebraicGroup.Borel.IntegralChevalleyRootCurves

/-!
# Integral Chevalley split-torus conjugation

For a finite reduced crystallographic root pairing with a chosen base, this module constructs
the diagonal split torus on the integral Cartan-plus-root lattice.  Its grading is the vector of
simple-coroot pairings.  Direct support calculations show that simple Tits lifts, their explicit
inverses, and arbitrary Tits words transport that grading by the corresponding reflections.
Consequently every all-root divided power obtained by Tits transport is homogeneous of degree
`n` times its root.

After specialization to any commutative ring, the negative basis weights define diagonal units.
Homogeneity then turns conjugation of the truncated exponential root curves into evaluation of
the expected root character.  The source parameter map is deliberately not claimed injective:
the exported character and common-kernel equivalences identify exactly when two diagonal images
agree, which is the interface required by generated-carrier constructions.

The construction uses the integral root operators and characteristic-free root curves from the
preceding modules.  Its root-lattice and Tits-word formulas follow the integral Geck construction
formalized there, rather than assuming a general Chevalley-group existence theorem.
-/

open scoped BigOperators Matrix

namespace RootPairing.IntegralGeckConstruction

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The coroot grading of the Cartan-plus-root basis. -/
def chevalleyBasisWeight (a : b.support ⊕ ι) (q : ι) : ℤ :=
  match a with
  | Sum.inl _ => 0
  | Sum.inr i => P.pairingIn ℤ i q

/-- A matrix is homogeneous when every nonzero entry has one fixed weight difference. -/
def IsChevalleyHomogeneous
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (d : ι → ℤ) : Prop :=
  ∀ row column, A row column ≠ 0 →
    ∀ q, chevalleyBasisWeight (P := P) row q - chevalleyBasisWeight column q = d q

/-- A matrix transports basis gradings contravariantly along a root permutation. -/
def RespectsChevalleyGrading
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (σ : ι → ι) : Prop :=
  ∀ row column, A row column ≠ 0 →
    ∀ q, chevalleyBasisWeight (P := P) row q = chevalleyBasisWeight column (σ q)

/-- The inverse simple-reflection action associated to a Tits word. -/
def inverseReflectionWord : List b.support → ι → ι
  | [], q => q
  | i :: word, q => inverseReflectionWord word (P.reflectionPerm i q)

private lemma matrix_mul_support
    {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ} {row column}
    (h : (A * B) row column ≠ 0) :
    ∃ middle, A row middle ≠ 0 ∧ B middle column ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨middle, -, hmiddle⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨middle, left_ne_zero_of_mul hmiddle, right_ne_zero_of_mul hmiddle⟩

private lemma RespectsChevalleyGrading.mul
    {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ} {σ τ : ι → ι}
    (hA : RespectsChevalleyGrading (P := P) A σ)
    (hB : RespectsChevalleyGrading (P := P) B τ) :
    RespectsChevalleyGrading (P := P) (A * B) (fun q => τ (σ q)) := by
  intro row column h q
  obtain ⟨middle, hAm, hBm⟩ := matrix_mul_support h
  rw [hA row middle hAm q, hB middle column hBm (σ q)]

lemma inverseReflectionWord_left_inverse (word : List b.support) (q : ι) :
    reflectionWord (P := P) word (inverseReflectionWord (P := P) word q) = q := by
  induction word generalizing q with
  | nil => rfl
  | cons i word ih =>
      simp only [reflectionWord, inverseReflectionWord]
      rw [ih (P.reflectionPerm i q), P.reflectionPerm_self]

lemma inverseReflectionWord_right_inverse (word : List b.support) (q : ι) :
    inverseReflectionWord (P := P) word (reflectionWord (P := P) word q) = q := by
  induction word generalizing q with
  | nil => rfl
  | cons i word ih =>
      simp only [reflectionWord, inverseReflectionWord]
      rw [P.reflectionPerm_self, ih]

lemma pairingIn_reflectionWord (word : List b.support) (j q : ι) :
    P.pairingIn ℤ (reflectionWord (P := P) word j) q =
      P.pairingIn ℤ j (inverseReflectionWord (P := P) word q) := by
  induction word generalizing q with
  | nil => rfl
  | cons i word ih =>
      simp only [reflectionWord, inverseReflectionWord]
      rw [← P.pairingIn_reflectionPerm ℤ, ih (P.reflectionPerm i q)]

private lemma titsLift_cartan_preimage (i j : b.support) :
    titsLift (P := P) i *ᵥ
        (u j - |b.cartanMatrix i j| • u i) = u j := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, titsLift_mulVec_u, titsLift_mulVec_u]
  have hii : |b.cartanMatrix i i| = 2 := by simp
  rw [hii]
  module

private lemma titsLiftInv_mulVec_u (i j : b.support) :
    titsLiftInv (P := P) i *ᵥ u j = u j - |b.cartanMatrix i j| • u i := by
  have h := congrArg (fun x => titsLiftInv (P := P) i *ᵥ x)
    (titsLift_cartan_preimage (P := P) i j)
  rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec] at h
  symm
  exact h

private lemma titsLiftInv_root_preimage (i : b.support) (j : ι) :
    letI := P.indexNeg
    (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j) •
        (titsLiftInv (P := P) i *ᵥ v (b := b) j) =
      v (b := b) (P.reflectionPerm i j) := by
  let := P.indexNeg
  have h := congrArg (fun x => titsLiftInv (P := P) i *ᵥ x)
    (titsLift_mulVec_v (P := P) i (P.reflectionPerm i j))
  rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec] at h
  symm
  simpa only [P.reflectionPerm_self, Matrix.mulVec_smul] using h

/-- A simple Tits lift preserves the grading after reflecting the coroot index. -/
theorem titsLift_respectsChevalleyGrading (i : b.support) :
    RespectsChevalleyGrading (P := P) (titsLift (P := P) i) (P.reflectionPerm i) := by
  let _ := P.indexNeg
  intro row column h q
  cases column with
  | inl j =>
      have hcol := congrFun (titsLift_mulVec_u (P := P) i j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k => rfl
      | inr k =>
          simp [u, Pi.single_apply] at hcol
          exact (h hcol).elim
  | inr j =>
      have hcol := congrFun (titsLift_mulVec_v (P := P) i j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k =>
          simp [v, Pi.single_apply] at hcol
          exact (h hcol).elim
      | inr k =>
          by_cases hk : k = P.reflectionPerm i j
          · subst k
            exact (P.pairingIn_reflectionPerm ℤ i j q).symm
          · simp [v, Pi.single_apply, hk] at hcol
            exact (h hcol).elim

/-- The explicit inverse of a simple Tits lift has the same reflected grading. -/
theorem titsLiftInv_respectsChevalleyGrading (i : b.support) :
    RespectsChevalleyGrading (P := P) (titsLiftInv (P := P) i)
      (P.reflectionPerm i) := by
  let _ := P.indexNeg
  intro row column h q
  cases column with
  | inl j =>
      have hcol := congrFun (titsLiftInv_mulVec_u (P := P) i j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k => rfl
      | inr k =>
          simp [u, Pi.single_apply] at hcol
          exact (h hcol).elim
  | inr j =>
      have hcol := congrFun (titsLiftInv_root_preimage (P := P) i j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k =>
          simp [v, Pi.single_apply] at hcol
          exact (h hcol).elim
      | inr k =>
          by_cases hk : k = P.reflectionPerm i j
          · subst k
            exact (P.pairingIn_reflectionPerm ℤ i j q).symm
          · simp [v, Pi.single_apply, hk] at hcol
            exact (h hcol).elim

private lemma titsWordInv_nil_eq :
    titsWordInv (P := P) (b := b) [] = 1 := by
  calc
    titsWordInv (P := P) (b := b) [] =
        titsWordInv (P := P) (b := b) [] * titsWord (P := P) (b := b) [] := by
          rw [titsWord]
          simp
    _ = 1 := titsWord_inv_mul (P := P) (b := b) []

private lemma titsWordInv_cons_eq (i : b.support) (word : List b.support) :
    titsWordInv (P := P) (i :: word) =
      titsWordInv (P := P) word * titsLiftInv (P := P) i := by
  let candidate := titsWordInv (P := P) word * titsLiftInv (P := P) i
  have hright : titsWord (P := P) (i :: word) * candidate = 1 := by
    dsimp only [candidate]
    rw [titsWord]
    calc
      (titsLift i * titsWord word) * (titsWordInv word * titsLiftInv i) =
          titsLift i * (titsWord word * titsWordInv word) * titsLiftInv i := by
            noncomm_ring
      _ = 1 := by rw [titsWord_mul_inv, Matrix.mul_one, titsLift_mul_inv]
  calc
    titsWordInv (P := P) (i :: word) = titsWordInv (P := P) (i :: word) * 1 := by
      rw [Matrix.mul_one]
    _ = titsWordInv (P := P) (i :: word) *
        (titsWord (P := P) (i :: word) * candidate) := by rw [hright]
    _ = (titsWordInv (P := P) (i :: word) * titsWord (P := P) (i :: word)) *
        candidate := by rw [Matrix.mul_assoc]
    _ = candidate := by rw [titsWord_inv_mul, Matrix.one_mul]

/-- A Tits word transports the grading by the inverse Weyl word. -/
theorem titsWord_respectsChevalleyGrading (word : List b.support) :
    RespectsChevalleyGrading (P := P) (titsWord (P := P) word)
      (inverseReflectionWord (P := P) word) := by
  induction word with
  | nil =>
      intro row column h q
      simp only [titsWord, Matrix.one_apply] at h
      have hrc : row = column := by
        by_contra hne
        simp [hne] at h
      subst column
      rfl
  | cons i word ih =>
      simp only [titsWord, inverseReflectionWord]
      exact (titsLift_respectsChevalleyGrading (P := P) i).mul ih

/-- The explicit inverse word transports the grading by the forward Weyl word. -/
theorem titsWordInv_respectsChevalleyGrading (word : List b.support) :
    RespectsChevalleyGrading (P := P) (titsWordInv (P := P) word)
      (reflectionWord (P := P) word) := by
  induction word with
  | nil =>
      rw [titsWordInv_nil_eq]
      intro row column h q
      simp only [Matrix.one_apply] at h
      have hrc : row = column := by
        by_contra hne
        simp [hne] at h
      subst column
      rfl
  | cons i word ih =>
      rw [titsWordInv_cons_eq]
      simp only [reflectionWord]
      exact ih.mul (titsLiftInv_respectsChevalleyGrading (P := P) i)

private lemma pairingIn_neg_left (i q : ι) :
    letI := P.indexNeg
    P.pairingIn ℤ (-i) q = -P.pairingIn ℤ i q := by
  let _ := P.indexNeg
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [map_neg, P.algebraMap_pairingIn]
  simp only [← P.root_coroot_eq_pairing, P.indexNeg_neg,
    P.root_reflectionPerm, P.reflection_apply_self, LinearMap.neg_apply, map_neg]
  rw [P.algebraMap_pairingIn]
  rw [P.root_coroot_eq_pairing]

private lemma pairingIn_add_nsmul {i j k q : ι} (n : ℕ)
    (h : P.root k = P.root j + n • P.root i) :
    P.pairingIn ℤ k q = P.pairingIn ℤ j q + (n : ℤ) * P.pairingIn ℤ i q := by
  have h' : P.root k = (1 : ℤ) • P.root j + (n : ℤ) • P.root i := by
    simpa using h
  simpa [smul_eq_mul] using
    (P.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := q) h')

private lemma pairingIn_sub_nsmul {i j k q : ι} (n : ℕ)
    (h : P.root k = P.root j - n • P.root i) :
    P.pairingIn ℤ k q = P.pairingIn ℤ j q - (n : ℤ) * P.pairingIn ℤ i q := by
  let _ := P.indexNeg
  have h' : P.root k = P.root j + n • P.root (-i : ι) := by
    simpa [sub_eq_add_neg] using h
  rw [pairingIn_add_nsmul (P := P) n h', pairingIn_neg_left (P := P)]
  ring

private lemma one_isChevalleyHomogeneous :
    IsChevalleyHomogeneous (P := P) (1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
      (fun _ => 0) := by
  intro row column h q
  simp only [Matrix.one_apply] at h
  have hrc : row = column := by
    by_contra hne
    simp [hne] at h
  subst column
  simp

/-- The positive simple-root operator raises every coroot grading by its root. -/
theorem eMatrix_isChevalleyHomogeneous (i : b.support) :
    IsChevalleyHomogeneous (P := P) (eMatrix (P := P) i)
      (fun q => P.pairingIn ℤ i q) := by
  let _ := P.indexNeg
  intro row column h q
  cases row with
  | inl k =>
      cases column with
      | inl j => simp [eMatrix] at h
      | inr j =>
          have hkji : k = i ∧ j = P.reflectionPerm i i := by
            simpa [eMatrix] using h
          have hki : k = i := hkji.1
          have hj : j = -i := by
            simpa only [P.indexNeg_neg] using hkji.2
          subst k
          subst j
          simp only [chevalleyBasisWeight, zero_sub, pairingIn_neg_left]
          ring
  | inr k =>
      cases column with
      | inl j =>
          have hki : k = i := by
            by_contra hne
            simp [eMatrix, hne] at h
          subst k
          simp [chevalleyBasisWeight]
      | inr j =>
          have hroot : P.root k = P.root i + P.root j := by
            by_contra hne
            simp [eMatrix, hne] at h
          simp only [chevalleyBasisWeight]
          rw [show P.pairingIn ℤ k q =
              P.pairingIn ℤ i q + P.pairingIn ℤ j q by
            exact P.pairingIn_eq_add_of_root_eq_add hroot]
          ring

/-- The negative simple-root operator lowers every coroot grading by its root. -/
theorem fMatrix_isChevalleyHomogeneous (i : b.support) :
    IsChevalleyHomogeneous (P := P) (fMatrix (P := P) i)
      (fun q => -P.pairingIn ℤ i q) := by
  let _ := P.indexNeg
  intro row column h q
  cases row with
  | inl k =>
      cases column with
      | inl j => simp [fMatrix] at h
      | inr j =>
          have hki : k = i := by
            by_contra hne
            simp [fMatrix, hne] at h
          have hj : j = i := by
            by_contra hne
            simp [fMatrix, hne] at h
          subst k
          subst j
          simp [chevalleyBasisWeight]
  | inr k =>
      cases column with
      | inl j =>
          have hki' : k = P.reflectionPerm i i ∧ b.cartanMatrix i j ≠ 0 := by
            simpa [fMatrix] using h
          have hki : k = -i := by
            simpa only [P.indexNeg_neg] using hki'.1
          subst k
          simp [chevalleyBasisWeight, pairingIn_neg_left]
      | inr j =>
          have hroot : P.root k = P.root j - P.root i := by
            by_contra hne
            simp [fMatrix, hne] at h
          simp only [chevalleyBasisWeight]
          rw [show P.pairingIn ℤ k q =
              P.pairingIn ℤ j q - P.pairingIn ℤ i q by
            simpa using pairingIn_sub_nsmul (P := P) (q := q) (n := 1)
              (by simpa using hroot)]
          ring

/-- Every positive simple-root divided power is homogeneous of the expected degree. -/
theorem eDividedPower_isChevalleyHomogeneous (i : b.support) (n : ℕ) :
    IsChevalleyHomogeneous (P := P) (eDividedPower (P := P) i n)
      (fun q => (n : ℤ) * P.pairingIn ℤ i q) := by
  rcases n with (_ | _ | n)
  · simpa using one_isChevalleyHomogeneous (P := P) (b := b)
  · simpa using eMatrix_isChevalleyHomogeneous (P := P) i
  · intro row column h q
    cases row with
    | inl k =>
        cases column <;> simp [eDividedPower] at h
    | inr k =>
        cases column with
        | inl j => simp [eDividedPower] at h
        | inr j =>
            have hroot : P.root k = P.root j + (n + 2) • P.root i := by
              by_contra hne
              simp [eDividedPower, hne] at h
            simp only [chevalleyBasisWeight]
            rw [pairingIn_add_nsmul (P := P) (q := q) (n + 2) hroot]
            push_cast
            ring

private lemma pairingIn_neg_right (i q : ι) :
    letI := P.indexNeg
    P.pairingIn ℤ i (-q) = -P.pairingIn ℤ i q := by
  let _ := P.indexNeg
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [P.algebraMap_pairingIn, map_neg, P.algebraMap_pairingIn]
  simp only [← P.root_coroot_eq_pairing, P.indexNeg_neg,
    P.coroot_reflectionPerm, P.coreflection_apply_self, LinearMap.map_neg]

/-- The Cartan-root involution negates the root grading and fixes Cartan degree zero. -/
theorem omegaMatrix_respectsChevalleyGrading :
    letI := P.indexNeg
    RespectsChevalleyGrading (P := P) (omegaMatrix (P := P) (b := b)) (-·) := by
  let _ := P.indexNeg
  intro row column h q
  cases column with
  | inl j =>
      have hcol := congrFun (omegaMatrix_mulVec_u (P := P) (b := b) j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k => rfl
      | inr k =>
          simp [u] at hcol
          exact (h hcol).elim
  | inr j =>
      have hcol := congrFun (omegaMatrix_mulVec_v (P := P) (b := b) j) row
      rw [Matrix.mulVec_single_one] at hcol
      cases row with
      | inl k =>
          simp [v] at hcol
          exact (h hcol).elim
      | inr k =>
          by_cases hk : k = -j
          · subst k
            simp only [chevalleyBasisWeight, pairingIn_neg_left, pairingIn_neg_right]
          · have hk' : k ≠ P.reflectionPerm j j := by
              simpa only [← P.indexNeg_neg] using hk
            simp [v, hk'] at hcol
            exact (h hcol).elim

private lemma homogeneous_sandwich
    {L A U : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ}
    {d : ι → ℤ} {σ τ : ι → ι}
    (hL : RespectsChevalleyGrading (P := P) L σ)
    (hA : IsChevalleyHomogeneous (P := P) A d)
    (hU : RespectsChevalleyGrading (P := P) U τ)
    (hinv : ∀ q, τ (σ q) = q) :
    IsChevalleyHomogeneous (P := P) (L * A * U) (fun q => d (σ q)) := by
  intro row column h q
  obtain ⟨middle, hLA, hUcol⟩ := matrix_mul_support h
  obtain ⟨source, hLrow, hAsource⟩ := matrix_mul_support hLA
  have hleft := hL row source hLrow q
  have hdegree := hA source middle hAsource (σ q)
  have hright := hU middle column hUcol (σ q)
  rw [hinv] at hright
  change chevalleyBasisWeight (P := P) row q - chevalleyBasisWeight column q = d (σ q)
  calc
    _ = chevalleyBasisWeight (P := P) source (σ q) -
        chevalleyBasisWeight column q := by rw [hleft]
    _ = chevalleyBasisWeight (P := P) source (σ q) -
        chevalleyBasisWeight middle (σ q) := by rw [hright]
    _ = d (σ q) := hdegree

/-- Every negative simple-root divided power is homogeneous of the expected degree. -/
theorem fDividedPower_isChevalleyHomogeneous (i : b.support) (n : ℕ) :
    IsChevalleyHomogeneous (P := P) (fDividedPower (P := P) i n)
      (fun q => -(n : ℤ) * P.pairingIn ℤ i q) := by
  let _ := P.indexNeg
  rw [fDividedPower]
  have h := homogeneous_sandwich (P := P)
    (omegaMatrix_respectsChevalleyGrading (P := P) (b := b))
    (eDividedPower_isChevalleyHomogeneous (P := P) i n)
    (omegaMatrix_respectsChevalleyGrading (P := P) (b := b))
    (fun q => neg_involutive q)
  convert h using 1
  funext q
  rw [pairingIn_neg_right (P := P)]
  ring

/-- Tits conjugation transports a homogeneous degree along the inverse Weyl word. -/
theorem transportedMatrix_isChevalleyHomogeneous
    (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (d : ι → ℤ)
    (hA : IsChevalleyHomogeneous (P := P) A d) :
    IsChevalleyHomogeneous (P := P) (transportedMatrix (P := P) word A)
      (fun q => d (inverseReflectionWord (P := P) word q)) := by
  rw [transportedMatrix]
  exact homogeneous_sandwich (P := P)
    (titsWord_respectsChevalleyGrading (P := P) word) hA
    (titsWordInv_respectsChevalleyGrading (P := P) word)
    (inverseReflectionWord_left_inverse (P := P) word)

/-- Every transported all-root divided power has degree `n` times its root pairing. -/
theorem rootDividedPower_isChevalleyHomogeneous (i : ι) (n : ℕ) :
    IsChevalleyHomogeneous (P := P) (rootDividedPower (P := P) (b := b) i n)
      (fun q => (n : ℤ) * P.pairingIn ℤ i q) := by
  classical
  let _ := P.indexNeg
  by_cases hi : b.IsPos i
  · rw [rootDividedPower_of_pos i hi]
    let route := rootRoute (P := P) (b := b) i
    have h := transportedMatrix_isChevalleyHomogeneous (P := P)
      route.word (eDividedPower (P := P) route.simple n)
      (fun q => (n : ℤ) * P.pairingIn ℤ route.simple q)
      (eDividedPower_isChevalleyHomogeneous (P := P) route.simple n)
    convert h using 1
    funext q
    have hpair : P.pairingIn ℤ i q =
        P.pairingIn ℤ route.simple (inverseReflectionWord (P := P) route.word q) := by
      calc
        _ = P.pairingIn ℤ (reflectionWord (P := P) route.word route.simple) q :=
          congrArg (fun j => P.pairingIn ℤ j q) route.target.symm
        _ = _ := pairingIn_reflectionWord (P := P) route.word route.simple q
    rw [hpair]
  · simp only [rootDividedPower, dif_neg hi]
    let route := rootRoute (P := P) (b := b) (-i)
    have h := transportedMatrix_isChevalleyHomogeneous (P := P)
      route.word (fDividedPower (P := P) route.simple n)
      (fun q => -(n : ℤ) * P.pairingIn ℤ route.simple q)
      (fDividedPower_isChevalleyHomogeneous (P := P) route.simple n)
    convert h using 1
    funext q
    have hpair : P.pairingIn ℤ (-i) q =
        P.pairingIn ℤ route.simple (inverseReflectionWord (P := P) route.word q) := by
      calc
        _ = P.pairingIn ℤ (reflectionWord (P := P) route.word route.simple) q :=
          congrArg (fun j => P.pairingIn ℤ j q) route.target.symm
        _ = _ := pairingIn_reflectionWord (P := P) route.word route.simple q
    rw [← hpair, pairingIn_neg_left]
    ring

/-- Parameters of the split torus indexed by the chosen simple roots. -/
abbrev IntegralChevalleyTorusParameter (S : Type*) [CommRing S] := b.support → Sˣ

/-- The diagonal unit on a Cartan or root basis vector. -/
def chevalleyBasisTorusUnit {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (a : b.support ⊕ ι) : Sˣ :=
  ∏ q : b.support, u q ^ (-chevalleyBasisWeight (P := P) a q)

/-- The root character of the source split torus. -/
def integralChevalleyRootScale {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) : Sˣ :=
  ∏ q : b.support, u q ^ P.pairingIn ℤ i q

/-- The source split torus acts diagonally on the specialized Chevalley lattice. -/
def integralChevalleyTorusElement {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ where
  val := Matrix.diagonal fun a => (chevalleyBasisTorusUnit (P := P) u a : S)
  inv := Matrix.diagonal fun a => ((chevalleyBasisTorusUnit (P := P) u a)⁻¹ : Sˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]

@[simp] theorem chevalleyBasisTorusUnit_one {S : Type*} [CommRing S]
    (a : b.support ⊕ ι) :
    chevalleyBasisTorusUnit (P := P) (1 : IntegralChevalleyTorusParameter (b := b) S) a = 1 := by
  simp [chevalleyBasisTorusUnit]

theorem chevalleyBasisTorusUnit_mul {S : Type*} [CommRing S]
    (u v : IntegralChevalleyTorusParameter (b := b) S) (a : b.support ⊕ ι) :
    chevalleyBasisTorusUnit (P := P) (u * v) a =
      chevalleyBasisTorusUnit (P := P) u a *
        chevalleyBasisTorusUnit (P := P) v a := by
  simp only [chevalleyBasisTorusUnit, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem chevalleyBasisTorusUnit_inv {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (a : b.support ⊕ ι) :
    chevalleyBasisTorusUnit (P := P) u⁻¹ a =
      (chevalleyBasisTorusUnit (P := P) u a)⁻¹ := by
  simp [chevalleyBasisTorusUnit, Finset.prod_inv_distrib]

@[simp] theorem integralChevalleyRootScale_one {S : Type*} [CommRing S] (i : ι) :
    integralChevalleyRootScale (P := P) (b := b)
      (1 : IntegralChevalleyTorusParameter (b := b) S) i = 1 := by
  simp [integralChevalleyRootScale]

theorem integralChevalleyRootScale_mul {S : Type*} [CommRing S]
    (u v : IntegralChevalleyTorusParameter (b := b) S) (i : ι) :
    integralChevalleyRootScale (P := P) (u * v) i =
      integralChevalleyRootScale (P := P) u i *
        integralChevalleyRootScale (P := P) v i := by
  simp only [integralChevalleyRootScale, Pi.mul_apply, mul_zpow,
    Finset.prod_mul_distrib]

theorem integralChevalleyRootScale_inv {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) :
    integralChevalleyRootScale (P := P) u⁻¹ i =
      (integralChevalleyRootScale (P := P) u i)⁻¹ := by
  simp [integralChevalleyRootScale, Finset.prod_inv_distrib]

@[simp] theorem integralChevalleyTorusElement_one {S : Type*} [CommRing S] :
    integralChevalleyTorusElement (P := P) (b := b)
      (1 : IntegralChevalleyTorusParameter (b := b) S) = 1 := by
  apply Units.ext
  ext i j
  simp [integralChevalleyTorusElement, Matrix.one_apply]

theorem integralChevalleyTorusElement_mul {S : Type*} [CommRing S]
    (u v : IntegralChevalleyTorusParameter (b := b) S) :
    integralChevalleyTorusElement (P := P) (u * v) =
      integralChevalleyTorusElement (P := P) u *
        integralChevalleyTorusElement (P := P) v := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact congrArg Units.val (chevalleyBasisTorusUnit_mul (P := P) u v a)

theorem integralChevalleyTorusElement_inv {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) :
    integralChevalleyTorusElement (P := P) u⁻¹ =
      (integralChevalleyTorusElement (P := P) u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← integralChevalleyTorusElement_mul, inv_mul_cancel,
    integralChevalleyTorusElement_one]

@[simp] theorem chevalleyBasisTorusUnit_root {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) :
    chevalleyBasisTorusUnit (P := P) u (Sum.inr i) =
      (integralChevalleyRootScale (P := P) u i)⁻¹ := by
  simp only [chevalleyBasisTorusUnit, chevalleyBasisWeight,
    integralChevalleyRootScale]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  rw [zpow_neg]

/-- Equality in the diagonal image is exactly equality of every root character;
this does not assert that the source parameters themselves are equal. -/
theorem integralChevalleyTorusElement_eq_iff_rootScale_eq {S : Type*} [CommRing S]
    (u v : IntegralChevalleyTorusParameter (b := b) S) :
    integralChevalleyTorusElement (P := P) u =
        integralChevalleyTorusElement (P := P) v ↔
      ∀ i, integralChevalleyRootScale (P := P) u i =
        integralChevalleyRootScale (P := P) v i := by
  constructor
  · intro h i
    have hdiag := congrArg
      (fun T : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ =>
        ((T : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
          (Sum.inr i) (Sum.inr i))) h
    have hunit : chevalleyBasisTorusUnit (P := P) u (Sum.inr i) =
        chevalleyBasisTorusUnit (P := P) v (Sum.inr i) := by
      apply Units.ext
      simpa [integralChevalleyTorusElement] using hdiag
    rw [chevalleyBasisTorusUnit_root, chevalleyBasisTorusUnit_root] at hunit
    exact inv_injective hunit
  · intro h
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _
    congr 1
    funext a
    apply congrArg Units.val
    cases a with
    | inl q => simp [chevalleyBasisTorusUnit, chevalleyBasisWeight]
    | inr i =>
        rw [chevalleyBasisTorusUnit_root, chevalleyBasisTorusUnit_root, h i]

/-- The kernel of the diagonal parameter map is the common kernel of all root characters. -/
theorem integralChevalleyTorusElement_eq_one_iff_rootScale_eq_one
    {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) :
    integralChevalleyTorusElement (P := P) u = 1 ↔
      ∀ i, integralChevalleyRootScale (P := P) u i = 1 := by
  rw [← integralChevalleyTorusElement_one (P := P) (b := b) (S := S),
    integralChevalleyTorusElement_eq_iff_rootScale_eq]
  simp

private lemma chevalleyBasisTorusUnit_ratio {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) (n : ℕ)
    (row column : b.support ⊕ ι)
    (hweight : ∀ q : b.support,
      chevalleyBasisWeight (P := P) row q -
          chevalleyBasisWeight (P := P) column q =
        (n : ℤ) * P.pairingIn ℤ i q) :
    (chevalleyBasisTorusUnit (P := P) u row)⁻¹ *
        chevalleyBasisTorusUnit (P := P) u column =
      (integralChevalleyRootScale (P := P) u i) ^ n := by
  simp only [chevalleyBasisTorusUnit, integralChevalleyRootScale]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q hq
  rw [← zpow_neg, ← zpow_add]
  rw [show - -chevalleyBasisWeight (P := P) row q +
      -chevalleyBasisWeight (P := P) column q =
        (n : ℤ) * P.pairingIn ℤ i q by
      have h := hweight q
      omega]
  rw [zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  exact mul_comm _ _

private lemma rootDividedPower_torus_entry {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) (n : ℕ)
    (row column : b.support ⊕ ι) :
    (((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
          specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i n) row column *
          ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S) =
      ((integralChevalleyRootScale (P := P) u i : S) ^ n) *
        specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i n) row column := by
  by_cases hzero : rootDividedPower (P := P) (b := b) i n row column = 0
  · simp [specializeMatrix, hzero]
  · have hratio :
        (chevalleyBasisTorusUnit (P := P) u row)⁻¹ *
            chevalleyBasisTorusUnit (P := P) u column =
          (integralChevalleyRootScale (P := P) u i) ^ n :=
      chevalleyBasisTorusUnit_ratio (P := P) u i n row column
        (fun q : b.support =>
          rootDividedPower_isChevalleyHomogeneous (P := P) (b := b) i n
            row column hzero (q : ι))
    have hratioVal :
        (((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
            ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S) =
          (integralChevalleyRootScale (P := P) u i : S) ^ n := by
      simpa using congrArg Units.val hratio
    change (((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
          (rootDividedPower (P := P) (b := b) i n row column : S) *
          ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S) = _
    calc
      _ = ((((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
            ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S)) *
          (rootDividedPower (P := P) (b := b) i n row column : S) := by ring
      _ = (integralChevalleyRootScale (P := P) u i : S) ^ n *
          (rootDividedPower (P := P) (b := b) i n row column : S) := by
        rw [hratioVal]
      _ = _ := rfl

private lemma rootDividedPower_torus_entry_mul {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) (n : ℕ)
    (row column : b.support ⊕ ι) (c : S) :
    ((((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
          (c * specializeMatrix (S := S)
            (rootDividedPower (P := P) (b := b) i n) row column)) *
          ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S) =
      c * (((integralChevalleyRootScale (P := P) u i : S) ^ n) *
        specializeMatrix (S := S)
          (rootDividedPower (P := P) (b := b) i n) row column) := by
  rw [show ((((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
          (c * specializeMatrix (S := S)
            (rootDividedPower (P := P) (b := b) i n) row column)) *
          ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S) =
      c * ((((chevalleyBasisTorusUnit (P := P) u row)⁻¹ : Sˣ) : S) *
        specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i n)
          row column *
        ((chevalleyBasisTorusUnit (P := P) u column : Sˣ) : S)) by ring]
  rw [rootDividedPower_torus_entry]

/-- Exact conjugation of every characteristic-free root curve by the source split torus. -/
theorem integralChevalleyRootCurve_torus_conjugation {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι) (t : S) :
    (integralChevalleyTorusElement (P := P) u)⁻¹ *
        rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t *
        integralChevalleyTorusElement (P := P) u =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i
        ((integralChevalleyRootScale (P := P) u i : S) * t) := by
  apply Units.ext
  change Matrix.diagonal
        (fun a : b.support ⊕ ι =>
          (((chevalleyBasisTorusUnit (P := P) u a)⁻¹ : Sˣ) : S)) *
      rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i t *
      Matrix.diagonal (fun a : b.support ⊕ ι =>
        ((chevalleyBasisTorusUnit (P := P) u a : Sˣ) : S)) =
    rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i
      ((integralChevalleyRootScale (P := P) u i : S) * t)
  ext row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [rootCurveMatrix, integralChevalleyRootOperators, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_add, mul_add, mul_add, add_mul, add_mul, add_mul]
  rw [rootDividedPower_torus_entry_mul (P := P) u i 1 row column t,
    rootDividedPower_torus_entry_mul (P := P) u i 2 row column (t ^ 2),
    rootDividedPower_torus_entry_mul (P := P) u i 3 row column (t ^ 3)]
  by_cases hrc : row = column
  · subst column
    simp
    ring
  · simp [hrc]
    ring

/-- A source-torus parameter supported at one simple coroot. -/
def integralChevalleySimpleCorootParameter {S : Type*} [CommRing S]
    (q : b.support) (u : Sˣ) : IntegralChevalleyTorusParameter (b := b) S :=
  fun r => if r = q then u else 1

@[simp] theorem integralChevalleyRootScale_simpleCorootParameter
    {S : Type*} [CommRing S] (q : b.support) (u : Sˣ) (i : ι) :
    integralChevalleyRootScale (P := P)
        (integralChevalleySimpleCorootParameter (b := b) q u) i =
      u ^ P.pairingIn ℤ i q := by
  classical
  simp [integralChevalleyRootScale, integralChevalleySimpleCorootParameter]

/-- Conjugation by one simple-coroot coordinate has precisely the Cartan pairing weight. -/
theorem integralChevalleyRootCurve_simpleCoroot_conjugation
    {S : Type*} [CommRing S] (q : b.support) (u : Sˣ) (i : ι) (t : S) :
    (integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter (b := b) q u))⁻¹ *
        rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t *
        integralChevalleyTorusElement (P := P)
          (integralChevalleySimpleCorootParameter (b := b) q u) =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i
        (((u ^ P.pairingIn ℤ i q : Sˣ) : S) * t) := by
  simpa using integralChevalleyRootCurve_torus_conjugation (P := P) (b := b)
    (integralChevalleySimpleCorootParameter (b := b) q u) i t

/--
The certified split-torus action on the integral Cartan-plus-root Chevalley lattice.

The source parameters need not act faithfully.  The final two character fields retain the
exact equivalence relation and kernel detected by all root characters, which is the form
needed when the matrix image rather than the parameter torus is used as a carrier.
-/
structure IntegralChevalleyTorusConjugation
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] where
  torusElement : IntegralChevalleyTorusParameter (b := b) S →
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ
  torusElement_apply : ∀ u,
    torusElement u = integralChevalleyTorusElement (P := P) u
  titsLift_grading : ∀ i : b.support,
    RespectsChevalleyGrading (P := P) (titsLift (P := P) i) (P.reflectionPerm i)
  titsLiftInv_grading : ∀ i : b.support,
    RespectsChevalleyGrading (P := P) (titsLiftInv (P := P) i) (P.reflectionPerm i)
  titsWord_grading : ∀ word : List b.support,
    RespectsChevalleyGrading (P := P) (titsWord (P := P) word)
      (inverseReflectionWord (P := P) word)
  titsWordInv_grading : ∀ word : List b.support,
    RespectsChevalleyGrading (P := P) (titsWordInv (P := P) word)
      (reflectionWord (P := P) word)
  dividedPower_homogeneous : ∀ (i : ι) (n : ℕ),
    IsChevalleyHomogeneous (P := P) (rootDividedPower (P := P) (b := b) i n)
      (fun q => (n : ℤ) * P.pairingIn ℤ i q)
  torus_one : torusElement (1 : IntegralChevalleyTorusParameter (b := b) S) = 1
  torus_mul : ∀ u v : IntegralChevalleyTorusParameter (b := b) S,
    torusElement (u * v) = torusElement u * torusElement v
  torus_inv : ∀ u : IntegralChevalleyTorusParameter (b := b) S,
    torusElement (u⁻¹) = (torusElement u)⁻¹
  rootScale_mul : ∀ (u v : IntegralChevalleyTorusParameter (b := b) S) (i : ι),
    integralChevalleyRootScale (P := P) (u * v) i =
      integralChevalleyRootScale (P := P) u i *
        integralChevalleyRootScale (P := P) v i
  rootScale_inv : ∀ (u : IntegralChevalleyTorusParameter (b := b) S) (i : ι),
    integralChevalleyRootScale (P := P) u⁻¹ i =
      (integralChevalleyRootScale (P := P) u i)⁻¹
  character_compatibility : ∀ u v : IntegralChevalleyTorusParameter (b := b) S,
    torusElement u = torusElement v ↔
      ∀ i, integralChevalleyRootScale (P := P) u i =
        integralChevalleyRootScale (P := P) v i
  kernel_compatibility : ∀ u : IntegralChevalleyTorusParameter (b := b) S,
    torusElement u = 1 ↔
      ∀ i, integralChevalleyRootScale (P := P) u i = 1
  rootCurve_conjugation : ∀ (u : IntegralChevalleyTorusParameter (b := b) S)
      (i : ι) (t : S),
    (torusElement u)⁻¹ *
        rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t *
        torusElement u =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i
        ((integralChevalleyRootScale (P := P) u i : S) * t)
  simpleCoroot_weight : ∀ (q : b.support) (u : Sˣ) (i : ι),
    integralChevalleyRootScale (P := P)
        (integralChevalleySimpleCorootParameter (b := b) q u) i =
      u ^ P.pairingIn ℤ i q
  simpleCoroot_conjugation : ∀ (q : b.support) (u : Sˣ) (i : ι) (t : S),
    (torusElement (integralChevalleySimpleCorootParameter (b := b) q u))⁻¹ *
        rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t *
        torusElement (integralChevalleySimpleCorootParameter (b := b) q u) =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i
        (((u ^ P.pairingIn ℤ i q : Sˣ) : S) * t)

/-- The canonical split-torus conjugation certificate over an arbitrary commutative ring. -/
def integralChevalleyTorusConjugation {S : Type*} [CommRing S] :
    IntegralChevalleyTorusConjugation P b S where
  torusElement := integralChevalleyTorusElement (P := P)
  torusElement_apply := fun _ => rfl
  titsLift_grading := titsLift_respectsChevalleyGrading (P := P) (b := b)
  titsLiftInv_grading := titsLiftInv_respectsChevalleyGrading (P := P) (b := b)
  titsWord_grading := titsWord_respectsChevalleyGrading (P := P) (b := b)
  titsWordInv_grading := titsWordInv_respectsChevalleyGrading (P := P) (b := b)
  dividedPower_homogeneous := rootDividedPower_isChevalleyHomogeneous (P := P) (b := b)
  torus_one := integralChevalleyTorusElement_one (P := P) (b := b)
  torus_mul := integralChevalleyTorusElement_mul (P := P) (b := b)
  torus_inv := integralChevalleyTorusElement_inv (P := P) (b := b)
  rootScale_mul := integralChevalleyRootScale_mul (P := P) (b := b)
  rootScale_inv := integralChevalleyRootScale_inv (P := P) (b := b)
  character_compatibility :=
    integralChevalleyTorusElement_eq_iff_rootScale_eq (P := P) (b := b)
  kernel_compatibility :=
    integralChevalleyTorusElement_eq_one_iff_rootScale_eq_one (P := P) (b := b)
  rootCurve_conjugation :=
    integralChevalleyRootCurve_torus_conjugation (P := P) (b := b)
  simpleCoroot_weight :=
    integralChevalleyRootScale_simpleCorootParameter (P := P) (b := b)
  simpleCoroot_conjugation :=
    integralChevalleyRootCurve_simpleCoroot_conjugation (P := P) (b := b)

/-- Integral split-torus conjugation exists after base change to every commutative ring. -/
theorem integralChevalleyTorusConjugation_exists {S : Type*} [CommRing S] :
    Nonempty (IntegralChevalleyTorusConjugation P b S) :=
  ⟨integralChevalleyTorusConjugation (P := P) (b := b) (S := S)⟩

end

end


end RootPairing.IntegralGeckConstruction
