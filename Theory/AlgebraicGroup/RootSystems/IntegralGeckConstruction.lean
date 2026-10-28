module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple

/-!
# Integral Geck operators and Tits lifts

For a finite reduced crystallographic root pairing with a chosen base, this module constructs
Geck's simple-root operators over the coefficient-independent lattice
`(b.support ⊕ ι) → ℤ`.  Their root-string columns give integral divided powers, whose
recurrence, factorial, multiplication, and uniform nilpotence identities are proved directly.
Finite divided-power sums then define characteristic-free positive and negative unipotent
operators.

The associated Tits matrices are proved mutually inverse.  Their action reverses each simple
root string with the expected integral sign, so a product along a word transports every root
basis line according to the corresponding word of simple reflections.  Matrix exchange and
conjugation formulas relate the positive and negative unipotents.  Finally, scalar extension
along `ℤ → R` identifies both simple operators and their vector actions with Mathlib's
`RootPairing.GeckConstruction` over any characteristic-zero field (and, more generally, over
the commutative domains admitted by that construction).

The proof is componentwise and never assumes irreducibility.  Its mathematical input is the
root-string theory used in Geck's 2017 construction; the integral binomial coefficients make
the divided powers independent of the target coefficient ring.  This module is the simple-root
foundation for the all-root integral Chevalley operators and root curves constructed downstream.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The finite free integral carrier, with Cartan coordinates followed by root coordinates. -/
abbrev Carrier := b.support ⊕ ι → ℤ

/-- The Cartan basis vector indexed by a simple root. -/
abbrev u (i : b.support) : Carrier (b := b) :=
  Pi.single (Sum.inl i) 1

/-- The root basis vector indexed by a root. -/
abbrev v (i : ι) : Carrier (b := b) :=
  Pi.single (Sum.inr i) 1

/-- Geck's positive simple-root operator, defined over `ℤ`. -/
def eMatrix (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j ↦ if i' = i then |b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/-- Geck's negative simple-root operator, defined over `ℤ`. -/
def fMatrix (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = -i then |b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

lemma map_eMatrix (i : b.support) :
    (eMatrix i).map (algebraMap ℤ R) = RootPairing.GeckConstruction.e i := by
  let := P.indexNeg
  ext (j | j) (k | k) <;>
    simp [eMatrix, RootPairing.GeckConstruction.e]

lemma map_fMatrix (i : b.support) :
    (fMatrix i).map (algebraMap ℤ R) = RootPairing.GeckConstruction.f i := by
  let := P.indexNeg
  ext (j | j) (k | k) <;>
    simp [fMatrix, RootPairing.GeckConstruction.f]

private lemma eq_of_map_eq {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ}
    (h : A.map (algebraMap ℤ R) = B.map (algebraMap ℤ R)) : A = B := by
  ext j k
  exact FaithfulSMul.algebraMap_injective ℤ R <| congrFun (congrFun h j) k

lemma eMatrix_isNilpotent (i : b.support) : IsNilpotent (eMatrix i) := by
  obtain ⟨n, hn⟩ := RootPairing.GeckConstruction.isNilpotent_e i
  refine ⟨n, eq_of_map_eq (R := R) ?_⟩
  rw [Matrix.map_pow, map_eMatrix, hn]
  simp

lemma fMatrix_isNilpotent (i : b.support) : IsNilpotent (fMatrix i) := by
  obtain ⟨n, hn⟩ := RootPairing.GeckConstruction.isNilpotent_f i
  refine ⟨n, eq_of_map_eq (R := R) ?_⟩
  rw [Matrix.map_pow, map_fMatrix, hn]
  simp

lemma eMatrix_mulVec_u (i j : b.support) :
    eMatrix i *ᵥ u j = |b.cartanMatrix i j| • v (b := b) i := by
  ext (k | k) <;> simp [eMatrix, u, v, Pi.single_apply]

lemma eMatrix_mulVec_v_neg (i : b.support) :
    letI := P.indexNeg
    eMatrix i *ᵥ v (b := b) (-i) = u i := by
  letI := P.indexNeg
  ext (k | k)
  · simp [eMatrix, u, v, Pi.single_apply]
  · have hk : P.root k ≠ P.root i + P.root (-i) := by simp [P.ne_zero]
    simp [eMatrix, u, v, P.ne_zero]

lemma eMatrix_mulVec_v_add {i : b.support} {j k : ι}
    (h : P.root k = P.root i + P.root j) :
    eMatrix i *ᵥ v (b := b) j =
      (P.chainBotCoeff i j + 1 : ℤ) • v (b := b) k := by
  letI := P.indexNeg
  have hj : j ≠ -i := by
    rintro rfl
    exact P.ne_zero k (by simpa using h)
  have hj' : j ≠ P.reflectionPerm i i := by simpa using hj
  ext (l | l)
  · simp [eMatrix, v, hj']
  · simp [eMatrix, v, Pi.single_apply, ← h]

lemma eMatrix_mulVec_v_zero {i : b.support} {j : ι}
    (hneg : letI := P.indexNeg; j ≠ -i)
    (hadd : P.root i + P.root j ∉ Set.range P.root) :
    eMatrix i *ᵥ v (b := b) j = 0 := by
  letI := P.indexNeg
  have hneg' : j ≠ P.reflectionPerm i i := by simpa using hneg
  ext (k | k)
  · simp [eMatrix, v, hneg']
  · have hk : P.root k ≠ P.root i + P.root j := fun hk ↦ hadd ⟨k, hk⟩
    simp [eMatrix, v, Pi.single_apply, hk]

lemma fMatrix_mulVec_u (i j : b.support) :
    fMatrix i *ᵥ u j =
      |b.cartanMatrix i j| • v (b := b) (P.reflectionPerm i i) := by
  letI := P.indexNeg
  ext (k | k) <;> simp [fMatrix, u, v, Pi.single_apply]

lemma fMatrix_mulVec_v_same (i : b.support) :
    fMatrix i *ᵥ v (b := b) i = u i := by
  ext (k | k)
  · simp [fMatrix, u, v, Pi.single_apply]
  · have hk : P.root k ≠ P.root i - P.root i := by simp [P.ne_zero]
    simp [fMatrix, u, v, P.ne_zero]

lemma fMatrix_mulVec_v_sub {i : b.support} {j k : ι}
    (h : P.root k = P.root j - P.root i) :
    fMatrix i *ᵥ v (b := b) j =
      (P.chainTopCoeff i j + 1 : ℤ) • v (b := b) k := by
  have hj : j ≠ i := by
    rintro rfl
    exact P.ne_zero k (by simpa using h)
  ext (l | l)
  · simp [fMatrix, v, Pi.single_apply, hj]
  · have hl : P.root l = P.root j - P.root i ↔ l = k := by
      rw [← h, EmbeddingLike.apply_eq_iff_eq]
    simp [fMatrix, v, hl, Pi.single_apply]

lemma fMatrix_mulVec_v_zero {i : b.support} {j : ι}
    (hsame : j ≠ i)
    (hsub : P.root j - P.root i ∉ Set.range P.root) :
    fMatrix i *ᵥ v (b := b) j = 0 := by
  ext (k | k)
  · simp [fMatrix, v, Pi.single_apply, hsame]
  · have hk : P.root k ≠ P.root j - P.root i := fun hk ↦ hsub ⟨k, hk⟩
    simp [fMatrix, v, Pi.single_apply, hk]

private lemma root_add_nsmul_mem_of_succ (i : b.support) (j : ι) {n : ℕ} (hn : 2 ≤ n)
    (h : P.root j + (n + 1) • P.root i ∈ Set.range P.root) :
    P.root j + n • P.root i ∈ Set.range P.root := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  by_cases hji : j = i
  · subst j
    obtain ⟨k, hk⟩ := h
    haveI : (n + 2).AtLeastTwo := ⟨by lia⟩
    exfalso
    exact (P.nsmul_notMem_range_root (n := n + 2) (i := i))
      ⟨k, by rw [hk]; module⟩
  by_cases hjneg : j = -i
  · subst j
    obtain ⟨k, hk⟩ := h
    haveI : n.AtLeastTwo := ⟨hn⟩
    exfalso
    exact (P.nsmul_notMem_range_root (n := n) (i := i))
      ⟨k, by rw [hk]; simp; module⟩
  have hlin : LinearIndependent R ![P.root i, P.root j] := by
    refine IsReduced.linearIndependent P (Ne.symm hji) fun hij ↦ ?_
    apply hjneg
    apply P.root.injective
    rw [show P.root (-i) = -P.root i by simp]
    exact ((neg_eq_iff_eq_neg).2 hij).symm
  rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin] at h ⊢
  omega

private lemma root_of_root_add_nsmul_ne_reflection_self
    (i : b.support) (j k : ι) {n : ℕ} (hn : 2 ≤ n)
    (hk : P.root k = P.root j + n • P.root i) : k ≠ P.reflectionPerm i i := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  rintro rfl
  haveI : (n + 1).AtLeastTwo := ⟨by lia⟩
  apply P.nsmul_notMem_range_root (n := n + 1) (i := i)
  refine ⟨P.reflectionPerm j j, ?_⟩
  rw [root_reflectionPerm, reflection_apply_self]
  have hk' : -P.root i = P.root j + n • P.root i := by
    simpa only [root_reflectionPerm, reflection_apply_self] using hk
  have hj : P.root j = -P.root i - n • P.root i := eq_sub_of_add_eq hk'.symm
  rw [hj]
  module

private lemma chainBotCoeff_of_add_nsmul {i : b.support} {j k : ι} {n : ℕ}
    (hlin : LinearIndependent R ![P.root i, P.root j])
    (hk : P.root k = P.root j + n • P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + n := by
  induction n generalizing k with
  | zero =>
      have : k = j := P.root.injective <| by simpa using hk
      subst k
      simp
  | succ n ih =>
      have hkn : P.root j + n • P.root i ∈ Set.range P.root := by
        rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
        have hks : P.root j + (n + 1) • P.root i ∈ Set.range P.root := ⟨k, hk⟩
        rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin] at hks
        omega
      obtain ⟨l, hl⟩ := hkn
      have hlinl : LinearIndependent R ![P.root i, P.root l] := by
        rw [hl, add_comm, ← natCast_zsmul, LinearIndependent.pair_add_smul_right_iff]
        exact hlin
      have hkl : P.root k = P.root l + P.root i := by rw [hk, hl]; module
      rw [P.chainBotCoeff_of_add hlinl hkl, ih hl]
      omega

/-- The integral divided powers of the positive simple-root operator. -/
def eDividedPower (i : b.support) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  open scoped Classical in
  match n with
  | 0 => 1
  | 1 => eMatrix i
  | n + 2 =>
    Matrix.of fun row column =>
      match row, column with
      | Sum.inr k, Sum.inr j =>
          if P.root k = P.root j + (n + 2) • P.root i then
            (P.chainBotCoeff i j + n + 2).choose (n + 2)
          else 0
      | _, _ => 0

@[simp] lemma eDividedPower_zero (i : b.support) :
    eDividedPower i 0 = 1 := rfl

@[simp] lemma eDividedPower_one (i : b.support) :
    eDividedPower i 1 = eMatrix i := rfl

lemma eDividedPower_add_two_mulVec_u (i j : b.support) (n : ℕ) :
    eDividedPower i (n + 2) *ᵥ u j = 0 := by
  ext (k | k) <;> simp [eDividedPower, u, Pi.single_apply]

lemma eDividedPower_add_two_mulVec_v {i : b.support} {j k : ι} (n : ℕ)
    (h : P.root k = P.root j + (n + 2) • P.root i) :
    eDividedPower i (n + 2) *ᵥ v (b := b) j =
      ((P.chainBotCoeff i j + n + 2).choose (n + 2) : ℤ) • v (b := b) k := by
  ext (l | l)
  · simp [eDividedPower, v, Pi.single_apply]
  · have hl : P.root l = P.root j + (n + 2) • P.root i ↔ l = k := by
      rw [← h, EmbeddingLike.apply_eq_iff_eq]
    simp [eDividedPower, v, hl, Pi.single_apply]

lemma eDividedPower_add_two_mulVec_v_zero (i : b.support) (j : ι) (n : ℕ)
    (h : P.root j + (n + 2) • P.root i ∉ Set.range P.root) :
    eDividedPower i (n + 2) *ᵥ v (b := b) j = 0 := by
  ext (k | k)
  · simp [eDividedPower, v, Pi.single_apply]
  · have hk : P.root k ≠ P.root j + (n + 2) • P.root i := fun hk ↦ h ⟨k, hk⟩
    simp [eDividedPower, v, hk, Pi.single_apply]

private lemma eMatrix_mul_eDividedPower_of_two_le (i : b.support) {n : ℕ} (hn : 2 ≤ n) :
    eMatrix i * eDividedPower i n = (n + 1) • eDividedPower i (n + 1) := by
  apply Matrix.ext_col
  rintro (j | j)
  · rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one,
      ← Matrix.mulVec_mulVec]
    rw [Matrix.smul_mulVec]
    change eMatrix i *ᵥ (eDividedPower i n *ᵥ u j) =
      (n + 1 : ℤ) • (eDividedPower i (n + 1) *ᵥ u j)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    subst n
    rw [Nat.add_comm 2 m]
    rw [eDividedPower_add_two_mulVec_u i j m]
    rw [eDividedPower_add_two_mulVec_u i j (m + 1)]
    simp
  · rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one,
      ← Matrix.mulVec_mulVec]
    rw [Matrix.smul_mulVec]
    change eMatrix i *ᵥ (eDividedPower i n *ᵥ v (b := b) j) =
      (n + 1 : ℤ) • (eDividedPower i (n + 1) *ᵥ v (b := b) j)
    by_cases hcur : P.root j + n • P.root i ∈ Set.range P.root
    · obtain ⟨k, hk⟩ := hcur
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
      subst n
      rw [Nat.add_comm 2 m] at hk ⊢
      rw [eDividedPower_add_two_mulVec_v (n := m) hk, Matrix.mulVec_smul]
      have hkneg := root_of_root_add_nsmul_ne_reflection_self i j k (by omega) hk
      by_cases hnext : P.root j + (m + 2 + 1) • P.root i ∈ Set.range P.root
      · obtain ⟨l, hl⟩ := hnext
        have hkl : P.root l = P.root i + P.root k := by rw [hl, hk]; module
        rw [eMatrix_mulVec_v_add hkl]
        rw [eDividedPower_add_two_mulVec_v (n := m + 1) (by simpa using hl)]
        have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
        have : IsAddTorsionFree M := .of_isTorsionFree R M
        let := P.indexNeg
        have hlin : LinearIndependent R ![P.root i, P.root j] := by
          refine IsReduced.linearIndependent P ?_ ?_
          · rintro rfl
            haveI : (m + 4).AtLeastTwo := ⟨by omega⟩
            exact P.nsmul_notMem_range_root (n := m + 4) (i := i)
              ⟨l, by rw [hl]; module⟩
          · intro hij
            have hj : P.root j = -P.root i := ((neg_eq_iff_eq_neg).2 hij).symm
            haveI : (m + 2).AtLeastTwo := ⟨by omega⟩
            exact P.nsmul_notMem_range_root (n := m + 2) (i := i)
              ⟨l, by rw [hl, hj]; module⟩
        rw [chainBotCoeff_of_add_nsmul hlin hk]
        simp only [smul_smul]
        congr 1
        norm_cast
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using
          Nat.add_one_mul_choose_eq (P.chainBotCoeff i j + m + 2) (m + 2)
      · have hknext : P.root i + P.root k ∉ Set.range P.root := by
          intro h
          apply hnext
          obtain ⟨l, hl⟩ := h
          exact ⟨l, by rw [hl, hk]; module⟩
        rw [eMatrix_mulVec_v_zero hkneg hknext]
        rw [eDividedPower_add_two_mulVec_v_zero i j (m + 1) hnext]
        simp
    · have hnext : P.root j + (n + 1) • P.root i ∉ Set.range P.root := fun h ↦
        hcur (root_add_nsmul_mem_of_succ i j hn h)
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
      subst n
      rw [Nat.add_comm 2 m] at hcur hnext ⊢
      rw [eDividedPower_add_two_mulVec_v_zero i j m hcur]
      rw [eDividedPower_add_two_mulVec_v_zero i j (m + 1) hnext]
      simp

private lemma root_add_mem_of_root_add_two_nsmul_mem (i : b.support) {j : ι}
    (hjneg : letI := P.indexNeg; j ≠ -i)
    (h : P.root j + 2 • P.root i ∈ Set.range P.root) :
    P.root j + P.root i ∈ Set.range P.root := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  by_cases hji : j = i
  · subst j
    obtain ⟨k, hk⟩ := h
    haveI : (3 : ℕ).AtLeastTwo := ⟨by omega⟩
    exfalso
    exact P.nsmul_notMem_range_root (n := 3) (i := i) ⟨k, by rw [hk]; module⟩
  have hlin : LinearIndependent R ![P.root i, P.root j] := by
    refine IsReduced.linearIndependent P (Ne.symm hji) fun hij ↦ ?_
    apply hjneg
    apply P.root.injective
    rw [show P.root (-i) = -P.root i by simp]
    exact ((neg_eq_iff_eq_neg).2 hij).symm
  rw [show P.root j + P.root i = P.root j + 1 • P.root i by simp]
  rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin] at h ⊢
  omega

private lemma eMatrix_mul_eMatrix (i : b.support) :
    eMatrix i * eMatrix i = 2 • eDividedPower i 2 := by
  let := P.indexNeg
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  apply Matrix.ext_col
  rintro (j | j)
  · rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]
    rw [Matrix.smul_mulVec]
    change eMatrix i *ᵥ (eMatrix i *ᵥ u j) =
      (2 : ℤ) • (eDividedPower i 2 *ᵥ u j)
    rw [eMatrix_mulVec_u, Matrix.mulVec_smul]
    have hneg : (i : ι) ≠ -i := ne_neg P i
    have hadd : P.root i + P.root i ∉ Set.range P.root := by
      haveI : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
      intro h
      apply P.nsmul_notMem_range_root (n := 2) (i := i)
      simpa [two_smul] using h
    rw [eMatrix_mulVec_v_zero hneg hadd]
    rw [eDividedPower_add_two_mulVec_u i j 0]
    simp
  · rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]
    rw [Matrix.smul_mulVec]
    change eMatrix i *ᵥ (eMatrix i *ᵥ v (b := b) j) =
      (2 : ℤ) • (eDividedPower i 2 *ᵥ v (b := b) j)
    by_cases hjneg : j = -i
    · subst j
      rw [eMatrix_mulVec_v_neg, eMatrix_mulVec_u]
      have htop : P.chainTopCoeff i i = 0 :=
        P.chainTopCoeff_of_not_linearIndependent (by
          simp_rw [LinearIndependent.pair_iff, not_forall]
          exact ⟨1, -1, by simp, by simp⟩)
      have hdiv : eDividedPower i 2 *ᵥ v (b := b) (-i : ι) = v (b := b) i := by
        simpa [htop] using
          eDividedPower_add_two_mulVec_v (i := i) (j := (-i : ι))
            (n := 0) (k := (i : ι)) (by simp; module)
      rw [hdiv]
      simp [RootPairing.chainBotCoeff_of_not_linearIndependent]
    · by_cases hadd : P.root i + P.root j ∈ Set.range P.root
      · obtain ⟨k, hk⟩ := hadd
        have hki : k ≠ -i := by
          rintro rfl
          haveI : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
          apply P.nsmul_notMem_range_root (n := 2) (i := i)
          refine ⟨-j, ?_⟩
          rw [show P.root (-j) = -P.root j by simp]
          have hk' : -P.root i = P.root i + P.root j := by simpa using hk
          calc
            -P.root j = -(P.root i + P.root j) + P.root i := by abel
            _ = -(-P.root i) + P.root i := by rw [← hk']
            _ = 2 • P.root i := by module
        rw [eMatrix_mulVec_v_add hk, Matrix.mulVec_smul]
        by_cases hadd2 : P.root j + 2 • P.root i ∈ Set.range P.root
        · obtain ⟨l, hl⟩ := hadd2
          have hkl : P.root l = P.root i + P.root k := by rw [hl, hk]; module
          rw [eMatrix_mulVec_v_add hkl]
          rw [eDividedPower_add_two_mulVec_v (n := 0) hl]
          have hlin : LinearIndependent R ![P.root i, P.root j] := by
            refine IsReduced.linearIndependent P ?_ ?_
            · rintro rfl
              haveI : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
              exact P.nsmul_notMem_range_root (n := 2) (i := i) ⟨k, by rw [hk]; module⟩
            · intro hij
              exact hjneg (P.root.injective <| by
                rw [show P.root (-i) = -P.root i by simp]
                exact ((neg_eq_iff_eq_neg).2 hij).symm)
          have hbot : P.chainBotCoeff i k = P.chainBotCoeff i j + 1 :=
            P.chainBotCoeff_of_add (i := i) (j := j) hlin (by simpa [add_comm] using hk)
          rw [hbot]
          simp only [smul_smul]
          congr 1
          have hcoeff := Nat.add_one_mul_choose_eq (P.chainBotCoeff i j + 1) 1
          have harg : P.chainBotCoeff i j + 1 + 1 = P.chainBotCoeff i j + 2 := by omega
          rw [harg] at hcoeff
          simp only [Nat.choose_one_right] at hcoeff
          exact_mod_cast (by simpa [Nat.mul_comm] using hcoeff)
        · have hknext : P.root i + P.root k ∉ Set.range P.root := by
            intro hmem
            apply hadd2
            obtain ⟨l, hl⟩ := hmem
            exact ⟨l, by rw [hl, hk]; module⟩
          rw [eMatrix_mulVec_v_zero hki hknext]
          rw [eDividedPower_add_two_mulVec_v_zero i j 0 hadd2]
          simp
      · have hadd2 : P.root j + 2 • P.root i ∉ Set.range P.root := fun hmem ↦
          hadd (by simpa [add_comm] using root_add_mem_of_root_add_two_nsmul_mem i hjneg hmem)
        rw [eMatrix_mulVec_v_zero hjneg hadd]
        rw [eDividedPower_add_two_mulVec_v_zero i j 0 hadd2]
        simp

lemma eMatrix_mul_eDividedPower (i : b.support) (n : ℕ) :
    eMatrix i * eDividedPower i n = (n + 1) • eDividedPower i (n + 1) := by
  rcases n with (_ | _ | n)
  · simp
  · simpa using eMatrix_mul_eMatrix i
  · exact eMatrix_mul_eDividedPower_of_two_le i (by omega)

lemma eMatrix_pow_eq_factorial_smul (i : b.support) (n : ℕ) :
    eMatrix i ^ n = n.factorial • eDividedPower i n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        eMatrix i ^ (n + 1) = eMatrix i * eMatrix i ^ n := pow_succ' _ _
        _ = eMatrix i * (n.factorial • eDividedPower i n) := by rw [ih]
        _ = (n.factorial : ℤ) • (eMatrix i * eDividedPower i n) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ, Matrix.mul_smul]
        _ = (n.factorial : ℤ) • ((n + 1) • eDividedPower i (n + 1)) := by
          rw [eMatrix_mul_eDividedPower]
        _ = (n + 1).factorial • eDividedPower i (n + 1) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
          norm_num [Nat.factorial_succ, mul_comm]

lemma eDividedPower_mul (i : b.support) (m n : ℕ) :
    eDividedPower i m * eDividedPower i n =
      (m + n).choose m • eDividedPower i (m + n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrec := eMatrix_mul_eDividedPower i m
      have hrec' := eMatrix_mul_eDividedPower i (m + n)
      have ih' := ih
      rw [← Nat.cast_smul_eq_nsmul ℤ] at hrec hrec' ih'
      have hscaled : (m + 1) •
          (eDividedPower i (m + 1) * eDividedPower i n) =
          (m + 1) • ((m + 1 + n).choose (m + 1) •
            eDividedPower i (m + 1 + n)) := by
        simp only [← Nat.cast_smul_eq_nsmul ℤ]
        calc
          (m + 1 : ℤ) • (eDividedPower i (m + 1) * eDividedPower i n) =
              ((m + 1 : ℤ) • eDividedPower i (m + 1)) * eDividedPower i n := by
                rw [Matrix.smul_mul]
          _ = (eMatrix i * eDividedPower i m) * eDividedPower i n := by
                rw [hrec]
                norm_num
          _ = eMatrix i * (eDividedPower i m * eDividedPower i n) := by
                rw [mul_assoc]
          _ = eMatrix i * ((↑((m + n).choose m) : ℤ) • eDividedPower i (m + n)) := by
                rw [ih']
          _ = (↑((m + n).choose m) : ℤ) •
              (eMatrix i * eDividedPower i (m + n)) := by rw [Matrix.mul_smul]
          _ = (↑((m + n).choose m) : ℤ) •
              ((m + n + 1 : ℤ) • eDividedPower i (m + n + 1)) := by
                rw [hrec']
                norm_num
          _ = (m + 1 : ℤ) •
              ((↑((m + 1 + n).choose (m + 1)) : ℤ) •
                eDividedPower i (m + 1 + n)) := by
                simp only [smul_smul]
                congr 1
                · exact_mod_cast (by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using
                      Nat.add_one_mul_choose_eq (m + n) m)
                · congr 1 <;> omega
      apply Matrix.ext
      intro row column
      have hs := congrFun (congrFun hscaled row) column
      change (m + 1) •
          (eDividedPower i (m + 1) * eDividedPower i n) row column =
        (m + 1) • (((m + 1 + n).choose (m + 1)) •
          eDividedPower i (m + 1 + n)) row column at hs
      exact nsmul_right_injective (show m + 1 ≠ 0 by omega) hs

/-- The integral involution exchanging positive and negative Geck operators. -/
def omegaMatrix : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

lemma map_omegaMatrix :
    (omegaMatrix (P := P) (b := b)).map (algebraMap ℤ R) =
      RootPairing.GeckConstruction.ω b := by
  let := P.indexNeg
  ext (j | j) (k | k) <;>
    simp [omegaMatrix, RootPairing.GeckConstruction.ω, Matrix.one_apply]

@[simp] lemma omegaMatrix_sq :
    omegaMatrix (P := P) (b := b) * omegaMatrix = 1 := by
  apply eq_of_map_eq (R := R)
  rw [Matrix.map_mul, map_omegaMatrix,
    RootPairing.GeckConstruction.ω_mul_ω]
  simp

lemma omegaMatrix_mul_eMatrix (i : b.support) :
    omegaMatrix (P := P) (b := b) * eMatrix i = fMatrix i * omegaMatrix := by
  apply eq_of_map_eq (R := R)
  rw [Matrix.map_mul, Matrix.map_mul, map_omegaMatrix, map_eMatrix, map_fMatrix,
    RootPairing.GeckConstruction.ω_mul_e]

lemma omegaMatrix_mul_fMatrix (i : b.support) :
    omegaMatrix (P := P) (b := b) * fMatrix i = eMatrix i * omegaMatrix := by
  apply eq_of_map_eq (R := R)
  rw [Matrix.map_mul, Matrix.map_mul, map_omegaMatrix, map_fMatrix, map_eMatrix,
    RootPairing.GeckConstruction.ω_mul_f]

@[simp] lemma omegaMatrix_mulVec_u (j : b.support) :
    omegaMatrix (P := P) (b := b) *ᵥ u j = u j := by
  let := P.indexNeg
  ext (k | k) <;> simp [omegaMatrix, u, Pi.single_apply, Matrix.one_apply]

@[simp] lemma omegaMatrix_mulVec_v (j : ι) :
    letI := P.indexNeg
    omegaMatrix (P := P) (b := b) *ᵥ v (b := b) j = v (b := b) (-j) := by
  letI := P.indexNeg
  ext (k | k) <;> simp [omegaMatrix, v, Pi.single_apply]

/-- Integral divided powers of the negative simple-root operator. -/
def fDividedPower (i : b.support) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  omegaMatrix * eDividedPower i n * omegaMatrix

@[simp] lemma fDividedPower_zero (i : b.support) : fDividedPower i 0 = 1 := by
  simp [fDividedPower, mul_assoc]

@[simp] lemma fDividedPower_one (i : b.support) : fDividedPower i 1 = fMatrix i := by
  rw [fDividedPower, eDividedPower_one, omegaMatrix_mul_eMatrix, mul_assoc,
    omegaMatrix_sq, mul_one]

lemma fMatrix_mul_fDividedPower (i : b.support) (n : ℕ) :
    fMatrix i * fDividedPower i n = (n + 1) • fDividedPower i (n + 1) := by
  rw [fDividedPower, fDividedPower]
  calc
    fMatrix i * (omegaMatrix * eDividedPower i n * omegaMatrix) =
        (fMatrix i * omegaMatrix) * eDividedPower i n * omegaMatrix := by
          simp [mul_assoc]
    _ = (omegaMatrix * eMatrix i) * eDividedPower i n * omegaMatrix := by
          rw [← omegaMatrix_mul_eMatrix]
    _ =
        omegaMatrix * (eMatrix i * eDividedPower i n) * omegaMatrix := by
          simp [mul_assoc]
    _ = omegaMatrix * ((n + 1) • eDividedPower i (n + 1)) * omegaMatrix := by
          rw [eMatrix_mul_eDividedPower]
    _ = (n + 1) • (omegaMatrix * eDividedPower i (n + 1) * omegaMatrix) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ, Matrix.mul_smul, Matrix.smul_mul,
            Nat.cast_smul_eq_nsmul]

lemma fMatrix_pow_eq_factorial_smul (i : b.support) (n : ℕ) :
    fMatrix i ^ n = n.factorial • fDividedPower i n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        fMatrix i ^ (n + 1) = fMatrix i * fMatrix i ^ n := pow_succ' _ _
        _ = fMatrix i * (n.factorial • fDividedPower i n) := by rw [ih]
        _ = (n.factorial : ℤ) • (fMatrix i * fDividedPower i n) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ, Matrix.mul_smul]
        _ = (n.factorial : ℤ) • ((n + 1) • fDividedPower i (n + 1)) := by
          rw [fMatrix_mul_fDividedPower]
        _ = (n + 1).factorial • fDividedPower i (n + 1) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
          norm_num [Nat.factorial_succ, mul_comm]

lemma fDividedPower_mul (i : b.support) (m n : ℕ) :
    fDividedPower i m * fDividedPower i n =
      (m + n).choose m • fDividedPower i (m + n) := by
  rw [fDividedPower, fDividedPower, fDividedPower]
  have hmiddle :
      (omegaMatrix (P := P) (b := b) * eDividedPower i m * omegaMatrix) *
          (omegaMatrix * eDividedPower i n * omegaMatrix) =
        omegaMatrix * (eDividedPower i m * eDividedPower i n) * omegaMatrix := by
    rw [show (omegaMatrix * eDividedPower i m * omegaMatrix) *
        (omegaMatrix * eDividedPower i n * omegaMatrix) =
      omegaMatrix * eDividedPower i m * (omegaMatrix * omegaMatrix) *
        eDividedPower i n * omegaMatrix by noncomm_ring]
    simp [mul_assoc]
  rw [hmiddle, eDividedPower_mul]
  rw [← Nat.cast_smul_eq_nsmul ℤ, Matrix.mul_smul, Matrix.smul_mul,
    Nat.cast_smul_eq_nsmul]

lemma fDividedPower_add_two_mulVec_u (i j : b.support) (n : ℕ) :
    fDividedPower i (n + 2) *ᵥ u j = 0 := by
  rw [fDividedPower, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_u, eDividedPower_add_two_mulVec_u]
  simp

lemma fDividedPower_add_two_mulVec_v {i : b.support} {j k : ι} (n : ℕ)
    (h : P.root k = P.root j - (n + 2) • P.root i) :
    fDividedPower i (n + 2) *ᵥ v (b := b) j =
      ((P.chainTopCoeff i j + n + 2).choose (n + 2) : ℤ) • v (b := b) k := by
  let := P.indexNeg
  rw [fDividedPower, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_v]
  have hneg : P.root (-k) = P.root (-j) + (n + 2) • P.root i := by
    rw [show P.root (-k) = -P.root k by simp,
      show P.root (-j) = -P.root j by simp, h]
    module
  rw [eDividedPower_add_two_mulVec_v n hneg, Matrix.mulVec_smul,
    omegaMatrix_mulVec_v]
  have hcoeff : P.chainBotCoeff i (-j) = P.chainTopCoeff i j := by
    simpa using P.chainBotCoeff_reflectionPerm_right (i := i) (j := j)
  have hkk : -(-k) = k := neg_involutive k
  rw [hcoeff, hkk]

lemma fDividedPower_add_two_mulVec_v_zero (i : b.support) (j : ι) (n : ℕ)
    (h : P.root j - (n + 2) • P.root i ∉ Set.range P.root) :
    fDividedPower i (n + 2) *ᵥ v (b := b) j = 0 := by
  let := P.indexNeg
  rw [fDividedPower, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_v]
  have hneg : P.root (-j) + (n + 2) • P.root i ∉ Set.range P.root := by
    intro hmem
    apply h
    obtain ⟨k, hk⟩ := hmem
    refine ⟨-k, ?_⟩
    rw [show P.root (-k) = -P.root k by simp, hk,
      show P.root (-j) = -P.root j by simp]
    module
  rw [eDividedPower_add_two_mulVec_v_zero i (-j) n hneg]
  simp

private lemma root_add_nsmul_not_mem_of_four_le (i : b.support) (j : ι) {n : ℕ}
    (hn : 4 ≤ n) : P.root j + n • P.root i ∉ Set.range P.root := by
  let := P.indexNeg
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hji : j = i
  · subst j
    rintro ⟨k, hk⟩
    haveI : (n + 1).AtLeastTwo := ⟨by omega⟩
    exact P.nsmul_notMem_range_root (n := n + 1) (i := i)
      ⟨k, by rw [hk]; module⟩
  by_cases hjneg : j = -i
  · subst j
    rintro ⟨k, hk⟩
    haveI : (n - 1).AtLeastTwo := ⟨by omega⟩
    have hn' : n = (n - 1) + 1 := by omega
    exact P.nsmul_notMem_range_root (n := n - 1) (i := i)
      ⟨k, by rw [hk, hn', add_smul]; simp⟩
  have hlin : LinearIndependent R ![P.root i, P.root j] := by
    refine IsReduced.linearIndependent P (Ne.symm hji) fun hij ↦ ?_
    apply hjneg
    apply P.root.injective
    rw [show P.root (-i) = -P.root i by simp]
    exact ((neg_eq_iff_eq_neg).2 hij).symm
  intro hmem
  rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin] at hmem
  have hbound := chainBotCoeff_add_chainTopCoeff_le_three (P := P) (i := i) (j := j)
  omega

lemma eDividedPower_eq_zero_of_four_le (i : b.support) {n : ℕ} (hn : 4 ≤ n) :
    eDividedPower i n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm 2 m]
  have hnone (j : ι) : P.root j + (m + 2) • P.root i ∉ Set.range P.root :=
    root_add_nsmul_not_mem_of_four_le i j (by omega)
  ext (row | row) (column | column) <;> simp [eDividedPower]
  intro h
  exact (hnone column ⟨row, h⟩).elim

lemma fDividedPower_eq_zero_of_four_le (i : b.support) {n : ℕ} (hn : 4 ≤ n) :
    fDividedPower i n = 0 := by
  rw [fDividedPower, eDividedPower_eq_zero_of_four_le i hn]
  simp

/-- The integral divided-power exponential of the positive simple-root operator. -/
def eUnipotent (i : b.support) (t : ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  1 + t • eDividedPower i 1 + t ^ 2 • eDividedPower i 2 +
    t ^ 3 • eDividedPower i 3

/-- The integral divided-power exponential of the negative simple-root operator. -/
def fUnipotent (i : b.support) (t : ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  1 + t • fDividedPower i 1 + t ^ 2 • fDividedPower i 2 +
    t ^ 3 • fDividedPower i 3

@[simp] lemma eUnipotent_zero (i : b.support) : eUnipotent i 0 = 1 := by
  simp [eUnipotent]

@[simp] lemma fUnipotent_zero (i : b.support) : fUnipotent i 0 = 1 := by
  simp [fUnipotent]

lemma eUnipotent_add (i : b.support) (s t : ℤ) :
    eUnipotent i s * eUnipotent i t = eUnipotent i (s + t) := by
  have h11 : eDividedPower i 1 * eDividedPower i 1 = 2 • eDividedPower i 2 := by
    simpa using eDividedPower_mul i 1 1
  have h12 : eDividedPower i 1 * eDividedPower i 2 = 3 • eDividedPower i 3 := by
    simpa using eDividedPower_mul i 1 2
  have h21 : eDividedPower i 2 * eDividedPower i 1 = 3 • eDividedPower i 3 := by
    simpa using eDividedPower_mul i 2 1
  have h13 : eDividedPower i 1 * eDividedPower i 3 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      eDividedPower_mul i 1 3
  have h31 : eDividedPower i 3 * eDividedPower i 1 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      eDividedPower_mul i 3 1
  have h22 : eDividedPower i 2 * eDividedPower i 2 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      eDividedPower_mul i 2 2
  have h23 : eDividedPower i 2 * eDividedPower i 3 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 5 by omega)] using
      eDividedPower_mul i 2 3
  have h32 : eDividedPower i 3 * eDividedPower i 2 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 5 by omega)] using
      eDividedPower_mul i 3 2
  have h33 : eDividedPower i 3 * eDividedPower i 3 = 0 := by
    simpa [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 6 by omega)] using
      eDividedPower_mul i 3 3
  simp only [eUnipotent, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  simp only [smul_zero, add_zero, zero_add, zero_smul]
  module

lemma fUnipotent_add (i : b.support) (s t : ℤ) :
    fUnipotent i s * fUnipotent i t = fUnipotent i (s + t) := by
  have h11 : fDividedPower i 1 * fDividedPower i 1 = 2 • fDividedPower i 2 := by
    simpa using fDividedPower_mul i 1 1
  have h12 : fDividedPower i 1 * fDividedPower i 2 = 3 • fDividedPower i 3 := by
    simpa using fDividedPower_mul i 1 2
  have h21 : fDividedPower i 2 * fDividedPower i 1 = 3 • fDividedPower i 3 := by
    simpa using fDividedPower_mul i 2 1
  have h13 : fDividedPower i 1 * fDividedPower i 3 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      fDividedPower_mul i 1 3
  have h31 : fDividedPower i 3 * fDividedPower i 1 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      fDividedPower_mul i 3 1
  have h22 : fDividedPower i 2 * fDividedPower i 2 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega)] using
      fDividedPower_mul i 2 2
  have h23 : fDividedPower i 2 * fDividedPower i 3 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 5 by omega)] using
      fDividedPower_mul i 2 3
  have h32 : fDividedPower i 3 * fDividedPower i 2 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 5 by omega)] using
      fDividedPower_mul i 3 2
  have h33 : fDividedPower i 3 * fDividedPower i 3 = 0 := by
    simpa [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 6 by omega)] using
      fDividedPower_mul i 3 3
  simp only [fUnipotent, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  simp only [smul_zero, add_zero, zero_add, zero_smul]
  module

lemma eUnipotent_mul_neg (i : b.support) (t : ℤ) :
    eUnipotent i t * eUnipotent i (-t) = 1 := by
  rw [eUnipotent_add]
  simp

lemma eUnipotent_neg_mul (i : b.support) (t : ℤ) :
    eUnipotent i (-t) * eUnipotent i t = 1 := by
  rw [eUnipotent_add]
  simp

lemma fUnipotent_mul_neg (i : b.support) (t : ℤ) :
    fUnipotent i t * fUnipotent i (-t) = 1 := by
  rw [fUnipotent_add]
  simp

lemma fUnipotent_neg_mul (i : b.support) (t : ℤ) :
    fUnipotent i (-t) * fUnipotent i t = 1 := by
  rw [fUnipotent_add]
  simp

lemma eUnipotent_mulVec_u (i j : b.support) (t : ℤ) :
    eUnipotent i t *ᵥ u j =
      u j + t • (|b.cartanMatrix i j| • v (b := b) i) := by
  simp only [eUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    eDividedPower_one, eMatrix_mulVec_u, eDividedPower_add_two_mulVec_u,
    smul_zero, add_zero]

private lemma eDividedPower_two_mulVec_v_neg (i : b.support) :
    letI := P.indexNeg
    eDividedPower i 2 *ᵥ v (b := b) (-i) = v (b := b) i := by
  let := P.indexNeg
  have htop : P.chainTopCoeff i i = 0 :=
    P.chainTopCoeff_of_not_linearIndependent (by
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, -1, by simp, by simp⟩)
  simpa [htop] using eDividedPower_add_two_mulVec_v (i := i) (j := (-i : ι))
    (n := 0) (k := (i : ι)) (by simp; module)

private lemma eDividedPower_three_mulVec_v_neg (i : b.support) :
    letI := P.indexNeg
    eDividedPower i 3 *ᵥ v (b := b) (-i) = 0 := by
  let := P.indexNeg
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  apply eDividedPower_add_two_mulVec_v_zero i (-i) 1
  intro hmem
  haveI : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
  apply P.nsmul_notMem_range_root (n := 2) (i := i)
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [hk, show P.root (-i) = -P.root i by simp]
  module

lemma eUnipotent_mulVec_v_neg (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    eUnipotent i t *ᵥ v (b := b) (-i) =
      v (b := b) (-i) + t • u i + t ^ 2 • v (b := b) i := by
  let := P.indexNeg
  simp only [eUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    eDividedPower_one,
    eMatrix_mulVec_v_neg, eDividedPower_two_mulVec_v_neg,
    eDividedPower_three_mulVec_v_neg, smul_zero, add_zero]

lemma fUnipotent_eq_omega (i : b.support) (t : ℤ) :
    fUnipotent i t = omegaMatrix * eUnipotent i t * omegaMatrix := by
  simp only [fUnipotent, eUnipotent, fDividedPower, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp [mul_assoc]

lemma fUnipotent_mulVec_u (i j : b.support) (t : ℤ) :
    fUnipotent i t *ᵥ u j =
      u j + t • (|b.cartanMatrix i j| • v (b := b) (P.reflectionPerm i i)) := by
  let := P.indexNeg
  rw [fUnipotent_eq_omega, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_u, eUnipotent_mulVec_u, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, omegaMatrix_mulVec_u,
    omegaMatrix_mulVec_v]
  rfl

lemma fUnipotent_mulVec_v_same (i : b.support) (t : ℤ) :
    fUnipotent i t *ᵥ v (b := b) i =
      v (b := b) i + t • u i + t ^ 2 • v (b := b) (P.reflectionPerm i i) := by
  let := P.indexNeg
  rw [fUnipotent_eq_omega, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_v, eUnipotent_mulVec_v_neg, Matrix.mulVec_add,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    omegaMatrix_mulVec_v, omegaMatrix_mulVec_u]
  have hneg : (-(-(i : ι)) : ι) = (i : ι) := neg_involutive (i : ι)
  rw [hneg, omegaMatrix_mulVec_v]
  rfl

private lemma eMatrix_mulVec_v_same (i : b.support) :
    eMatrix i *ᵥ v (b := b) i = 0 := by
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  apply eMatrix_mulVec_v_zero (i := i) (j := (i : ι))
  · exact ne_neg P i
  · intro hmem
    haveI : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
    apply P.nsmul_notMem_range_root (n := 2) (i := i)
    simpa [two_smul] using hmem

private lemma eDividedPower_two_mulVec_v_same (i : b.support) :
    eDividedPower i 2 *ᵥ v (b := b) i = 0 := by
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  apply eDividedPower_add_two_mulVec_v_zero i i 0
  intro hmem
  haveI : (3 : ℕ).AtLeastTwo := ⟨by omega⟩
  apply P.nsmul_notMem_range_root (n := 3) (i := i)
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by rw [hk]; module⟩

private lemma eDividedPower_three_mulVec_v_same (i : b.support) :
    eDividedPower i 3 *ᵥ v (b := b) i = 0 := by
  letI : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  letI : IsAddTorsionFree M := .of_isTorsionFree R M
  apply eDividedPower_add_two_mulVec_v_zero i i 1
  intro hmem
  haveI : (4 : ℕ).AtLeastTwo := ⟨by omega⟩
  apply P.nsmul_notMem_range_root (n := 4) (i := i)
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by rw [hk]; module⟩

lemma eUnipotent_mulVec_v_same (i : b.support) (t : ℤ) :
    eUnipotent i t *ᵥ v (b := b) i = v (b := b) i := by
  simp only [eUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    eDividedPower_one, eMatrix_mulVec_v_same, eDividedPower_two_mulVec_v_same,
    eDividedPower_three_mulVec_v_same, smul_zero, add_zero]

/-- The simple Tits lift, formed from the two integral root exponentials. -/
def titsLift (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  eUnipotent i 1 * fUnipotent i (-1) * eUnipotent i 1

/-- The explicit inverse word for a simple Tits lift. -/
def titsLiftInv (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  eUnipotent i (-1) * fUnipotent i 1 * eUnipotent i (-1)

lemma titsLift_mul_inv (i : b.support) : titsLift i * titsLiftInv i = 1 := by
  rw [titsLift, titsLiftInv]
  rw [show (eUnipotent i 1 * fUnipotent i (-1) * eUnipotent i 1) *
      (eUnipotent i (-1) * fUnipotent i 1 * eUnipotent i (-1)) =
    eUnipotent i 1 * fUnipotent i (-1) *
      (eUnipotent i 1 * eUnipotent i (-1)) * fUnipotent i 1 *
        eUnipotent i (-1) by noncomm_ring]
  rw [eUnipotent_mul_neg, mul_one]
  rw [show eUnipotent i 1 * fUnipotent i (-1) * fUnipotent i 1 *
      eUnipotent i (-1) = eUnipotent i 1 *
        (fUnipotent i (-1) * fUnipotent i 1) * eUnipotent i (-1) by
          noncomm_ring]
  rw [fUnipotent_neg_mul, mul_one, eUnipotent_mul_neg]

lemma titsLift_inv_mul (i : b.support) : titsLiftInv i * titsLift i = 1 := by
  rw [titsLift, titsLiftInv]
  rw [show (eUnipotent i (-1) * fUnipotent i 1 * eUnipotent i (-1)) *
      (eUnipotent i 1 * fUnipotent i (-1) * eUnipotent i 1) =
    eUnipotent i (-1) * fUnipotent i 1 *
      (eUnipotent i (-1) * eUnipotent i 1) * fUnipotent i (-1) *
        eUnipotent i 1 by noncomm_ring]
  rw [eUnipotent_neg_mul, mul_one]
  rw [show eUnipotent i (-1) * fUnipotent i 1 * fUnipotent i (-1) *
      eUnipotent i 1 = eUnipotent i (-1) *
        (fUnipotent i 1 * fUnipotent i (-1)) * eUnipotent i 1 by
          noncomm_ring]
  rw [fUnipotent_mul_neg, mul_one, eUnipotent_neg_mul]

lemma titsLift_mulVec_u (i j : b.support) :
    titsLift i *ᵥ u j = u j - |b.cartanMatrix i j| • u i := by
  rw [titsLift, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    eUnipotent_mulVec_u]
  simp only [one_smul]
  have hmiddle : fUnipotent i (-1) *ᵥ
      (u j + |b.cartanMatrix i j| • v (b := b) i) =
      u j + |b.cartanMatrix i j| • v (b := b) i -
        |b.cartanMatrix i j| • u i := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, fUnipotent_mulVec_u,
      fUnipotent_mulVec_v_same]
    simp only [neg_smul, one_smul, neg_one_sq]
    module
  rw [hmiddle, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, eUnipotent_mulVec_u, eUnipotent_mulVec_u,
    eUnipotent_mulVec_v_same]
  simp only [one_smul]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

private lemma root_chainBotIdx_add_nsmul_mem {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (P.chainBotIdx i j) + n • P.root i ∈ Set.range P.root := by
  rw [P.root_chainBotIdx]
  have heq : P.root j - P.chainBotCoeff i j • P.root i + n • P.root i =
      P.root j + ((n : ℤ) - P.chainBotCoeff i j) • P.root i := by
    simp only [sub_smul]
    module
  rw [heq, P.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc]
  constructor <;> omega

private noncomputable def rootStringIdx (i : b.support) (j : ι)
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) : ι :=
  (root_chainBotIdx_add_nsmul_mem hlin hn).choose

private lemma root_rootStringIdx {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (rootStringIdx i j hlin n hn) =
      P.root (P.chainBotIdx i j) + n • P.root i :=
  (root_chainBotIdx_add_nsmul_mem hlin hn).choose_spec

private lemma root_rootStringIdx_eq {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (rootStringIdx i j hlin n hn) =
      P.root j + ((n : ℤ) - P.chainBotCoeff i j) • P.root i := by
  rw [root_rootStringIdx hlin hn, P.root_chainBotIdx]
  simp only [sub_smul]
  module

private lemma linearIndependent_rootStringIdx {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    LinearIndependent R ![P.root i, P.root (rootStringIdx i j hlin n hn)] := by
  rw [root_rootStringIdx_eq hlin hn, add_comm,
    LinearIndependent.pair_add_smul_right_iff]
  exact hlin

private lemma chainBotCoeff_rootStringIdx {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.chainBotCoeff i (rootStringIdx i j hlin n hn) = n := by
  have hlink : LinearIndependent R
      ![P.root i, P.root (rootStringIdx i j hlin n hn)] :=
    linearIndependent_rootStringIdx hlin hn
  apply le_antisymm
  · have hmem := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlink).2
      (le_refl (P.chainBotCoeff i (rootStringIdx i j hlin n hn)))
    rw [root_rootStringIdx_eq hlin hn] at hmem
    have heq : P.root j + ((n : ℤ) - P.chainBotCoeff i j) • P.root i -
        P.chainBotCoeff i (rootStringIdx i j hlin n hn) • P.root i =
        P.root j + ((n : ℤ) - P.chainBotCoeff i j -
          P.chainBotCoeff i (rootStringIdx i j hlin n hn)) • P.root i := by
      simp only [sub_smul]
      module
    rw [heq, P.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc] at hmem
    omega
  · apply (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlink).1
    refine ⟨P.chainBotIdx i j, ?_⟩
    rw [root_rootStringIdx hlin hn]
    module

private lemma chainTopCoeff_rootStringIdx {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.chainTopCoeff i (rootStringIdx i j hlin n hn) =
      P.chainBotCoeff i j + P.chainTopCoeff i j - n := by
  have hlink : LinearIndependent R
      ![P.root i, P.root (rootStringIdx i j hlin n hn)] :=
    linearIndependent_rootStringIdx hlin hn
  apply le_antisymm
  · have hmem := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlink).2
      (le_refl (P.chainTopCoeff i (rootStringIdx i j hlin n hn)))
    rw [root_rootStringIdx_eq hlin hn] at hmem
    have heq : P.root j + ((n : ℤ) - P.chainBotCoeff i j) • P.root i +
        P.chainTopCoeff i (rootStringIdx i j hlin n hn) • P.root i =
        P.root j + ((n : ℤ) - P.chainBotCoeff i j +
          P.chainTopCoeff i (rootStringIdx i j hlin n hn)) • P.root i := by
      simp only [add_smul]
      module
    rw [heq, P.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc] at hmem
    omega
  · apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlink).1
    refine ⟨P.chainTopIdx i j, ?_⟩
    rw [root_rootStringIdx_eq hlin hn, P.root_chainTopIdx]
    rw [← natCast_zsmul, ← natCast_zsmul]
    have hcast : ((P.chainBotCoeff i j + P.chainTopCoeff i j - n : ℕ) : ℤ) =
        P.chainBotCoeff i j + P.chainTopCoeff i j - n := by
      omega
    rw [hcast]
    module

private noncomputable def rootStringVector (i : b.support) (j : ι)
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ) : Carrier (b := b) :=
  if hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j then
    v (b := b) (rootStringIdx i j hlin n hn)
  else 0

private lemma rootStringVector_of_le {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    rootStringVector i j hlin n = v (b := b) (rootStringIdx i j hlin n hn) := by
  simp only [rootStringVector, dif_pos hn]

@[simp] private lemma rootStringVector_of_lt {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n : ℕ}
    (hn : P.chainBotCoeff i j + P.chainTopCoeff i j < n) :
    rootStringVector i j hlin n = 0 := by
  simp [rootStringVector, Nat.not_le.mpr hn]

private lemma rootStringVector_botCoeff {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) :
    rootStringVector i j hlin (P.chainBotCoeff i j) = v (b := b) j := by
  have hn : P.chainBotCoeff i j ≤
      P.chainBotCoeff i j + P.chainTopCoeff i j := Nat.le_add_right _ _
  rw [rootStringVector_of_le hlin hn]
  congr 1
  apply P.root.injective
  rw [root_rootStringIdx_eq hlin hn]
  simp

private lemma rootStringVector_chainTopCoeff {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) :
    rootStringVector i j hlin (P.chainTopCoeff i j) =
      v (b := b) (P.reflectionPerm i j) := by
  have hn : P.chainTopCoeff i j ≤
      P.chainBotCoeff i j + P.chainTopCoeff i j := Nat.le_add_left _ _
  rw [rootStringVector_of_le hlin hn]
  congr 1
  apply P.root.injective
  rw [root_rootStringIdx_eq hlin hn, root_reflectionPerm, reflection_apply_root,
    ← P.algebraMap_pairingIn ℤ, ← P.chainBotCoeff_sub_chainTopCoeff hlin]
  simp only [sub_smul]
  module

private lemma rootStringIdx_add_nsmul_mem_iff {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n a : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (rootStringIdx i j hlin n hn) + a • P.root i ∈ Set.range P.root ↔
      n + a ≤ P.chainBotCoeff i j + P.chainTopCoeff i j := by
  rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
    (linearIndependent_rootStringIdx hlin hn),
    chainTopCoeff_rootStringIdx hlin hn]
  omega

private lemma rootStringIdx_sub_nsmul_mem_iff {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n a : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (rootStringIdx i j hlin n hn) - a • P.root i ∈ Set.range P.root ↔ a ≤ n := by
  rw [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff
    (linearIndependent_rootStringIdx hlin hn),
    chainBotCoeff_rootStringIdx hlin hn]

private lemma root_rootStringIdx_add {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n a : ℕ}
    (hna : n + a ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    P.root (rootStringIdx i j hlin (n + a) hna) =
      P.root (rootStringIdx i j hlin n (Nat.le_trans (Nat.le_add_right n a) hna)) +
        a • P.root i := by
  rw [root_rootStringIdx_eq hlin hna,
    root_rootStringIdx_eq hlin (Nat.le_trans (Nat.le_add_right n a) hna)]
  simp only [Nat.cast_add, add_smul]
  module

private lemma eDividedPower_mulVec_rootStringVector {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n a : ℕ) :
    eDividedPower i a *ᵥ rootStringVector i j hlin n =
      ((n + a).choose a : ℤ) • rootStringVector i j hlin (n + a) := by
  by_cases hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j
  swap
  · have hn' : P.chainBotCoeff i j + P.chainTopCoeff i j < n := Nat.lt_of_not_ge hn
    rw [rootStringVector_of_lt hlin hn', rootStringVector_of_lt hlin (lt_of_lt_of_le hn'
      (Nat.le_add_right n a))]
    simp
  rw [rootStringVector_of_le hlin hn]
  by_cases hna : n + a ≤ P.chainBotCoeff i j + P.chainTopCoeff i j
  · rw [rootStringVector_of_le hlin hna]
    have hroot := root_rootStringIdx_add hlin hna
    have hnproof : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j :=
      Nat.le_trans (Nat.le_add_right n a) hna
    have hcur : rootStringIdx i j hlin n hn = rootStringIdx i j hlin n hnproof := by
      congr
    rw [hcur]
    rcases a with (_ | _ | a)
    · have hidx : rootStringIdx i j hlin (n + 0) hna =
          rootStringIdx i j hlin n hnproof := P.root.injective (by simpa using hroot)
      rw [hidx]
      ext x
      classical
      simp [Matrix.one_apply, v, Pi.single_apply]
    · rw [eDividedPower_one, eMatrix_mulVec_v_add (by simpa [add_comm] using hroot),
        chainBotCoeff_rootStringIdx hlin hnproof]
      simp
    · rw [eDividedPower_add_two_mulVec_v a (by simpa [Nat.add_assoc] using hroot),
        chainBotCoeff_rootStringIdx hlin hnproof]
      congr 3 <;> omega
  · have hlt : P.chainBotCoeff i j + P.chainTopCoeff i j < n + a :=
      Nat.lt_of_not_ge hna
    rw [rootStringVector_of_lt hlin hlt, smul_zero]
    have hnot := (rootStringIdx_add_nsmul_mem_iff hlin hn).not.mpr hna
    rcases a with (_ | _ | a)
    · omega
    · rw [eDividedPower_one]
      apply eMatrix_mulVec_v_zero
      · intro heq
        have hli := linearIndependent_rootStringIdx hlin hn
        rw [heq] at hli
        have hli' : LinearIndependent R ![P.root i, P.root i] := by simpa using hli
        rw [LinearIndependent.pair_iff] at hli'
        have hone := hli' 1 (-1) (by simp)
        exact one_ne_zero hone.1
      · simpa [add_comm] using hnot
    · apply eDividedPower_add_two_mulVec_v_zero
      simpa [Nat.add_assoc] using hnot

private lemma root_rootStringIdx_sub {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) {n a : ℕ}
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) (ha : a ≤ n) :
    P.root (rootStringIdx i j hlin (n - a) (by omega)) =
      P.root (rootStringIdx i j hlin n hn) - a • P.root i := by
  rw [root_rootStringIdx_eq hlin (show n - a ≤
      P.chainBotCoeff i j + P.chainTopCoeff i j by omega),
    root_rootStringIdx_eq hlin hn]
  have hcast : ((n - a : ℕ) : ℤ) = n - a := by omega
  rw [hcast]
  simp only [sub_smul]
  module

private lemma fDividedPower_mulVec_rootStringVector {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n a : ℕ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    fDividedPower i a *ᵥ rootStringVector i j hlin n =
      if ha : a ≤ n then
        ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + a).choose a : ℤ) •
          rootStringVector i j hlin (n - a)
      else 0 := by
  rw [rootStringVector_of_le hlin hn]
  by_cases ha : a ≤ n
  · rw [dif_pos ha]
    have hna : n - a ≤ P.chainBotCoeff i j + P.chainTopCoeff i j := by omega
    rw [rootStringVector_of_le hlin hna]
    have hroot := root_rootStringIdx_sub hlin hn ha
    rcases a with (_ | _ | a)
    · have hidx : rootStringIdx i j hlin (n - 0) hna =
          rootStringIdx i j hlin n hn := P.root.injective (by simpa using hroot)
      rw [hidx]
      ext x
      classical
      simp [Matrix.one_apply, v, Pi.single_apply]
    · rw [fDividedPower_one, fMatrix_mulVec_v_sub (by simpa using hroot),
        chainTopCoeff_rootStringIdx hlin hn]
      simp
    · rw [fDividedPower_add_two_mulVec_v a (by simpa [Nat.add_assoc] using hroot),
        chainTopCoeff_rootStringIdx hlin hn]
      congr 3 <;> omega
  · rw [dif_neg ha]
    have hnot := (rootStringIdx_sub_nsmul_mem_iff hlin hn).not.mpr ha
    rcases a with (_ | _ | a)
    · omega
    · rw [fDividedPower_one]
      apply fMatrix_mulVec_v_zero
      · intro heq
        have hli := linearIndependent_rootStringIdx hlin hn
        rw [heq] at hli
        have hli' : LinearIndependent R ![P.root i, P.root i] := by simpa using hli
        rw [LinearIndependent.pair_iff] at hli'
        have hone := hli' 1 (-1) (by simp)
        exact one_ne_zero hone.1
      · simpa using hnot
    · apply fDividedPower_add_two_mulVec_v_zero
      simpa [Nat.add_assoc] using hnot

private lemma eUnipotent_mulVec_rootStringVector {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ) (t : ℤ) :
    eUnipotent i t *ᵥ rootStringVector i j hlin n =
      rootStringVector i j hlin n +
        t • (((n + 1).choose 1 : ℤ) • rootStringVector i j hlin (n + 1)) +
        t ^ 2 • (((n + 2).choose 2 : ℤ) • rootStringVector i j hlin (n + 2)) +
        t ^ 3 • (((n + 3).choose 3 : ℤ) • rootStringVector i j hlin (n + 3)) := by
  simp only [eUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    eDividedPower_mulVec_rootStringVector]

private lemma fUnipotent_mulVec_rootStringVector {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ) (t : ℤ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    fUnipotent i t *ᵥ rootStringVector i j hlin n =
      rootStringVector i j hlin n +
        t • (if h1 : 1 ≤ n then
          ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 1).choose 1 : ℤ) •
            rootStringVector i j hlin (n - 1) else 0) +
        t ^ 2 • (if h2 : 2 ≤ n then
          ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 2).choose 2 : ℤ) •
            rootStringVector i j hlin (n - 2) else 0) +
        t ^ 3 • (if h3 : 3 ≤ n then
          ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 3).choose 3 : ℤ) •
            rootStringVector i j hlin (n - 3) else 0) := by
  simp only [fUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    fDividedPower_mulVec_rootStringVector hlin n 1 hn,
    fDividedPower_mulVec_rootStringVector hlin n 2 hn,
    fDividedPower_mulVec_rootStringVector hlin n 3 hn]

private lemma fUnipotent_mulVec_rootStringVector' {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ) (t : ℤ) :
    fUnipotent i t *ᵥ rootStringVector i j hlin n =
      if hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j then
        rootStringVector i j hlin n +
          t • (if h1 : 1 ≤ n then
            ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 1).choose 1 : ℤ) •
              rootStringVector i j hlin (n - 1) else 0) +
          t ^ 2 • (if h2 : 2 ≤ n then
            ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 2).choose 2 : ℤ) •
              rootStringVector i j hlin (n - 2) else 0) +
          t ^ 3 • (if h3 : 3 ≤ n then
            ((P.chainBotCoeff i j + P.chainTopCoeff i j - n + 3).choose 3 : ℤ) •
              rootStringVector i j hlin (n - 3) else 0)
      else 0 := by
  by_cases hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j
  · rw [dif_pos hn, fUnipotent_mulVec_rootStringVector hlin n t hn]
  · rw [dif_neg hn, rootStringVector_of_lt hlin (Nat.lt_of_not_ge hn)]
    simp

private lemma titsLift_mulVec_rootStringVector {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) :
    titsLift i *ᵥ rootStringVector i j hlin n =
      (-1 : ℤ) ^ n • rootStringVector i j hlin
        (P.chainBotCoeff i j + P.chainTopCoeff i j - n) := by
  have hbound := P.chainBotCoeff_add_chainTopCoeff_le_three (i := (i : ι)) (j := j)
  generalize hd : P.chainBotCoeff i j + P.chainTopCoeff i j = d at hbound hn ⊢
  have hzero (m : ℕ) (hm : d < m) : rootStringVector i j hlin m = 0 :=
    rootStringVector_of_lt hlin (by omega)
  have he_mul (z : ℤ) (x : Carrier (b := b)) :
      eUnipotent i 1 *ᵥ (z * x) = z * (eUnipotent i 1 *ᵥ x) := by
    rw [show z * x = z • x by ext; simp, Matrix.mulVec_smul (R := ℤ)]
    ext
    simp
  have hf_mul (z : ℤ) (x : Carrier (b := b)) :
      fUnipotent i (-1) *ᵥ (z * x) = z * (fUnipotent i (-1) *ᵥ x) := by
    rw [show z * x = z • x by ext; simp, Matrix.mulVec_smul (R := ℤ)]
    ext
    simp
  have he_two (x : Carrier (b := b)) :
      eUnipotent i 1 *ᵥ (2 * x) = 2 * (eUnipotent i 1 *ᵥ x) := he_mul 2 x
  have he_three (x : Carrier (b := b)) :
      eUnipotent i 1 *ᵥ (3 * x) = 3 * (eUnipotent i 1 *ᵥ x) := he_mul 3 x
  have hf_two (x : Carrier (b := b)) :
      fUnipotent i (-1) *ᵥ (2 * x) = 2 * (fUnipotent i (-1) *ᵥ x) := hf_mul 2 x
  have hf_three (x : Carrier (b := b)) :
      fUnipotent i (-1) *ᵥ (3 * x) = 3 * (fUnipotent i (-1) *ᵥ x) := hf_mul 3 x
  interval_cases d <;> interval_cases n <;> try omega
  all_goals
    simp_all [titsLift, ← Matrix.mulVec_mulVec,
      eUnipotent_mulVec_rootStringVector, fUnipotent_mulVec_rootStringVector',
      Matrix.mulVec_add, Matrix.mulVec_neg, he_two, he_three, hf_two, hf_three,
      hzero, Nat.choose]
  all_goals ring

private lemma fUnipotent_mulVec_v_neg (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    fUnipotent i t *ᵥ v (b := b) (-i) = v (b := b) (-i) := by
  let := P.indexNeg
  rw [fUnipotent_eq_omega, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaMatrix_mulVec_v]
  simp only [neg_neg]
  rw [eUnipotent_mulVec_v_same, omegaMatrix_mulVec_v]

lemma titsLift_mulVec_v_same (i : b.support) :
    letI := P.indexNeg
    titsLift i *ᵥ v (b := b) i = v (b := b) (P.reflectionPerm i i) := by
  let := P.indexNeg
  rw [titsLift, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    eUnipotent_mulVec_v_same, fUnipotent_mulVec_v_same]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl]
  rw [
    Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul,
    eUnipotent_mulVec_v_same, eUnipotent_mulVec_u, eUnipotent_mulVec_v_neg]
  simp only [one_smul, neg_one_sq, neg_smul]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

lemma titsLift_mulVec_v_neg (i : b.support) :
    letI := P.indexNeg
    titsLift i *ᵥ v (b := b) (-i) = v (b := b) i := by
  let := P.indexNeg
  rw [titsLift, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    eUnipotent_mulVec_v_neg]
  have hmiddle : fUnipotent i (-1) *ᵥ
      (v (b := b) (-i) + 1 • u i + 1 ^ 2 • v (b := b) i) = v (b := b) i := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, fUnipotent_mulVec_v_neg, fUnipotent_mulVec_u,
      fUnipotent_mulVec_v_same]
    simp only [one_smul, one_pow, neg_smul, neg_one_sq]
    have hcartan : |b.cartanMatrix i i| = 2 := by simp
    rw [hcartan]
    module
  calc
    eUnipotent i 1 *ᵥ fUnipotent i (-1) *ᵥ
        (v (b := b) (-i) + 1 • u i + 1 ^ 2 • v (b := b) i) =
        eUnipotent i 1 *ᵥ v (b := b) i := congrArg (fun x ↦ eUnipotent i 1 *ᵥ x) hmiddle
    _ = v (b := b) i := eUnipotent_mulVec_v_same i 1

private lemma not_linearIndependent_root_self (i : b.support) :
    ¬ LinearIndependent R ![P.root i, P.root i] := by
  rw [LinearIndependent.pair_iff]
  intro h
  have hone := h 1 (-1) (by simp)
  exact one_ne_zero hone.1

private lemma not_linearIndependent_root_neg (i : b.support) :
    letI := P.indexNeg
    ¬ LinearIndependent R ![P.root i, P.root (-i)] := by
  let := P.indexNeg
  rw [LinearIndependent.pair_iff]
  intro h
  have hone := h 1 1 (by simp)
  exact one_ne_zero hone.1

/-- A simple Tits lift sends every root basis vector to the reflected root line, with the
root-string sign determined by the distance from the bottom of the string. -/
lemma titsLift_mulVec_v (i : b.support) (j : ι) :
    letI := P.indexNeg
    titsLift i *ᵥ v (b := b) j =
      (-1 : ℤ) ^ P.chainBotCoeff i j • v (b := b) (P.reflectionPerm i j) := by
  let := P.indexNeg
  by_cases hsame : j = (i : ι)
  · subst j
    rw [titsLift_mulVec_v_same]
    rw [P.chainBotCoeff_of_not_linearIndependent
      (not_linearIndependent_root_self (P := P) i)]
    simp
  by_cases hneg : j = (-i : ι)
  · subst j
    rw [titsLift_mulVec_v_neg]
    rw [P.chainBotCoeff_of_not_linearIndependent
      (not_linearIndependent_root_neg (P := P) i)]
    simp
  have hlin : LinearIndependent R ![P.root i, P.root j] :=
    IsReduced.linearIndependent P (Ne.symm hsame) (by
      intro hroot
      apply hneg
      apply P.root.injective
      rw [show P.root (-i) = -P.root i by simp]
      have hroot' := congrArg Neg.neg hroot
      simpa using hroot'.symm)
  rw [← rootStringVector_botCoeff hlin,
    titsLift_mulVec_rootStringVector hlin (P.chainBotCoeff i j)
      (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, rootStringVector_chainTopCoeff]

/-- The product of simple Tits lifts attached to a word, in its action order. -/
def titsWord : List b.support → Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ
  | [] => 1
  | i :: word => titsLift i * titsWord word

/-- The Weyl permutation represented by a word of simple reflections. -/
def reflectionWord : List b.support → ι → ι
  | [], j => j
  | i :: word, j => P.reflectionPerm i (reflectionWord word j)

/-- The integral sign accumulated by a Tits word on a root basis vector. -/
def titsWordSign : List b.support → ι → ℤ
  | [], _ => 1
  | i :: word, j =>
      titsWordSign word j *
        (-1 : ℤ) ^ P.chainBotCoeff i (reflectionWord word j)

/-- Products of Tits lifts transport root basis lines according to the corresponding Weyl word. -/
lemma titsWord_mulVec_v (word : List b.support) (j : ι) :
    letI := P.indexNeg
    titsWord word *ᵥ v (b := b) j =
      titsWordSign word j • v (b := b) (reflectionWord word j) := by
  let := P.indexNeg
  induction word with
  | nil =>
      ext x
      simp [titsWord, titsWordSign, reflectionWord, v, Pi.single_apply,
        Matrix.one_apply]
  | cons i word ih =>
      rw [titsWord, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        titsLift_mulVec_v]
      simp only [titsWordSign, reflectionWord, smul_smul]

private lemma titsLift_eUnipotent_rootString {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) (t : ℤ) :
    titsLift i *ᵥ (eUnipotent i t *ᵥ rootStringVector i j hlin n) =
      fUnipotent i (-t) *ᵥ (titsLift i *ᵥ rootStringVector i j hlin n) := by
  rw [titsLift_mulVec_rootStringVector hlin n hn, Matrix.mulVec_smul,
    eUnipotent_mulVec_rootStringVector]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hbound := P.chainBotCoeff_add_chainTopCoeff_le_three (i := (i : ι)) (j := j)
  generalize hd : P.chainBotCoeff i j + P.chainTopCoeff i j = d at hbound hn ⊢
  have hzero (m : ℕ) (hm : d < m) : rootStringVector i j hlin m = 0 :=
    rootStringVector_of_lt hlin (by omega)
  interval_cases d <;> interval_cases n <;> try omega
  all_goals
    simp_all [eUnipotent_mulVec_rootStringVector,
      fUnipotent_mulVec_rootStringVector', titsLift_mulVec_rootStringVector,
      Matrix.mulVec_add, Matrix.mulVec_neg, hzero, Nat.choose]
  all_goals ring

private lemma titsLift_fUnipotent_rootString {i : b.support} {j : ι}
    (hlin : LinearIndependent R ![P.root i, P.root j]) (n : ℕ)
    (hn : n ≤ P.chainBotCoeff i j + P.chainTopCoeff i j) (t : ℤ) :
    titsLift i *ᵥ (fUnipotent i t *ᵥ rootStringVector i j hlin n) =
      eUnipotent i (-t) *ᵥ (titsLift i *ᵥ rootStringVector i j hlin n) := by
  rw [titsLift_mulVec_rootStringVector hlin n hn, Matrix.mulVec_smul,
    fUnipotent_mulVec_rootStringVector hlin n t hn]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hbound := P.chainBotCoeff_add_chainTopCoeff_le_three (i := (i : ι)) (j := j)
  generalize hd : P.chainBotCoeff i j + P.chainTopCoeff i j = d at hbound hn ⊢
  have hzero (m : ℕ) (hm : d < m) : rootStringVector i j hlin m = 0 :=
    rootStringVector_of_lt hlin (by omega)
  have hT_root_mul_nat (m z : ℕ) (hm : m ≤ d) :
      titsLift i *ᵥ
          (((z : ℕ) : Carrier (b := b)) * rootStringVector i j hlin m) =
        (z : ℤ) • ((-1 : ℤ) ^ m • rootStringVector i j hlin (d - m)) := by
    have hcast :
        ((z : ℕ) : Carrier (b := b)) * rootStringVector i j hlin m =
          (z : ℤ) • rootStringVector i j hlin m := by
      ext
      simp
    rw [hcast, Matrix.mulVec_smul,
      titsLift_mulVec_rootStringVector hlin m (by omega)]
    rw [hd]
  have hT_root_two (m : ℕ) (hm : m ≤ d) :
      titsLift i *ᵥ (2 * rootStringVector i j hlin m) =
        (2 : ℤ) • ((-1 : ℤ) ^ m • rootStringVector i j hlin (d - m)) := by
    simpa using hT_root_mul_nat m 2 hm
  have hT_root_three (m : ℕ) (hm : m ≤ d) :
      titsLift i *ᵥ (3 * rootStringVector i j hlin m) =
        (3 : ℤ) • ((-1 : ℤ) ^ m • rootStringVector i j hlin (d - m)) := by
    simpa using hT_root_mul_nat m 3 hm
  interval_cases d <;> interval_cases n <;> try omega
  all_goals
    simp_all [eUnipotent_mulVec_rootStringVector,
      fUnipotent_mulVec_rootStringVector', titsLift_mulVec_rootStringVector,
      Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hT_root_two,
      hT_root_three, hzero, Nat.choose]
  case «3».«3» => ring

private lemma titsLift_eUnipotent_u (i j : b.support) (t : ℤ) :
    titsLift i *ᵥ (eUnipotent i t *ᵥ u j) =
      fUnipotent i (-t) *ᵥ (titsLift i *ᵥ u j) := by
  let := P.indexNeg
  rw [eUnipotent_mulVec_u, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul,
    titsLift_mulVec_u, titsLift_mulVec_v_same,
    Matrix.mulVec_sub, Matrix.mulVec_smul,
    fUnipotent_mulVec_u (i := i) (j := j),
    fUnipotent_mulVec_u (i := i) (j := i)]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

private lemma titsLift_eUnipotent_v_same (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    titsLift i *ᵥ (eUnipotent i t *ᵥ v (b := b) i) =
      fUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) i) := by
  let := P.indexNeg
  rw [eUnipotent_mulVec_v_same, titsLift_mulVec_v_same]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl,
    fUnipotent_mulVec_v_neg]

private lemma titsLift_eUnipotent_v_neg (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    titsLift i *ᵥ (eUnipotent i t *ᵥ v (b := b) (-i)) =
      fUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) (-i)) := by
  let := P.indexNeg
  rw [eUnipotent_mulVec_v_neg, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, titsLift_mulVec_v_neg,
    titsLift_mulVec_u, titsLift_mulVec_v_same]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl,
    fUnipotent_mulVec_v_same]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

private lemma titsLift_fUnipotent_v_same (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    titsLift i *ᵥ (fUnipotent i t *ᵥ v (b := b) i) =
      eUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) i) := by
  let := P.indexNeg
  rw [fUnipotent_mulVec_v_same]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl]
  rw [Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, titsLift_mulVec_v_same,
    titsLift_mulVec_u, titsLift_mulVec_v_neg]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl,
    eUnipotent_mulVec_v_neg]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

private lemma titsLift_fUnipotent_v_neg (i : b.support) (t : ℤ) :
    letI := P.indexNeg
    titsLift i *ᵥ (fUnipotent i t *ᵥ v (b := b) (-i)) =
      eUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) (-i)) := by
  let := P.indexNeg
  rw [fUnipotent_mulVec_v_neg, titsLift_mulVec_v_neg,
    eUnipotent_mulVec_v_same]

private lemma titsLift_fUnipotent_u (i j : b.support) (t : ℤ) :
    titsLift i *ᵥ (fUnipotent i t *ᵥ u j) =
      eUnipotent i (-t) *ᵥ (titsLift i *ᵥ u j) := by
  let := P.indexNeg
  rw [fUnipotent_mulVec_u, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, titsLift_mulVec_u]
  rw [show P.reflectionPerm i i = (-i : ι) by rfl,
    titsLift_mulVec_v_neg, Matrix.mulVec_sub,
    Matrix.mulVec_smul, eUnipotent_mulVec_u (i := i) (j := j),
    eUnipotent_mulVec_u (i := i) (j := i)]
  have hcartan : |b.cartanMatrix i i| = 2 := by simp
  rw [hcartan]
  module

/-- A simple Tits lift exchanges the positive and negative integral root exponentials. -/
lemma titsLift_mul_eUnipotent (i : b.support) (t : ℤ) :
    titsLift i * eUnipotent i t = fUnipotent i (-t) * titsLift i := by
  let := P.indexNeg
  apply Matrix.ext_of_mulVec_single
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases x with j | j
  · exact titsLift_eUnipotent_u i j t
  · by_cases hsame : j = (i : ι)
    · subst j
      exact titsLift_eUnipotent_v_same i t
    by_cases hneg : j = (-i : ι)
    · subst j
      exact titsLift_eUnipotent_v_neg i t
    have hlin : LinearIndependent R ![P.root i, P.root j] :=
      IsReduced.linearIndependent P (Ne.symm hsame) (by
        intro hroot
        apply hneg
        apply P.root.injective
        rw [show P.root (-i) = -P.root i by simp]
        have hroot' := congrArg Neg.neg hroot
        simpa using hroot'.symm)
    change titsLift i *ᵥ (eUnipotent i t *ᵥ v (b := b) j) =
      fUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) j)
    rw [← rootStringVector_botCoeff hlin]
    exact titsLift_eUnipotent_rootString hlin _ (Nat.le_add_right _ _) t

/-- The companion exchange formula for the negative integral root exponential. -/
lemma titsLift_mul_fUnipotent (i : b.support) (t : ℤ) :
    titsLift i * fUnipotent i t = eUnipotent i (-t) * titsLift i := by
  let := P.indexNeg
  apply Matrix.ext_of_mulVec_single
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases x with j | j
  · exact titsLift_fUnipotent_u i j t
  · by_cases hsame : j = (i : ι)
    · subst j
      exact titsLift_fUnipotent_v_same i t
    by_cases hneg : j = (-i : ι)
    · subst j
      exact titsLift_fUnipotent_v_neg i t
    have hlin : LinearIndependent R ![P.root i, P.root j] :=
      IsReduced.linearIndependent P (Ne.symm hsame) (by
        intro hroot
        apply hneg
        apply P.root.injective
        rw [show P.root (-i) = -P.root i by simp]
        have hroot' := congrArg Neg.neg hroot
        simpa using hroot'.symm)
    change titsLift i *ᵥ (fUnipotent i t *ᵥ v (b := b) j) =
      eUnipotent i (-t) *ᵥ (titsLift i *ᵥ v (b := b) j)
    rw [← rootStringVector_botCoeff hlin]
    exact titsLift_fUnipotent_rootString hlin _ (Nat.le_add_right _ _) t

/-- Conjugation by the simple Tits lift sends a positive root exponential to the
corresponding negative root exponential with negated parameter. -/
lemma titsLift_conj_eUnipotent (i : b.support) (t : ℤ) :
    titsLift i * eUnipotent i t * titsLiftInv i = fUnipotent i (-t) := by
  calc
    titsLift i * eUnipotent i t * titsLiftInv i =
        (fUnipotent i (-t) * titsLift i) * titsLiftInv i := by
      rw [titsLift_mul_eUnipotent]
    _ = fUnipotent i (-t) * (titsLift i * titsLiftInv i) := by
      rw [Matrix.mul_assoc]
    _ = fUnipotent i (-t) := by rw [titsLift_mul_inv, Matrix.mul_one]

/-- Conjugation by the simple Tits lift sends a negative root exponential to the
corresponding positive root exponential with negated parameter. -/
lemma titsLift_conj_fUnipotent (i : b.support) (t : ℤ) :
    titsLift i * fUnipotent i t * titsLiftInv i = eUnipotent i (-t) := by
  calc
    titsLift i * fUnipotent i t * titsLiftInv i =
        (eUnipotent i (-t) * titsLift i) * titsLiftInv i := by
      rw [titsLift_mul_fUnipotent]
    _ = eUnipotent i (-t) * (titsLift i * titsLiftInv i) := by
      rw [Matrix.mul_assoc]
    _ = eUnipotent i (-t) := by rw [titsLift_mul_inv, Matrix.mul_one]

/-- Scalar extension intertwines the integral positive simple-root action with Geck's
characteristic-zero action. -/
lemma map_eMatrix_mulVec (i : b.support) (x : Carrier (b := b)) :
    (algebraMap ℤ R) ∘ (eMatrix i *ᵥ x) =
      RootPairing.GeckConstruction.e i *ᵥ ((algebraMap ℤ R) ∘ x) := by
  ext k
  change algebraMap ℤ R ((eMatrix i *ᵥ x) k) =
    (RootPairing.GeckConstruction.e i *ᵥ ((algebraMap ℤ R) ∘ x)) k
  rw [RingHom.map_mulVec, map_eMatrix]

/-- Scalar extension intertwines the integral negative simple-root action with Geck's
characteristic-zero action. -/
lemma map_fMatrix_mulVec (i : b.support) (x : Carrier (b := b)) :
    (algebraMap ℤ R) ∘ (fMatrix i *ᵥ x) =
      RootPairing.GeckConstruction.f i *ᵥ ((algebraMap ℤ R) ∘ x) := by
  ext k
  change algebraMap ℤ R ((fMatrix i *ᵥ x) k) =
    (RootPairing.GeckConstruction.f i *ᵥ ((algebraMap ℤ R) ∘ x)) k
  rw [RingHom.map_mulVec, map_fMatrix]

end

end

end RootPairing.IntegralGeckConstruction
