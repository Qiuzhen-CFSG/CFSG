module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Lifting

/-!
# The scalar character of a fundamental unitary centralizer

In the identity Hermitian form over a field of order q², the centralizer of the
marked SU₂ consists exactly of matrices diag(a I₂, B), with a of norm one,
B unitary, and a² det(B) = 1. A generator of the (q+1)-st roots of unity gives
a diagonal SU₂ element whose eigenvalues are distinct and different from one.
Commutation with this element eliminates the mixed blocks and the off-diagonal
entries of the first block. Commutation with the determinant-one swap then
identifies its two diagonal entries.

Reading this scalar defines a character on the literal covering centralizer.
Its kernel is exactly the range of the existing complementary SU embedding.
This supplies the character input of `residual_eq_complement_of_covering_character`;
defining-prime generation of the complementary group is a separate input.
The calculation holds for every q > 1 and every complementary dimension, in
particular for q = 3 and complementary dimension one.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.17,
printed pp.38–39 of `refs/quasithin.pdf`, the unitary centralizer residual
identified with SU_{N-2}(q).
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

private theorem exists_separating_norm_one [Finite F] {q : ℕ} (hq : 1 < q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, σ x = x ^ q) :
    ∃ u : Fˣ, σ (u : F) * (u : F) = 1 ∧ (u : F) ≠ (u : F)⁻¹ := by
  have hd : q + 1 ∣ Nat.card F - 1 := by
    rw [hc]
    refine ⟨q - 1, ?_⟩
    have h : q = q - 1 + 1 := by omega
    have hh : q ^ 2 = (q + 1) * (q - 1) + 1 := by nlinarith
    omega
  have hcard := FiniteField.card_rootsOfUnity_of_dvd F (q+1) hd
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity (q+1) F)
  refine ⟨u.val, ?_, ?_⟩
  · have hp := congrArg Units.val ((mem_rootsOfUnity _ u.val).mp u.property)
    simpa [hj, pow_succ] using hp
  · intro he
    have hp : u ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      change (u.val : F)^2 = 1
      rw [pow_two]
      calc
        (u.val : F) * (u.val : F) = (u.val : F)⁻¹ * (u.val : F) := congrArg (· * (u.val : F)) he
        _ = 1 := inv_mul_cancel₀ (Units.ne_zero u.val)
    have hh := orderOf_dvd_of_pow_eq_one hp
    rw [hu, hcard] at hh
    have := Nat.le_of_dvd (by decide : 0 < 2) hh
    omega

private def diagSU (u : Fˣ) (hu : σ (u : F) * (u : F) = 1) :
    (form σ hσ 2).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (diagonal ![(u : F), (u : F)⁻¹]) (by
    simp [Units.ne_zero u]), by
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_, Units.ext ?_⟩
    · have hu' : (σ (u : F))⁻¹ * (u : F)⁻¹ = 1 := by
        rw [← mul_inv, hu, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [form, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
          hu, hu']
    · change (diagonal ![(u : F), (u : F)⁻¹]).det = 1
      simp [Units.ne_zero u]⟩

private def swapSU : (form σ hσ 2).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![0,1;-1,0] (by simp [det_fin_two]), by
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_, Units.ext ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [form, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    · change (!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) F).det = 1
      simp [det_fin_two]⟩

private theorem matrix_shape {n : ℕ} (u : Fˣ) (hu : (u : F) ≠ (u : F)⁻¹)
    (M : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) F)
    (hd : fromBlocks (diagonal ![(u : F), (u : F)⁻¹]) 0 0 1 * M =
      M * fromBlocks (diagonal ![(u : F), (u : F)⁻¹]) 0 0 1)
    (hs : fromBlocks !![0,1;-1,0] 0 0 1 * M =
      M * fromBlocks !![0,1;-1,0] 0 0 1) :
    M = fromBlocks (Matrix.scalar (Fin 2) (M (.inl 0) (.inl 0))) 0 0
      (fun i j => M (.inr i) (.inr j)) := by
  have hu1 : (u : F) ≠ 1 := by intro h; apply hu; simp [h]
  have hui1 : (u : F)⁻¹ ≠ 1 := by simpa using hu1
  have hdiag : (1 : Matrix (Fin n) (Fin n) F) = diagonal (fun _ => 1) := by simp
  rw [hdiag, fromBlocks_diagonal] at hd
  have hz (i j : Fin 2 ⊕ Fin n)
      (hij : Sum.elim ![(u : F), (u : F)⁻¹] (fun _ => 1) i ≠
        Sum.elim ![(u : F), (u : F)⁻¹] (fun _ => 1) j) : M i j = 0 := by
    have h := congrArg (fun A => A i j) hd
    simp only [diagonal_mul, mul_diagonal] at h
    by_contra hn
    exact hij (mul_right_cancel₀ hn (h.trans (mul_comm _ _)))
  have h01 : M (.inl 0) (.inl 1) = 0 := hz _ _ hu
  have h10 : M (.inl 1) (.inl 0) = 0 := hz _ _ hu.symm
  have hlr (i : Fin 2) (j : Fin n) : M (.inl i) (.inr j) = 0 := by
    apply hz
    fin_cases i
    · exact hu1
    · exact hui1
  have hrl (i : Fin n) (j : Fin 2) : M (.inr i) (.inl j) = 0 := by
    apply hz
    fin_cases j
    · exact hu1.symm
    · exact hui1.symm
  have he : M (.inl 0) (.inl 0) = M (.inl 1) (.inl 1) := by
    have h := congrArg (fun A => A (.inl 0) (.inl 1)) hs
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using h.symm
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => fin_cases i <;> fin_cases j <;> simp [fromBlocks, Matrix.scalar, h01, h10, he]
    | inr j => simp [fromBlocks, hlr]
  | inr i => cases j with
    | inl j => simp [fromBlocks, hrl]
    | inr j => rfl

private theorem covering_shape {n : ℕ} (u : Fˣ)
    (hu : σ (u : F) * (u : F) = 1) (hne : (u : F) ≠ (u : F)⁻¹)
    (g : coveringCentralizer σ hσ (n := n)) :
    g.val.val.val = blockMatrix
      (Matrix.scalar (Fin 2) (g.val.val.val (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0))))
      (fun i j => g.val.val.val (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))) := by
  let E := reindexRingEquiv F (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2+n))
  let M := E.symm g.val.val.val
  have hh (A : (form σ hσ 2).specialSubgroup) :
      fromBlocks A.val.val 0 0 1 * M = M * fromBlocks A.val.val 0 0 1 := by
    apply E.injective
    rw [map_mul, map_mul]
    have h := congrArg (fun x : (form σ hσ (2+n)).specialSubgroup => x.val.val)
      (mem_centralizer_iff.mp g.property (left σ hσ A) ⟨A, rfl⟩)
    change blockMatrix A.val.val 1 * g.val.val.val =
      g.val.val.val * blockMatrix A.val.val 1 at h
    simpa [M, E, blockMatrix, coe_reindexRingEquiv, reindex_apply] using h
  have hm := matrix_shape u hne M (hh (diagSU σ hσ u hu)) (hh (swapSU σ hσ))
  have h := congrArg E hm
  simpa [M, E, blockMatrix, coe_reindexRingEquiv, reindex_apply] using h


/-- The covering centralizer is scalar on its marked two-space and preserves the complement. -/
theorem coveringCentralizer_matrix_eq [Finite F] {q : ℕ} (hq : 1 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q)
    {n : ℕ} (g : coveringCentralizer σ hσ (n := n)) :
    g.val.val.val = blockMatrix
      (Matrix.scalar (Fin 2) (g.val.val.val (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0))))
      (fun i j => g.val.val.val (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))) := by
  obtain ⟨u, hu, hne⟩ := exists_separating_norm_one σ hq hc hj
  exact covering_shape σ hσ u hu hne g

variable {n : ℕ} [Finite F] {q : ℕ}
variable (hq : 1 < q) (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q)

private def firstScalar (g : coveringCentralizer σ hσ (n := n)) : F :=
  g.val.val.val (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0))
private def lastMatrix (g : coveringCentralizer σ hσ (n := n)) : Matrix (Fin n) (Fin n) F :=
  fun i j => g.val.val.val (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))

include hq hc hj in
private theorem block_equations (g : coveringCentralizer σ hσ (n := n)) :
    σ (firstScalar σ hσ g) * firstScalar σ hσ g = 1 ∧
    (form σ hσ n).conjTranspose (lastMatrix σ hσ g) * lastMatrix σ hσ g = 1 ∧
    firstScalar σ hσ g ^ 2 * (lastMatrix σ hσ g).det = 1 := by
  have hg := ((form σ hσ (2+n)).mem_specialSubgroup_iff _).mp g.val.property
  have hm := coveringCentralizer_matrix_eq σ hσ hq hc hj g
  change g.val.val.val = blockMatrix (Matrix.scalar (Fin 2) (firstScalar σ hσ g))
    (lastMatrix σ hσ g) at hm
  have he : (form σ hσ (2+n)).conjTranspose g.val.val.val * g.val.val.val = 1 := by
    simpa only [form, mul_one] using hg.1
  rw [hm, blockMatrix_adj, ← blockMatrix_mul] at he
  have hn := congrArg (fun A : Matrix (Fin (2+n)) (Fin (2+n)) F =>
    A (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0))) he
  refine ⟨?_, ?_, ?_⟩
  · erw [blockMatrix_inl_inl] at hn
    simpa [Matrix.scalar, HermitianForm.conjTranspose,
      form, Matrix.mul_apply, Fin.sum_univ_two] using hn
  · ext i j
    have h := congrArg (fun A : Matrix (Fin (2+n)) (Fin (2+n)) F =>
      A (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))) he
    erw [blockMatrix_inr_inr] at h
    simpa [Matrix.one_apply] using h
  · have hd := congrArg Units.val hg.2
    change g.val.val.val.det = 1 at hd
    rw [hm, blockMatrix_det] at hd
    simpa using hd

include hq hc hj in
private theorem firstScalar_ne_zero (g : coveringCentralizer σ hσ (n := n)) :
    firstScalar σ hσ g ≠ 0 := by
  intro h
  have hh := (block_equations σ hσ hq hc hj g).1
  simp [h] at hh

/-- The character reads the scalar on the marked fundamental two-space. -/
def coveringCharacter : coveringCentralizer σ hσ (n := n) →* Fˣ where
  toFun g := Units.mk0 (firstScalar σ hσ g) (firstScalar_ne_zero σ hσ hq hc hj g)
  map_one' := by
    apply Units.ext
    change firstScalar σ hσ 1 = 1
    simp [firstScalar]
  map_mul' g k := by
    apply Units.ext
    change firstScalar σ hσ (g * k) = firstScalar σ hσ g * firstScalar σ hσ k
    unfold firstScalar
    change (g.val.val.val * k.val.val.val) _ _ = _
    rw [coveringCentralizer_matrix_eq σ hσ hq hc hj g,
      coveringCentralizer_matrix_eq σ hσ hq hc hj k]
    erw [← blockMatrix_mul, blockMatrix_inl_inl, blockMatrix_inl_inl, blockMatrix_inl_inl]
    simp [Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two]

/-- Evaluation of the character is the literal first-block matrix entry. -/
theorem coveringCharacter_apply_val (g : coveringCentralizer σ hσ (n := n)) :
    (coveringCharacter σ hσ hq hc hj g : F) =
      g.val.val.val (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0)) := (rfl)

/-- The unitary action on the complementary coordinate space. -/
def coveringComplement (g : coveringCentralizer σ hσ (n := n)) :
    (form σ hσ n).unitarySubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (lastMatrix σ hσ g) (by
    intro h
    have hh := (block_equations σ hσ hq hc hj g).2.2
    simp [h] at hh), by
    rw [HermitianForm.mem_unitarySubgroup_iff]
    change (form σ hσ n).conjTranspose (lastMatrix σ hσ g) * 1 * lastMatrix σ hσ g = 1
    rw [mul_one]
    exact (block_equations σ hσ hq hc hj g).2.1⟩

/-- The scalar has Hermitian norm one. -/
theorem coveringCharacter_norm (g : coveringCentralizer σ hσ (n := n)) :
    σ (coveringCharacter σ hσ hq hc hj g : F) * (coveringCharacter σ hσ hq hc hj g : F) = 1 :=
  (block_equations σ hσ hq hc hj g).1

/-- The determinant couples the scalar and complementary unitary block. -/
theorem coveringCharacter_det (g : coveringCentralizer σ hσ (n := n)) :
    coveringCharacter σ hσ hq hc hj g ^ 2 *
      GeneralLinearGroup.det (coveringComplement σ hσ hq hc hj g).val = 1 := by
  apply Units.ext
  exact (block_equations σ hσ hq hc hj g).2.2

/-- The exact matrix of a covering centralizer element. -/
theorem coveringCharacter_matrix (g : coveringCentralizer σ hσ (n := n)) :
    g.val.val.val = blockMatrix
      (Matrix.scalar (Fin 2) (coveringCharacter σ hσ hq hc hj g : F))
      (coveringComplement σ hσ hq hc hj g).val.val :=
  coveringCentralizer_matrix_eq σ hσ hq hc hj g

/-- Exactly the literal complementary SU map is killed by the scalar character. -/
theorem coveringCharacter_ker :
    (coveringCharacter σ hσ hq hc hj (n := n)).ker =
      (complementInCoveringCentralizer σ hσ).range := by
  ext g
  constructor
  · intro hg
    have ha : coveringCharacter σ hσ hq hc hj g = 1 := hg
    let B := coveringComplement σ hσ hq hc hj g
    have hd : GeneralLinearGroup.det B.val = 1 := by
      have h := coveringCharacter_det σ hσ hq hc hj g
      simpa only [ha, one_pow, one_mul] using h
    let b : (form σ hσ n).specialSubgroup := ⟨B.val, B.property, hd⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change blockMatrix 1 b.val.val = g.val.val.val
    rw [coveringCharacter_matrix σ hσ hq hc hj g, ha]
    simp only [Units.val_one, map_one]
    rfl
  · rintro ⟨b, rfl⟩
    apply Units.ext
    change firstScalar σ hσ (complementInCoveringCentralizer σ hσ b) = 1
    change blockMatrix (1 : Matrix (Fin 2) (Fin 2) F) b.val.val
      (finSumFinEquiv (.inl 0)) (finSumFinEquiv (.inl 0)) = 1
    erw [blockMatrix_inl_inl]
    simp

omit [Finite F] in
private theorem centralizes_of_scalar_block
    (g : (form σ hσ (2+n)).specialSubgroup) (a : F)
    (B : Matrix (Fin n) (Fin n) F)
    (hg : g.val.val = blockMatrix (Matrix.scalar (Fin 2) a) B) :
    g ∈ coveringCentralizer σ hσ := by
  apply mem_centralizer_iff.mpr
  rintro _ ⟨A, rfl⟩
  apply Subtype.ext
  apply Units.ext
  change blockMatrix A.val.val 1 * g.val.val = g.val.val * blockMatrix A.val.val 1
  rw [hg, ← blockMatrix_mul, ← blockMatrix_mul, one_mul, mul_one]
  congr 1
  exact (Matrix.scalar_commute a (Commute.all _) A.val.val).symm

include hq hc hj in
/-- Membership in the covering centralizer with all Hermitian and determinant constraints. -/
theorem mem_coveringCentralizer_iff (g : (form σ hσ (2+n)).specialSubgroup) :
    g ∈ coveringCentralizer σ hσ ↔
      ∃ (a : Fˣ) (B : (form σ hσ n).unitarySubgroup),
        σ (a : F) * (a : F) = 1 ∧
        a ^ 2 * GeneralLinearGroup.det B.val = 1 ∧
        g.val.val = blockMatrix (Matrix.scalar (Fin 2) (a : F)) B.val.val := by
  constructor
  · intro hg
    let c : coveringCentralizer σ hσ := ⟨g, hg⟩
    exact ⟨coveringCharacter σ hσ hq hc hj c, coveringComplement σ hσ hq hc hj c,
      coveringCharacter_norm σ hσ hq hc hj c, coveringCharacter_det σ hσ hq hc hj c,
      coveringCharacter_matrix σ hσ hq hc hj c⟩
  · rintro ⟨a, B, _, _, hg⟩
    exact centralizes_of_scalar_block σ hσ g a B.val.val hg

/-- The character required by the defining-prime residual computation. -/
theorem exists_covering_character {r e : ℕ} [Fact r.Prime]
    (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e)) :
    ∃ χ : coveringCentralizer σ hσ (n := n) →* Fˣ,
      χ.ker = (complementInCoveringCentralizer σ hσ).range := by
  have hq : 1 < r ^ e := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩ |>.one_lt
  exact ⟨coveringCharacter σ hσ hq hc hj, coveringCharacter_ker σ hσ hq hc hj⟩

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
