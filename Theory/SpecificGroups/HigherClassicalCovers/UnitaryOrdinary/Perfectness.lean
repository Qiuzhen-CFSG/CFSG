module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Basic
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Perfectness of the ordinary SU₄ and SU₅ natural covers

For SU₅(4), each scalar fifth root is the commutator of a determinant-one
norm-one diagonal matrix with a five-cycle. For SU₄(q) with eight dividing
q+1, a primitive norm-one eighth root supplies a diagonal matrix whose
commutator with a signed four-cycle generates the scalar kernel. Thus the
whole projective kernel lies in the derived subgroup. Perfectness of the
actual projective image then makes the full special-unitary group perfect.
Orthonormal basis changes transport these arguments to the original form.

These are the perfectness inputs for the ordinary unitary coverings in
Aschbacher--Smith I.1.3--4, pp.407--408, and GLS3 Section 6.1. Only projective
perfectness, inherited from the source quotient, remains an input; there is
no assumed scalar commutator, matrix-group perfectness or multiplier bound.
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
open scoped commutatorElement
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
variable {F : Type*} [Field F]

private def diagonalSU {n : ℕ} (J : HermitianForm n F) (hJ : J.form = 1)
    (d : Fin n → F) (hd : ∀ i, J.conj (d i) * d i = 1)
    (hp : ∏ i, d i = 1) : J.specialSubgroup := by
  let D := diagonal d
  have hdet : D.det = 1 := by simpa [D] using hp
  refine ⟨GeneralLinearGroup.mkOfDetNeZero D (hdet ▸ one_ne_zero), ?_⟩
  constructor
  · change J.conjTranspose D * J.form * D = J.form
    rw [hJ, mul_one]
    have hadj : J.conjTranspose D = diagonal (fun i => J.conj (d i)) := by
      ext i j
      by_cases h : i = j <;> simp [D, HermitianForm.conjTranspose, h, Ne.symm]
    rw [hadj, diagonal_mul_diagonal]
    exact (congrArg diagonal (funext hd)).trans diagonal_one
  · apply Units.ext
    exact hdet

private def cycleFive : Matrix (Fin 5) (Fin 5) F :=
  !![0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1; 1,0,0,0,0]

private theorem cycleFive_eq : cycleFive (F := F) =
    (1 : Matrix (Fin 5) (Fin 5) F).submatrix
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 :
        Equiv.Perm (Fin 5)) id := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleFive, Matrix.submatrix, Matrix.one_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def]

private theorem cycleFive_det : (cycleFive (F := F)).det = 1 := by
  rw [cycleFive_eq, Matrix.det_permute]
  simp

private theorem permutation_unitary {n : ℕ} (J : HermitianForm n F)
    (σ : Equiv.Perm (Fin n)) :
    J.conjTranspose ((1 : Matrix (Fin n) (Fin n) F).submatrix σ id) *
      (1 : Matrix (Fin n) (Fin n) F).submatrix σ id = 1 := by
  have ha : J.conjTranspose ((1 : Matrix (Fin n) (Fin n) F).submatrix σ id) =
      (1 : Matrix (Fin n) (Fin n) F).submatrix id σ := by
    ext i j
    by_cases h : σ j = i <;> simp [HermitianForm.conjTranspose, Matrix.submatrix,
      Matrix.one_apply, h, Ne.symm, eq_comm]
  rw [ha, Matrix.submatrix_mul_equiv, one_mul, Matrix.submatrix_id_id]

private theorem cycleFive_unitary (J : HermitianForm 5 F) :
    J.conjTranspose cycleFive * cycleFive = 1 := by
  rw [cycleFive_eq]
  exact permutation_unitary J _

private def cycleFiveSU (J : HermitianForm 5 F) (hJ : J.form = 1) :
    J.specialSubgroup := by
  let W : GL (Fin 5) F := ⟨cycleFive, J.conjTranspose cycleFive,
    mul_eq_one_comm.mp (cycleFive_unitary J), cycleFive_unitary J⟩
  refine ⟨W, ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose cycleFive * J.form * cycleFive = J.form
    rw [hJ, mul_one]
    exact cycleFive_unitary J
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact cycleFive_det (F := F)

private theorem scalarFive_mem_commutator (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) (u : rootsOfUnity 5 F) :
    (scalarToKernel J hconj u).val ∈ commutator J.specialSubgroup := by
  let a : F := u.val
  have ha : a ^ 5 = 1 := (mem_rootsOfUnity' 5 u.val).mp u.property
  have hp (k : ℕ) : J.conj (a ^ k) * a ^ k = 1 := by
    rw [hconj, ← pow_succ, ← pow_mul, Nat.mul_comm k 5, pow_mul, ha, one_pow]
  let D := diagonalSU J hJ ![1,a^4,a^3,a^2,a]
    (by
      intro i
      fin_cases i
      · simp
      · exact hp 4
      · exact hp 3
      · exact hp 2
      · simpa using hp 1)
    (by simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, Fin.prod_univ_zero, mul_one, one_mul]
        calc
          a ^ 4 * (a ^ 3 * (a ^ 2 * a)) = (a ^ 5) ^ 2 := by ring
          _ = 1 := by rw [ha, one_pow])
  let W := cycleFiveSU J hJ
  let s := (scalarToKernel J hconj u).val
  have he : D * W = s * W * D := by
    apply Subtype.ext
    apply Units.ext
    change diagonal ![1,a^4,a^3,a^2,a] * cycleFive =
      (GeneralLinearGroup.scalar (Fin 5) u.val).val * cycleFive * diagonal ![1,a^4,a^3,a^2,a]
    rw [GeneralLinearGroup.coe_scalar]
    have ha' : (u.val : F) ^ 5 = 1 := ha
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleFive, Matrix.scalar, diagonal_mul, mul_diagonal,
        ← pow_succ', ← sq, a, ha']
  have hs : ⁅D, W⁆ = s := by
    rw [commutatorElement_def, he]
    group
  change s ∈ commutator J.specialSubgroup
  rw [← hs]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top W)

private theorem perfect_of_kernel_le {n : ℕ} (J : HermitianForm n F)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hk : (project J).ker ≤ commutator J.specialSubgroup) :
    Group.IsPerfect J.specialSubgroup := by
  have hm : (commutator J.specialSubgroup).map (project J) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (project_surjective J)]
    exact Group.IsPerfect.commutator_eq_top
  have hc := congrArg (Subgroup.comap (project J)) hm
  rw [Subgroup.comap_map_eq, Subgroup.comap_top, sup_eq_left.mpr hk] at hc
  exact ⟨hc⟩

private theorem fiveFour_identity_isPerfect (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)] :
    Group.IsPerfect J.specialSubgroup := by
  apply perfect_of_kernel_le J
  intro A hA
  obtain ⟨u, hu⟩ := (scalarToKernel_bijective J hconj).2 ⟨A, hA⟩
  have he : (scalarToKernel J hconj u).val = A := congrArg Subtype.val hu
  rw [← he]
  exact scalarFive_mem_commutator J hJ hconj u

/-- Perfectness of the actual special unitary group over the field of order 16. -/
theorem fiveFour_isPerfect [Finite F] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)] :
    Group.IsPerfect J.specialSubgroup := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 4 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
      (by decide) (by simpa using hcard) (by simpa using hconj)
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J 4 (by simpa using hcard) hf
  let e := HermitianForm.IdentityGram.specialEquiv J C hC
  let ep := HermitianForm.IdentityGram.projectiveEquiv J C hC
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup
      (HermitianForm.IdentityGram.identityGram J)) :=
    Group.IsPerfect.ofSurjective (f := ep.toMonoidHom) ep.surjective
  let : Group.IsPerfect (HermitianForm.IdentityGram.identityGram J).specialSubgroup :=
    fiveFour_identity_isPerfect _ rfl hconj
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private def cycleFour : Matrix (Fin 4) (Fin 4) F :=
  !![0,1,0,0; 0,0,1,0; 0,0,0,1; -1,0,0,0]

private theorem cycleFour_det : (cycleFour (F := F)).det = 1 := by
  have he : cycleFour (F := F) =
      (diagonal ![1,1,1,-1] : Matrix (Fin 4) (Fin 4) F) *
        (1 : Matrix (Fin 4) (Fin 4) F).submatrix
          (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) id := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleFour, diagonal_mul, Matrix.submatrix, Matrix.one_apply,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  rw [he, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute]
  simp [Fin.prod_univ_succ]

private theorem cycleFour_unitary (J : HermitianForm 4 F) :
    J.conjTranspose cycleFour * cycleFour = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleFour, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]

private def cycleFourSU (J : HermitianForm 4 F) (hJ : J.form = 1) :
    J.specialSubgroup := by
  let W : GL (Fin 4) F := ⟨cycleFour, J.conjTranspose cycleFour,
    mul_eq_one_comm.mp (cycleFour_unitary J), cycleFour_unitary J⟩
  refine ⟨W, ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose cycleFour * J.form * cycleFour = J.form
    rw [hJ, mul_one]
    exact cycleFour_unitary J
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact cycleFour_det (F := F)

private theorem scalarFourSquare_mem_commutator (J : HermitianForm 4 F)
    (hJ : J.form = 1) {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q)
    (v : Fˣ) (hv : v ^ 8 = 1) (hn : v ^ (q + 1) = 1)
    (u : rootsOfUnity (Nat.gcd 4 (q + 1)) F) (hu : u.val = v ^ 2) :
    (scalarToKernel J hconj u).val ∈ commutator J.specialSubgroup := by
  let a : F := v
  have ha : a ^ 8 = 1 := congrArg Units.val hv
  have han : a ^ (q + 1) = 1 := congrArg Units.val hn
  have hp (k : ℕ) : J.conj (a ^ k) * a ^ k = 1 := by
    rw [hconj, ← pow_succ, ← pow_mul, Nat.mul_comm k (q + 1), pow_mul, han, one_pow]
  let D := diagonalSU J hJ ![a^7,a^5,a^3,a]
    (by
      intro i
      fin_cases i
      · exact hp 7
      · exact hp 5
      · exact hp 3
      · simpa using hp 1)
    (by
      simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Fin.prod_univ_zero, mul_one]
      calc
        a ^ 7 * (a ^ 5 * (a ^ 3 * a)) = (a ^ 8) ^ 2 := by ring
        _ = 1 := by rw [ha, one_pow])
  let W := cycleFourSU J hJ
  let s := (scalarToKernel J hconj u).val
  have he : D * W = s * W * D := by
    apply Subtype.ext
    apply Units.ext
    change diagonal ![a^7,a^5,a^3,a] * cycleFour =
      (GeneralLinearGroup.scalar (Fin 4) u.val).val * cycleFour * diagonal ![a^7,a^5,a^3,a]
    rw [hu, GeneralLinearGroup.coe_scalar]
    have ha9 : (v : F) ^ 9 = v := by rw [pow_succ, show (v : F) ^ 8 = 1 from ha, one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleFour, Matrix.scalar, diagonal_mul, mul_diagonal, a,
        ← pow_add, ← pow_succ, ha9]
  have hs : ⁅D, W⁆ = s := by
    rw [commutatorElement_def, he]
    group
  change s ∈ commutator J.specialSubgroup
  rw [← hs]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top W)

private theorem four_identity_isPerfect [Finite F] (J : HermitianForm 4 F)
    (hJ : J.form = 1) {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (h8 : 8 ∣ q + 1)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)] :
    Group.IsPerfect J.specialSubgroup := by
  have hq : 0 < q := by
    have := Nat.card_pos (α := F)
    rw [hcard] at this
    nlinarith
  have hsplit : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have he : q = q - 1 + 1 := by omega
    have hpow : q ^ 2 = (q + 1) * (q - 1) + 1 := by nlinarith
    omega

  have hg : Nat.gcd 4 (q + 1) = 4 :=
    Nat.gcd_eq_left_iff_dvd.mpr ((show 4 ∣ 8 by decide).trans h8)
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hd : 8 ∣ orderOf a := by
    rw [ha, Nat.card_units, hcard, hsplit]
    exact h8.trans (dvd_mul_right _ _)
  let v := a ^ (orderOf a / 8)
  have hv : IsPrimitiveRoot v 8 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_pow_orderOf_div (orderOf_pos a).ne' hd)
  have hv2 : IsPrimitiveRoot (v ^ 2) 4 := hv.pow (by decide) (by decide)
  let u₀ : rootsOfUnity (Nat.gcd 4 (q + 1)) F :=
    ⟨v ^ 2, by rw [mem_rootsOfUnity, hg]; exact hv2.pow_eq_one⟩
  have hm := scalarFourSquare_mem_commutator J hJ hconj v hv.pow_eq_one
    ((hv.pow_eq_one_iff_dvd _).mpr h8) u₀ rfl
  apply perfect_of_kernel_le J
  intro A hA
  obtain ⟨u, hu⟩ := (scalarToKernel_bijective J hconj).2 ⟨A, hA⟩
  have he : (scalarToKernel J hconj u).val = A := congrArg Subtype.val hu
  have hur : u.val ∈ rootsOfUnity 4 F := by simpa only [hg] using u.property
  obtain ⟨k, _, hk⟩ := hv2.eq_pow_of_mem_rootsOfUnity hur
  have huk : u = u₀ ^ k := Subtype.ext hk.symm
  rw [← he, huk, map_pow]
  exact (commutator J.specialSubgroup).pow_mem hm k

/-- A norm-one eighth root puts the whole scalar kernel in the derived group.
This proves perfectness for the Mersenne primes greater than three. -/
theorem fourMersenne_isPerfect [Finite F] (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)] :
    Group.IsPerfect J.specialSubgroup := by
  obtain ⟨k, hk⟩ := hm
  have hk3 : 3 ≤ k := by
    by_contra h
    interval_cases k <;> norm_num at hk <;> omega
  have h8 : 8 ∣ q + 1 := by rw [hk]; exact Nat.pow_dvd_pow 2 hk3
  obtain ⟨C, _, _, hC, _, _⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J q hp hcard hconj
  let e := HermitianForm.IdentityGram.specialEquiv J C hC
  let ep := HermitianForm.IdentityGram.projectiveEquiv J C hC
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup
      (HermitianForm.IdentityGram.identityGram J)) :=
    Group.IsPerfect.ofSurjective (f := ep.toMonoidHom) ep.surjective
  let : Group.IsPerfect (HermitianForm.IdentityGram.identityGram J).specialSubgroup :=
    four_identity_isPerfect _ rfl hcard hconj h8
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
