module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# The canonical special-unitary projective kernel

For the actual special unitary group of a nondegenerate Hermitian form, the
kernel of its map to PGL consists of scalar matrices. Determinant one gives
`u^n = 1`, and the Hermitian equation gives `u^(q+1) = 1` when conjugation is
the q-power map. Thus the kernel is multiplicatively equivalent to the
`gcd(n,q+1)`-th roots of unity, and has that order over a field of order q².
The proof retains the original form and does not use a simplicity theorem.

This computes the canonical kernel only. Universality and the exceptional
Schur multiplier require separate proofs. Source: GLS3, Section 6.1,
Theorem 6.1.2, unitary row of Table 6.1.2; the matrix calculation generalizes
`Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel`.
-/

public section

open BenderSuzuki.MatrixGroups Matrix Subgroup

namespace Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
variable {n : ℕ} {F : Type*} [Field F] (J : HermitianForm n F)

/-- The literal map from SU to its image in PGL. -/
@[expose] def project : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ProjGenLinGroup.mk.subgroupMap J.specialSubgroup

/-- Projectivization is onto its defining image. -/
theorem project_surjective : Function.Surjective (project J) :=
  MonoidHom.subgroupMap_surjective _ _

/-- Projectively trivial matrices are central in the special unitary group. -/
theorem project_kernel_le_center : (project J).ker ≤ center J.specialSubgroup := by
  intro A hA
  have hz : A.val ∈ center (GL (Fin n) F) :=
    ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hA))
  exact mem_center_iff.mpr fun B => Subtype.ext (mem_center_iff.mp hz B.val)

/-- The determinant and Hermitian equations for a scalar matrix. -/
theorem scalar_special_iff [NeZero n] {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q)
    (u : Fˣ) :
    GeneralLinearGroup.scalar (Fin n) u ∈ J.specialSubgroup ↔
      u ^ n = 1 ∧ u ^ (q + 1) = 1 := by
  have ha : J.conjTranspose (GeneralLinearGroup.scalar (Fin n) u).val =
      diagonal (fun _ => J.conj (u : F)) := by
    ext i j
    by_cases h : i = j <;>
      simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar,
        Matrix.scalar, h, Ne.symm]
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rintro ⟨hs, hd⟩
    refine ⟨by simpa using hd, ?_⟩
    have hentry : ∃ i j, J.form i j ≠ 0 := by
      by_contra! h
      have hzero : J.form = 0 := Matrix.ext fun i j => h i j
      exact J.form_nondegenerate (by simp [hzero])
    obtain ⟨i, j, hij⟩ := hentry
    rw [ha, GeneralLinearGroup.coe_scalar] at hs
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hs
    change (diagonal (fun _ : Fin n => J.conj (u : F)) * J.form *
      diagonal (fun _ : Fin n => (u : F))) i j = J.form i j at he
    simp only [diagonal_mul, mul_diagonal, hconj] at he
    apply Units.ext
    change (u : F) ^ (q + 1) = 1
    apply mul_right_cancel₀ hij
    calc
      (u : F) ^ (q + 1) * J.form i j =
          (u : F) ^ q * J.form i j * (u : F) := by rw [pow_succ]; ring
      _ = 1 * J.form i j := by simpa only [one_mul] using he
  · rintro ⟨hd, hn⟩
    constructor
    · rw [ha, GeneralLinearGroup.coe_scalar]
      ext i j
      change (diagonal (fun _ : Fin n => J.conj (u : F)) * J.form *
        diagonal (fun _ : Fin n => (u : F))) i j = J.form i j
      simp only [diagonal_mul, mul_diagonal, hconj]
      have hn' : (u : F) ^ (q + 1) = 1 := congrArg Units.val hn
      calc
        (u : F) ^ q * J.form i j * (u : F) =
            (u : F) ^ (q + 1) * J.form i j := by rw [pow_succ]; ring
        _ = J.form i j := by rw [hn', one_mul]
    · simpa using hd

variable [NeZero n] {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q)

/-- The scalar embedding of the common roots into the actual projective kernel. -/
@[expose] def scalarToKernel : rootsOfUnity (Nat.gcd n (q + 1)) F →* (project J).ker where
  toFun u := ⟨⟨GeneralLinearGroup.scalar (Fin n) u.val,
    (scalar_special_iff J hconj u.val).mpr
      (pow_gcd_eq_one.mp ((mem_rootsOfUnity _ u.val).mp u.property))⟩, by
        apply Subtype.ext
        exact ProjGenLinGroup.mk_scalar u.val⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (GeneralLinearGroup.scalar (Fin n))
  map_mul' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (GeneralLinearGroup.scalar (Fin n)) u.val v.val

/-- Every projectively trivial SU matrix is a unique such scalar. -/
theorem scalarToKernel_bijective : Function.Bijective (scalarToKernel J hconj) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Units.ext
    have he := congrArg (fun A : (project J).ker =>
      (A.val.val : Matrix (Fin n) (Fin n) F) 0 0) h
    simpa [scalarToKernel, GeneralLinearGroup.coe_scalar, Matrix.scalar] using he
  · intro A
    have hA : ProjGenLinGroup.mk A.val.val = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp A.property)
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hA
    obtain ⟨u, hu⟩ := hA
    have hs : GeneralLinearGroup.scalar (Fin n) u ∈ J.specialSubgroup :=
      hu ▸ A.val.property
    have hr : u ∈ rootsOfUnity (Nat.gcd n (q + 1)) F :=
      (mem_rootsOfUnity _ u).mpr (pow_gcd_eq_one.mpr
        ((scalar_special_iff J hconj u).mp hs))
    refine ⟨⟨u, hr⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu

/-- The scalar kernel as a group, without a simplicity assumption. -/
@[expose] noncomputable def scalarKernelEquiv :
    rootsOfUnity (Nat.gcd n (q + 1)) F ≃* (project J).ker :=
  MulEquiv.ofBijective (scalarToKernel J hconj) (scalarToKernel_bijective J hconj)

include hconj in
/-- The canonical unitary covering kernel has order `gcd(n,q+1)`. -/
theorem card_project_kernel [Finite F] (hcard : Nat.card F = q ^ 2) :
    Nat.card (project J).ker = Nat.gcd n (q + 1) := by
  rw [← Nat.card_congr (scalarKernelEquiv J hconj).toEquiv]
  have hq : 0 < q := by
    have h := Nat.card_pos (α := F)
    rw [hcard] at h
    exact Nat.pos_of_ne_zero (by intro hz; simp [hz] at h)
  have hg : 0 < Nat.gcd n (q + 1) := Nat.gcd_pos_of_pos_right _ (by omega)
  let : NeZero (Nat.gcd n (q + 1)) := ⟨hg.ne'⟩
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  apply (Nat.gcd_dvd_right n (q + 1)).trans
  refine ⟨q - 1, ?_⟩
  have he : q ^ 2 = (q + 1) * (q - 1) + 1 := by
    have he' : q = q - 1 + 1 := by omega
    nlinarith
  omega

include hconj in
/-- In even characteristic the canonical unitary kernel has odd order. -/
theorem odd_card_project_kernel [Finite F] (hcard : Nat.card F = q ^ 2)
    (he : Even q) : Odd (Nat.card (project J).ker) := by
  rw [card_project_kernel J hconj hcard]
  exact he.add_one.of_dvd_nat (Nat.gcd_dvd_right n (q + 1))

end Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
