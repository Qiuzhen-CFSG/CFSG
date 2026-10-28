module

public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.MatrixWitnesses
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.QuasithinBasic

/-!
# Cubic rank witnesses in signed degree three

A primitive cubic scalar and the diagonal matrix diag(1,u,u²) generate an
order-nine elementary subgroup in SL₃. After passage to the projective
quotient, diag(1,u,u²) and the coordinate three-cycle provide another such
subgroup. For SU₃ the cubic scalars have norm one when the fixed-field degree
is odd; an orthonormal basis transports the same witnesses to every stored
nondegenerate Hermitian form.

Source application: Aschbacher–Smith, proof of 13.8.20(a), printed p.954
(PDF p.971), excluding the other signed-three parities from three-rank one.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.SignedThreeCubicRank
variable {F : Type*} [Field F]

private theorem exists_cubic [Finite F] (hd : 3 ∣ Nat.card F - 1) :
    ∃ u : F, u ^ 3 = 1 ∧ u ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  refine ⟨u, ?_, ?_⟩
  · exact congrArg Units.val (orderOf_eq_prime_iff.mp hu).1
  · intro he
    exact (orderOf_eq_prime_iff.mp hu).2 (Units.ext he)

/-- In even binary field degree, SL₃ contains two independent diagonal cubics. -/
theorem linear_special [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hn : Even n) : 2 ≤ primeRank 3 SL(3,F) := by
  obtain ⟨u, hu, hne⟩ := exists_cubic (F := F) (by
    rw [hcard]; exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn)
  exact special_rank u hu hne SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    (diagonal u hu) (scalar u hu) rfl rfl

/-- The diagonal/cycle elementary subgroup survives in PSL₃ in even binary degree. -/
theorem linear_projective [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hn : Even n) : 2 ≤ primeRank 3 PSL(3,F) := by
  obtain ⟨u, hu, hne⟩ := exists_cubic (F := F) (by
    rw [hcard]; exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn)
  exact projective_rank u hu hne ProjectiveSpecialLinearGroup.toPGL
    ProjectiveSpecialLinearGroup.toPGL_injective
    (QuotientGroup.mk (diagonal u hu)) (QuotientGroup.mk cycle) rfl rfl

private theorem diagonal_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (diagonal u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (diagonal u hu).val * (diagonal u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hnorm]
  calc J.conj u ^ 2 * u ^ 2 = (J.conj u * u) ^ 2 := by ring
       _ = 1 := by rw [hnorm]; simp

private theorem scalar_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (scalar u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (scalar u hu).val * (scalar u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalar, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hnorm]

private theorem cycle_unitary (J : HermitianForm 3 F) (hJ : J.form = 1) :
    SpecialLinearGroup.toGL (cycle (F := F)) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (cycle (F := F)).val * (cycle (F := F)).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]

private theorem identity_unitary_ranks [Finite F]
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    2 ≤ primeRank 3 J.specialSubgroup ∧
      2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hD := diagonal_unitary u hu J hJ hnorm
  have hZ := scalar_unitary u hu J hJ hnorm
  have hC := cycle_unitary J hJ
  let : Finite (PGL(3,F)) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  constructor
  · exact special_rank u hu hne J.specialSubgroup.subtype J.specialSubgroup.subtype_injective
      ⟨_, hD⟩ ⟨_, hZ⟩ rfl rfl
  · exact projective_rank u hu hne (ProjectiveSpecialUnitaryMatrixGroup J).subtype
      (ProjectiveSpecialUnitaryMatrixGroup J).subtype_injective
      ⟨_, ⟨_, hD, rfl⟩⟩ ⟨_, ⟨_, hC, rfl⟩⟩ rfl rfl

private theorem unitary_ranks [Finite F] (J : HermitianForm 3 F) {n : ℕ}
    (hnpos : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (hn : Odd n) :
    2 ≤ primeRank 3 J.specialSubgroup ∧
      2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨u, hu, hne⟩ := exists_cubic (F := F) (by
    rw [hcard, ← pow_mul]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff (n * 2)).mpr ⟨n, by omega⟩)
  have hnorm : J.conj u * u = 1 := by
    rw [hconj, ← pow_succ]
    have hd : 3 ∣ 2 ^ n + 1 := by
      have hm := Nat.BinaryTorusParity.two_pow_mod_three n
      have ho := Nat.odd_iff.mp hn
      rw [ho] at hm
      norm_num at hm
      omega
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hu, one_pow]
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hnpos hcard hconj
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J (2 ^ n)
    hcard hfixed
  obtain ⟨hs, hp⟩ := identity_unitary_ranks u hu hne (HermitianForm.IdentityGram.identityGram J)
    rfl hnorm
  let : Finite (PGL(3,F)) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  constructor
  · rwa [Theory.GroupTheory.primeRank_equiv 3 (HermitianForm.IdentityGram.specialEquiv J C hC)]
  · rwa [Theory.GroupTheory.primeRank_equiv 3 (HermitianForm.IdentityGram.projectiveEquiv J C hC)]

/-- In odd positive binary fixed-field degree, every SU₃ has three-rank at least two. -/
theorem unitary_special [Finite F] (J : HermitianForm 3 F) {n : ℕ}
    (hnpos : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (hn : Odd n) :
    2 ≤ primeRank 3 J.specialSubgroup :=
  (unitary_ranks J hnpos hcard hconj hn).1

/-- The diagonal/cycle witness gives the same bound in the actual projective SU₃ image. -/
theorem unitary_projective [Finite F] (J : HermitianForm 3 F) {n : ℕ}
    (hnpos : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (hn : Odd n) :
    2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (unitary_ranks J hnpos hcard hconj hn).2

end Theory.SpecificGroups.SignedThreeCubicRank
end
