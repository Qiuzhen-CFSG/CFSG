module
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Cubic rank from a divisible diagonal torus

The existing diagonal and three-cycle witnesses give projective three-rank
at least two whenever the appropriate torus order is divisible by three.
For an odd-prime unitary field, an orthonormal basis transports these literal
matrices to the supplied Hermitian form. This is the parameter-free matrix
step needed in the nonnormal-component inspection of A.3.8, pp.45–46.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.SignedThreeCubicRank
variable {F : Type*} [Field F] [Finite F]

private theorem cubic_of_dvd (hd : 3 ∣ Nat.card F - 1) :
    ∃ u : F, u ^ 3 = 1 ∧ u ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  exact ⟨u, congrArg Units.val (orderOf_eq_prime_iff.mp hu).1,
    fun he => (orderOf_eq_prime_iff.mp hu).2 (Units.ext he)⟩

/-- The actual projective diagonal/cycle subgroup has order nine. -/
theorem linear_projective_of_three_dvd (hd : 3 ∣ Nat.card F - 1) :
    2 ≤ primeRank 3 PSL(3,F) := by
  obtain ⟨u, hu, hne⟩ := cubic_of_dvd hd
  exact projective_rank u hu hne ProjectiveSpecialLinearGroup.toPGL
    ProjectiveSpecialLinearGroup.toPGL_injective
    (QuotientGroup.mk (diagonal u hu)) (QuotientGroup.mk cycle) rfl rfl

/-- The projective unitary diagonal/cycle subgroup for an odd-prime model.
The statement retains the original field, form and Frobenius action. -/
theorem unitary_projective_of_three_dvd (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) (hd : 3 ∣ p + 1) :
    2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := hp.one_le
    have hh : p - 1 + 1 = p := by omega
    have hh2 : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (one_le_pow₀ hp.one_le)
    nlinarith
  obtain ⟨u, hu, hne⟩ := cubic_of_dvd (F := F) (by
    rw [hcard, hf]; exact dvd_mul_of_dvd_right hd (p - 1))
  have hnorm : J.conj u * u = 1 := by
    rw [hconj, ← pow_succ]
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hu, one_pow]
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    let : Fact p.Prime := ⟨hp⟩
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J p
    hcard hfixed
  let I := HermitianForm.IdentityGram.identityGram J
  have hD : SpecialLinearGroup.toGL (diagonal u hu) ∈ I.specialSubgroup := by
    rw [I.mem_specialSubgroup_iff]
    refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
    change I.conjTranspose (diagonal u hu).val * 1 * (diagonal u hu).val = 1
    rw [mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, HermitianForm.conjTranspose, I, Matrix.mul_apply,
        Fin.sum_univ_three, hnorm]
    calc J.conj u ^ 2 * u ^ 2 = (J.conj u * u) ^ 2 := by ring
         _ = 1 := by rw [hnorm]; simp
  have hcycle : SpecialLinearGroup.toGL (cycle (F := F)) ∈ I.specialSubgroup := by
    rw [I.mem_specialSubgroup_iff]
    refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
    change I.conjTranspose (cycle (F := F)).val * 1 * (cycle (F := F)).val = 1
    rw [mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycle, HermitianForm.conjTranspose, I, Matrix.mul_apply, Fin.sum_univ_three]
  let : Finite (PGL(3,F)) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hr := projective_rank u hu hne (ProjectiveSpecialUnitaryMatrixGroup I).subtype
    (ProjectiveSpecialUnitaryMatrixGroup I).subtype_injective
    ⟨_, ⟨_, hD, rfl⟩⟩ ⟨_, ⟨_, hcycle, rfl⟩⟩ rfl rfl
  rw [Theory.GroupTheory.primeRank_equiv 3
    (HermitianForm.IdentityGram.projectiveEquiv J C hC)]
  exact hr

end Theory.SpecificGroups.SignedThreeCubicRank
