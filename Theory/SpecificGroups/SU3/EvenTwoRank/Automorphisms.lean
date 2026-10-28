module

public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Binary PSU₃ automorphism rank from semilinear coverage

The unitary diagonal image in the actual outer automorphism group has exponent
three. Under arbitrary-automorphism semilinear coverage, the quotient above
that image is cyclic, so the outer two-rank is at most one. The scalar
centralizer of the concrete projective model proves its center trivial;
therefore its inner automorphism group has the already calculated rank n.
The kernel/image rank inequality gives the bound n+1. A genuine Hermitian
basis change transports the result to an arbitrary form.

Only semilinear coverage remains an explicit structural premise. This is a
conditional numerical calculation, not the unconditional automorphism theorem.
Source: Aschbacher–Smith, printed p.356 and 16.1.7(3b), p.1172;
GLS3, Theorem 2.5.12 and §2.7 for the concrete semilinear action.
-/

noncomputable section
public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
variable {E : Type*} [Field E] [Finite E]

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The actual diagonal outer image has no two-rank: each element has cube one. -/
theorem diagonal_two_rank_zero (J : HermitianForm 3 E) :
    primeRank 2 J.unitaryOuterHom.range = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply primeRank_le_of_pow_eq_one_subset (⊥ : Subgroup J.unitaryOuterHom.range)
  · simp
  · intro x hx
    have hc : x ^ 3 = 1 := by
      obtain ⟨u, hu⟩ := x.property
      obtain ⟨b, hb⟩ := J.unitaryConj_cube_is_inner u
      apply Subtype.ext
      change x.val ^ 3 = 1
      rw [← hu]
      change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (J.unitaryConjHom u)) ^ 3 = 1
      rw [← map_pow, J.unitaryConjHom_apply, hb]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
    have he : x = 1 := by
      simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hx, one_mul] using hc
    exact Subgroup.mem_bot.mpr he

/-- Semilinear coverage makes the outer group cyclic modulo its odd diagonal image. -/
theorem outer_two_rank_le_of_coverage (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    primeRank 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 1 := by
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcoverage
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcoverage
  have h := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' J.unitaryOuterHom.range)
  rw [QuotientGroup.ker_mk', diagonal_two_rank_zero, zero_add] at h
  let P : Sylow 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) ⧸
    J.unitaryOuterHom.range) := Classical.choice inferInstance
  exact h.trans (P.primeRank_le_one_of_isCyclic inferInstance)

omit [Finite E] in
/-- The matrix scalar-centralizer calculation makes the actual PSU image centerless. -/
theorem standard_center_eq_bot [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  apply mem_bot.mpr
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
  apply J.projective_centralizer_scalar hJ hconj
  intro b
  have he := congrArg Subtype.val ((mem_center_iff.mp hx b).symm)
  change (Matrix.ProjGenLinGroup.mk (u : Matrix.GeneralLinearGroup (Fin 3) E)) *
      (b : Matrix.ProjGenLinGroup (Fin 3) E) =
      (b : Matrix.ProjGenLinGroup (Fin 3) E) *
        Matrix.ProjGenLinGroup.mk (u : Matrix.GeneralLinearGroup (Fin 3) E)
  simpa only [Subgroup.coe_mul, J.specialToProjective_apply_val] using he

omit [Finite E] in
private theorem exists_nonfixed (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    ∃ t : E, J.conj t ≠ t := by
  by_contra! h
  have hc : Nat.card {x : E // J.conj x = x} = Nat.card E :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  rw [hcard, hfixed] at hc
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  nlinarith

/-- With arbitrary-automorphism coverage, the only extra two-rank is the cyclic
field quotient; no numerical rank hypothesis is used. -/
theorem standard_automorphism_two_rank_le_of_coverage (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ n + 1 := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hcenter := standard_center_eq_bot J hJ (exists_nonfixed J hn hcard hfixed)
  let e := MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hcenter)
  have hi : primeRank 2 (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = n :=
    (primeRank_equiv 2 e).symm.trans (standard_two_rank J hJ hn hcard hfixed)
  have h := primeRank_le_ker_add (p := 2)
    (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
  rw [QuotientGroup.ker_mk', hi] at h
  exact h.trans (Nat.add_le_add_left (outer_two_rank_le_of_coverage J hJ hcoverage) n)

open OddPrimeSylow.NormalizedOuter.FormTransport

/-- Transport through a genuine Hermitian change of basis preserves the full
automorphism group. Coverage is needed only for the standard form. -/
theorem automorphism_two_rank_le_of_standard_coverage (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)),
      ∃ σ : E ≃+* E, (standardForm J).HasUnitarySemilinearForm a σ) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ n + 1 := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact standard_automorphism_two_rank_le_of_coverage (standardForm J) rfl hn
    hcard hfixed hcoverage

end BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
