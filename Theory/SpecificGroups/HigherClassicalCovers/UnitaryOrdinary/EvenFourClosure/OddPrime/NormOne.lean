module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.NormOneIndex
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence

/-!
# Norm-one primes in binary SU₄ covering kernels

For odd p dividing q+1, q = 2^n, the full Sylow p-subgroup of GF(q²)ˣ
consists of norm-one coefficients. Its rank-three diagonal torus and
coordinate three-cycle have index prime to p, by the determinant-kernel
valuation calculation. Swaps make the torus preimage abelian; the
three-cycle norm argument handles the nonabelian Sylow three-subgroups.
Orthonormal basis change followed by the injective natural projection
transports the literal covering map without changing its kernel.

The parameter argument extends the checked `UnitaryQuadratic.NormOneIndex`
result to binary extension fields. Source: Aschbacher–Smith I.1.1–4,
printed pp.407–408 of `refs/quasithin.pdf`, and GLS3 §6.1.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic

public noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime

variable {F : Type*} [Field F] [Finite F]

theorem exists_binary_normOne_torus_prime_index
    (J : HermitianForm 4 F) (hJ : J.form = 1) (n : ℕ)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n + 1) :
    ∃ (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1),
      (Nat.card C).Coprime 2 ∧
        ¬ p ∣ ((diagonalProjective J hJ C hC).range ⊔ zpowers (cycle J hJ)).index := by
  let P : Sylow p Fˣ := default
  have hcop : p.Coprime (2 ^ n - 1) := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro he
    have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
    have ht : p ∣ 2 := by
      convert Nat.dvd_sub hd he using 1
      omega
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp ht)
  have hP : Nat.card P ∣ 2 ^ n + 1 := by
    have hc : (Nat.card P).Coprime (2 ^ n - 1) := by
      rw [P.card_eq_multiplicity]
      exact hcop.pow_left _
    apply hc.dvd_of_dvd_mul_left
    have he := P.toSubgroup.card_subgroup_dvd_card
    rw [Nat.card_units, hcard] at he
    have heq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa only [one_pow] using Nat.sq_sub_sq (2 ^ n) 1
    simpa only [heq, mul_comm] using he
  have hC : ∀ u : P, J.conj (u.val : F) * (u.val : F) = 1 := by
    intro u
    rw [hconj, ← pow_succ]
    have he : u ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard u).trans hP)
    exact congrArg (fun v : P => (v.val : F)) he
  refine ⟨P.toSubgroup, hC, sylow_units_card_coprime_two hp P, ?_⟩
  apply diagonal_cycle_index_of_sylow J hJ hp _ P hC
  rw [hcard]
  have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa only [one_pow] using Nat.sq_sub_sq (2 ^ n) 1
  rw [he]
  exact dvd_mul_of_dvd_left hd _

theorem not_dvd_kernel_of_dvd_succ
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n + 1)
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  let K := UnitaryFourFormTransport.standardForm J
  let I := HermitianForm.IdentityGram.identityGram K
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 4 K
    (2 ^ n) hcard (UnitaryFourFormTransport.fixed_card K n hn hcard hconj)
  have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  let e : Standard J ≃* ProjectiveSpecialUnitaryMatrixGroup I :=
    (HermitianForm.IdentityGram.specialEquiv K C hC).trans
      (fourEvenProjectEquiv I heven hcard hconj)
  let f : Cover E (ProjectiveSpecialUnitaryMatrixGroup I) := {
    toMonoidHom := e.toMonoidHom.comp d.toMonoidHom
    surjective := e.surjective.comp d.surjective
    isPerfect := d.isPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact d.ker_le_center }
  obtain ⟨T, hT, ho, hi⟩ := exists_binary_normOne_torus_prime_index I rfl n hcard hconj hp hd
  have hf := f.not_dvd_kernel_of_permuted_torus (diagonalProjective I rfl T hT)
    (diagonalProjective_injective I rfl T hT ho) ho
    (exists_coordinate_swap I rfl T hT) (cycle I rfl) (cycle_cube I rfl)
    (cycle_diagonal I rfl T hT) hi
  change ¬ p ∣ Nat.card (e.toMonoidHom.comp d.toMonoidHom).ker at hf
  rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at hf

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
