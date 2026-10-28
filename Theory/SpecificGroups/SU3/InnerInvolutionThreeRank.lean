module

public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.Standard
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Derived three-rank for inner involutions of PSU₃(p)

The centralizer calculation is transported from the standard concrete model
to every nondegenerate ternary Hermitian form over a field of order p²
with prime Frobenius conjugation. It bounds the first commutator subgroup
of each involution centralizer, without a simplicity hypothesis.

For the inner-automorphism formulation, inherited simplicity and a nontrivial
inner involution force the projective group to be centerless. Its inducing
element is therefore an involution, and its fixed subgroup is the actual
element centralizer. All odd primes, including three, are covered.

Source: Aschbacher–Smith E.6.18, printed p.252, Theorem C, printed p.33,
and A.3.21(a), printed p.55.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace Matrix.SU3.InnerThreeRank

/-- The derived centralizer rank bound for every allowed Hermitian matrix model. -/
theorem projective_involution_centralizer_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (k : ProjectiveSpecialUnitaryMatrixGroup J) (hk : orderOf k = 2) :
    primeRank 3 (commutator (centralizer ({k} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) ≤ 1 := by
  obtain ⟨e⟩ := exists_projective_equiv_standard p E J hcard hc
  let : Finite (GL (Fin 3) E) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero)) :=
    Finite.of_equiv _ e.toEquiv
  rw [primeRank_equiv 3 (commutatorEquiv (centralizerEquiv e k))]
  exact standard_projective_centralizer_rank p hp (e k) ((e.orderOf_eq k).trans hk)

private theorem orderOf_eq_two_of_inner_orderOf_eq_two
    {G : Type*} [Group G] [IsSimpleGroup G] (k : G)
    (hk : orderOf (MulAut.conj k) = 2) : orderOf k = 2 := by
  have hc : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hmem : k ∈ center G := by rw [hc]; trivial
      have hone : MulAut.conj k = 1 := by
        ext x
        change k * x * k⁻¹ = x
        rw [← mem_center_iff.mp hmem x, mul_inv_cancel_right]
      simp only [hone, orderOf_one] at hk
      omega
  exact (MulAut.conj_orderOf_of_center_eq_bot hc k).symm.trans hk

/-- The first commutator of every inner involution fixed group has three-rank at most one. -/
theorem inner_involution_derived_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (k : ProjectiveSpecialUnitaryMatrixGroup J) (hk : orderOf (MulAut.conj k) = 2) :
    primeRank 3 (commutator (MulAut.conj k).fixedSubgroup) ≤ 1 := by
  rw [MulAut.fixedSubgroup_conj]
  exact projective_involution_centralizer_rank p hp E J hcard hc k
    (orderOf_eq_two_of_inner_orderOf_eq_two k hk)

end Matrix.SU3.InnerThreeRank
