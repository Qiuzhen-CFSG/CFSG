module

public import Theory.Alternating.FiveCubeKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugacy

/-!
# No binary PSL₃ perfect subgroup in a PSU₃ involution centralizer

For the standard form, lift an involution to SU₃ through the scalar kernel
of exponent three. Its full centralizer is GU₂, embedded in GL₂, so the
cubic-kernel involution obstruction excludes a perfect A₅ subgroup in
the actual projective centralizer. Transport through an orthonormal basis
and the coefficient-field isomorphism gives the result for every
nondegenerate Hermitian form with prime Frobenius conjugation.

All odd primes, including three, are covered. There are no rank or
centralizer-shape premises. Source: Aschbacher--Smith, proof of 15.3.38,
p.1137; Theorem C, p.33; A.3.21(a), p.55.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Matrix.SU3.InnerComponentExclusion

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

variable {K : Type*} [Group K] [Group.IsPerfect K]
/-- The exclusion for the actual standard PSU₃(p) carrier. -/
theorem standard_no_perfect_alternating_five_in_centralizer (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (t : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))))
    (hj : Function.Injective j) (e : K ≃* alternatingGroup (Fin 5)) : False := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube t ht
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  have hker : ∀ g ∈ f.ker, g ^ 3 = 1 := by
    intro g hg
    apply Subtype.ext
    apply hcube
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
  have hp2 : p ≠ 2 := by
    have := Nat.odd_iff.mp hp
    omega
  let ec : C ≃* J2.unitarySubgroup :=
    (SU3.involutionCentralizerEquiv hp2 (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  let ρ := J2.unitarySubgroup.subtype.comp ec.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp ec.injective
  exact AlternatingFive.CubeKernel.no_perfect_alternating_five
    (CharP.cast_ne_zero_of_ne_of_prime (GaloisField p (2 * 1)) Nat.prime_two hp2)
    f hf hker ρ hρ j hj e

/-- The exclusion for every allowed nondegenerate ternary Hermitian form. -/
theorem no_perfect_alternating_five_in_centralizer (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hj : Function.Injective j) (e : K ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨a⟩ := SU3.InnerThreeRank.exists_projective_equiv_standard p E J hcard hc
  let c := SU3.InnerThreeRank.centralizerEquiv a t
  exact standard_no_perfect_alternating_five_in_centralizer p hp (a t) ((a.orderOf_eq t).trans ht)
    (c.toMonoidHom.comp j) (c.injective.comp hj) e
end Matrix.SU3.InnerComponentExclusion
