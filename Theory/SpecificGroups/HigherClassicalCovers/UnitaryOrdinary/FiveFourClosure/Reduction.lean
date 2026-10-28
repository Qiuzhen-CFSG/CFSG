module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Perfectness
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!+# Prime-degree local calculations for SU₅(4)

An orthonormal basis transports the actual special-unitary group to identity
Gram matrix without changing the kernel of a covering map. A prime divisor
of that kernel survives in a central quotient cover of prime degree. A section
of this quotient over a subgroup of index prime to that prime then contradicts
central transfer. Thus the defining and nondefining local calculations may be
carried out independently, only for prime-degree covers of the identity form.

The matrix field has sixteen elements and the involution is fourth power.
Projective quasisimplicity transports from the original model; no separate
simplicity certification is needed. The local-section premises below are still
obligations, not consequences of the scalar C₅ kernel calculation.

Source: Aschbacher--Smith I.1.1 and I.1.4(4), printed pp.407--408 of
`refs/quasithin.pdf`; GLS3 Section 6.1. The form change uses Huppert II.10.4.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory PerfectCentralCovering
open HermitianForm.IdentityGram

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure

universe u
variable {F : Type u} [Field F] [Finite F]

/-- The local calculation needed for a single prime. The subgroup and its
section use the literal covering homomorphism and may depend on the cover.
Only prime-degree covers are tested; arbitrary kernels are handled by quotienting.
-/
@[expose] def PrimeLocalSections (J : HermitianForm 5 F) (p : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (d : Cover E J.specialSubgroup),
    Nat.card d.toMonoidHom.ker = p →
      ∃ (P : Subgroup J.specialSubgroup) (s : P →* E),
        ¬ p ∣ P.index ∧ d.toMonoidHom.comp s = P.subtype

private theorem exists_orthonormal_basis (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    ∃ C : GL (Fin 5) F,
      J.conjTranspose C.val * J.form * C.val = (identityGram J).form := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 4 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
      (by decide) (by simpa using hcard) (by simpa using hconj)
  exact BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J 4 (by simpa using hcard) hf

/-- The source's projective quasisimplicity is inherited by the identity form.
This is transport of the given model hypothesis, not an independent simplicity
theorem for the matrix group.
-/
theorem identity_projective_isQuasisimple (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) := by
  obtain ⟨C, hC⟩ := exists_orthonormal_basis J hcard hconj
  let e := projectiveEquiv J C hC
  let d : Cover (ProjectiveSpecialUnitaryMatrixGroup (identityGram J))
      (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toMonoidHom := e.symm.toMonoidHom
      surjective := e.symm.surjective
      isPerfect := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      ker_le_center := by
        rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]
        exact bot_le }
  exact d.isQuasisimple

/-- An identity-form local calculation excludes the prime from every finite
perfect central cover of the original form, with no kernel-size restriction.
-/
theorem not_dvd_kernel_of_identity_prime_sections (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    {p : ℕ} [Fact p.Prime] (hsections : PrimeLocalSections (identityGram J) p)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨C, hC⟩ := exists_orthonormal_basis J hcard hconj
  let e := specialEquiv J C hC
  let d : Cover E (identityGram J).specialSubgroup :=
    { toMonoidHom := e.toMonoidHom.comp c.toMonoidHom
      surjective := e.surjective.comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact c.ker_le_center }
  have hd := d.not_dvd_card_kernel_of_prime_kernel_local_sections hsections
  have hk : d.toMonoidHom.ker = c.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  rwa [hk] at hd

/-- Combine the defining and odd-prime local calculations. Prime quotient
reduction controls all exponents and all mixed-order central kernels.
-/
theorem injective_of_identity_primary_sections (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (htwo : PrimeLocalSections (identityGram J) 2)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → PrimeLocalSections (identityGram J) p)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    Function.Injective c.toMonoidHom := by
  apply c.toMonoidHom.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    exact not_dvd_kernel_of_identity_prime_sections J hcard hconj htwo c
  · exact not_dvd_kernel_of_identity_prime_sections J hcard hconj (hodd p hp hp2) c

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
