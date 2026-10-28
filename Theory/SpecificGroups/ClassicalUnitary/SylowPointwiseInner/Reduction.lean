module

public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.GroupAction.SylowPointwiseInnerTransport

/-!
# Binary PSU form transport and the dimension-two Sylow fixer

Orthonormalization identifies the literal projective special-unitary image
with the identity-Gram model in every dimension. The conditional higher-rank
reduction separates concrete semilinear coverage from its Sylow-fixer matrix
calculation. Neither premise is asserted here.

In dimension two, the genuine comparison with PSL₂ of the fixed field supplies
both the automorphism calculation and a conjugating element in the given Sylow.
The coefficient field has order (2^f)²; its fixed field has order 2^f.

Sources: Huppert II.10.4; GLS3, §2.7; Aschbacher–Smith, the characteristic-two
Sylow-centralizer step of B.1.13, printed pp.73–74.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
namespace Theory.SpecificGroups.ClassicalUnitary.SylowPointwiseInner
variable {F : Type*} [Field F] [Finite F]

private theorem finite_projective {d : ℕ} (J : HermitianForm d F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let p : J.specialSubgroup → ProjectiveSpecialUnitaryMatrixGroup J :=
    fun A => ⟨ProjGenLinGroup.mk A.val, ⟨A.val, A.property, rfl⟩⟩
  apply Finite.of_surjective p
  rintro ⟨x, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

/-- The actual projective matrix formula, with a unitary representative and
an entrywise field automorphism. Coverage is only requested on identity Gram. -/
@[expose] def HasSemilinearForm {d : ℕ} (J : HermitianForm d F)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : F ≃+* F) : Prop :=
  ∃ u : J.unitarySubgroup, ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
    (a x).val = ProjGenLinGroup.mk u.val *
      ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹

/-- The standard-form calculation suffices for every nondegenerate Hermitian form. -/
theorem fixing_sylow_of_identity_gram {d f : ℕ} (J : HermitianForm d F)
    (hf : 0 < f) (hcard : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ f))
    (hstandard : ∀ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)))
      (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (identityGram J))),
      (∀ x ∈ S, a x = x) → ∃ x ∈ S, a = MulAut.conj x)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨C, hC⟩ := UnitaryRootNormalizer.exists_binary_identity_basis J hf hcard hconj
  exact MulAut.fixing_sylow_inner_of_equiv (projectiveEquiv J C hC) hstandard S a hfix

/-- Conditional assembly of the independent coverage and matrix calculations.
Both hypotheses still require producers before this yields the higher-rank theorem. -/
theorem fixing_sylow_of_semilinear_calculation {d f : ℕ} (J : HermitianForm d F)
    (hf : 0 < f) (hcard : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ f))
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      ∃ σ : F ≃+* F, HasSemilinearForm (identityGram J) a σ)
    (hcalculation : ∀ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)))
      (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (identityGram J))) (σ : F ≃+* F),
      HasSemilinearForm (identityGram J) a σ →
      (∀ x ∈ S, a x = x) → ∃ x ∈ S, a = MulAut.conj x)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  apply fixing_sylow_of_identity_gram J hf hcard hconj _ S a hfix
  intro P b hb
  obtain ⟨σ, hσ⟩ := hcoverage b
  exact hcalculation P b σ hσ hb

/-- PSU₂ uses the actual PSL₂ comparison over the fixed subfield; no restriction
on the actor order or on the Hermitian Gram matrix is imposed. -/
theorem fixing_sylow_two (J : HermitianForm 2 F) {f : ℕ}
    (hf : 0 < f) (hcard : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ f))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  let : CharP F 2 := UnitaryRootNormalizer.charP_binary hf hcard
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨e⟩ := UnitaryRootNormalizer.nonempty_projectiveTwoEquiv J hcard
    (UnitaryRootNormalizer.fixed_card_binary J hf hcard hconj)
  exact MulAut.fixing_sylow_inner_of_equiv e Theory.PSL2.aut_fixing_sylow_inner S a hfix

end Theory.SpecificGroups.ClassicalUnitary.SylowPointwiseInner
