module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.Setup
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization

/-!
# Semilinear coverage in the original identity Gram basis

Apply the checked odd-prime automorphism theorem in an antidiagonal basis
and transport its actual PGL formula back. If `C` is the basis change and
`u` its unitary representative, the transported matrix is `C * u * σ(C)⁻¹`.
Mapping the basis identity by `σ` proves that this matrix is unitary for
the original form. Prime Frobenius commutes with every field automorphism,
and the quadratic field has only the identity and Hermitian conjugation.

This supplies the coverage input for the pointwise standard-four fixer in
Aschbacher--Smith E.1.14(7), printed p.214. The automorphism theorem is
Steinberg, Theorem 36, and GLS3, Theorem 2.5.12 and §2.7; basis transport
uses Huppert II.10.4 and the formulas in `NormalizedOuter.FormTransport`.
No diagonal placement or simultaneous conjugator is asserted here.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer
variable {F : Type*} [Field F]

private theorem adjoint_mul (J : HermitianForm 3 F)
    (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private def adjointUnit (J : HermitianForm 3 F) (C : GL (Fin 3) F) : GL (Fin 3) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by
    rw [← adjoint_mul, Units.inv_mul]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one, transpose_one]
  inv_val := by
    rw [← adjoint_mul, Units.mul_inv]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one, transpose_one]

private theorem transport_unitary (J : HermitianForm 3 F)
    (C D : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (FormTransport.standardForm J).form)
    (hD : J.conjTranspose D.val * J.form * D.val = (FormTransport.standardForm J).form)
    (u : (FormTransport.standardForm J).unitarySubgroup) :
    C * u.val * D⁻¹ ∈ J.unitarySubgroup := by
  have hu := ((FormTransport.standardForm J).mem_unitarySubgroup_iff _).mp u.property
  change J.conjTranspose u.val.val * (FormTransport.standardForm J).form *
    u.val.val = (FormTransport.standardForm J).form at hu
  rw [J.mem_unitarySubgroup_iff]
  simp only [Units.val_mul, adjoint_mul]
  calc
    _ = J.conjTranspose (D⁻¹).val *
        (J.conjTranspose u.val.val *
          (J.conjTranspose C.val * J.form * C.val) * u.val.val) * (D⁻¹).val := by
      simp only [mul_assoc]
    _ = J.conjTranspose (D⁻¹).val * (FormTransport.standardForm J).form * (D⁻¹).val := by
      rw [hC, hu]
    _ = J.form := by
      rw [← hD]
      change (adjointUnit J D)⁻¹.val *
        ((adjointUnit J D).val * J.form * D.val) * (D⁻¹).val = J.form
      simp only [← mul_assoc, Units.inv_mul, one_mul, Units.mul_inv_cancel_right]

private theorem transport_semilinear (J : HermitianForm 3 F) (hJ : J.form = 1)
    (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (FormTransport.standardForm J).form)
    (σ : F ≃+* F) (hσ : ∀ x, J.conj (σ x) = σ (J.conj x))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : (FormTransport.standardForm J).HasUnitarySemilinearForm
      (MulAut.congr (FormTransport.projectiveEquiv J C hC) a) σ) :
    J.HasUnitarySemilinearForm a σ := by
  let D := GeneralLinearGroup.map σ.toRingHom C
  have hD : J.conjTranspose D.val * J.form * D.val = (FormTransport.standardForm J).form := by
    have hadj : J.conjTranspose D.val = (J.conjTranspose C.val).map σ := by
      ext i j
      exact hσ _
    have hform : J.form.map σ = J.form := by simp [hJ]
    have hstandard : (FormTransport.standardForm J).form.map σ =
        (FormTransport.standardForm J).form := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [FormTransport.standardForm]
    rw [hadj, ← hform]
    change (J.conjTranspose C.val).map σ * J.form.map σ * C.val.map σ = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hC, hstandard]
  obtain ⟨u, hu⟩ := ha
  refine ⟨⟨C * u.val * D⁻¹, transport_unitary J C D hC hD u⟩, ?_⟩
  intro x
  let e := FormTransport.projectiveEquiv J C hC
  have h := hu (e x)
  change (e (a (e.symm (e x)))).val = _ at h
  rw [e.symm_apply_apply, FormTransport.projectiveEquiv_apply,
    FormTransport.projectiveEquiv_apply] at h
  have h' := congrArg (fun z => ProjGenLinGroup.mk C * z * (ProjGenLinGroup.mk C)⁻¹) h
  simpa [D, map_mul, map_inv, mul_assoc] using h'

/-- Every automorphism has a concrete unitary formula in the identity Gram basis,
with field part identity or the stored prime Frobenius. -/
theorem identityGram_semilinear_coverage [Finite F] (J : HermitianForm 3 F) (hJ : J.form = 1)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ σ : F ≃+* F, (σ = 1 ∨ σ = J.conj) ∧ J.HasUnitarySemilinearForm a σ := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed := J.card_fixed_of_prime_frobenius hc
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J p hcard hfixed
  let e := FormTransport.projectiveEquiv J C hC
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  obtain ⟨σ, hσ⟩ := Coverage.semilinear_coverage_odd (FormTransport.standardForm J) rfl
    hp ho hcard hfixed (MulAut.congr e a)
  refine ⟨σ, fieldAut_eq_one_or_conj J hp hcard hfixed σ, ?_⟩
  apply transport_semilinear J hJ C hC σ _ a hσ
  intro x
  simp only [hc, map_pow]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer
