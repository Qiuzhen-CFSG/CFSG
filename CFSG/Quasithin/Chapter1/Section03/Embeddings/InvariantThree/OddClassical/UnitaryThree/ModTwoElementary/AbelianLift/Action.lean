module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases

/-!
# Multiplicative lifts of projective unitary automorphisms

Every automorphism of the actual PSU₃ image over an odd prime-square field
has a multiplicative lift to SU₃. For the standard form, the lift applies the
field automorphism to matrix entries and conjugates by the unitary matrix
supplied by semilinear coverage. For an arbitrary Gram matrix, compatible
special and projective basis changes transport that lift.

Only inherited simplicity is used. No assertion about universal central
covers or their multipliers is needed. These lifts preserve the cube-one
subgroups used in the abelian branch of the order-nine sieve.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); Steinberg, Theorem 36, and GLS3,
Theorem 2.5.12 and §2.7, through the proved odd-prime semilinear coverage.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private theorem field_map_special
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (σ : E ≃+* E) (x : J.specialSubgroup) :
    GeneralLinearGroup.map σ.toRingHom x.val ∈ J.specialSubgroup := by
  have hform : J.form.map σ = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hadj : J.conjTranspose (x.val.val.map σ) = (J.conjTranspose x.val.val).map σ := by
    let := HermitianForm.finiteFieldAut_isCyclic (E := E)
    let := IsCyclic.commGroup (α := E ≃+* E)
    ext i j
    exact congrArg (fun f : E ≃+* E => f (x.val.val j i)) (Commute.all J.conj σ).eq
  refine ⟨?_, ?_⟩
  · change GeneralLinearGroup.map σ.toRingHom x.val ∈ J.unitarySubgroup
    rw [J.mem_unitarySubgroup_iff]
    change J.conjTranspose (x.val.val.map σ) * J.form * x.val.val.map σ = J.form
    rw [hadj, ← hform, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map σ)
      ((J.mem_unitarySubgroup_iff _).mp x.property.1)
  · change GeneralLinearGroup.det (GeneralLinearGroup.map σ.toRingHom x.val) = 1
    have hx : GeneralLinearGroup.det x.val = 1 := x.property.2
    rw [GeneralLinearGroup.map_det, hx, map_one]

private def specialSemilinear
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (σ : E ≃+* E) (u : J.unitarySubgroup) : J.specialSubgroup →* J.specialSubgroup where
  toFun x := J.specialUnitaryConj u
    ⟨GeneralLinearGroup.map σ.toRingHom x.val, field_map_special J hJ σ x⟩
  map_one' := by
    apply Subtype.ext
    rw [J.specialUnitaryConj_val]
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [J.specialUnitaryConj_val, map_mul, mul_assoc]

/-- The semilinear formula lifts through the actual SU₃ → PSU₃ map. -/
theorem standard_automorphism_lifts
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ f : J.specialSubgroup →* J.specialSubgroup,
      ∀ x, J.specialToProjective (f x) = a (J.specialToProjective x) := by
  obtain ⟨σ, u, hu⟩ := Coverage.semilinear_coverage_odd J hJ hp ho hcard hfixed a
  refine ⟨specialSemilinear J hJ σ u, fun x => Subtype.ext ?_⟩
  rw [hu, J.specialToProjective_apply_val, J.specialToProjective_apply_val,
    ProjGenLinGroup.map_mk]
  change ProjGenLinGroup.mk (J.specialUnitaryConj u _).val = _
  rw [J.specialUnitaryConj_val]
  simp only [map_mul, map_inv]

/-- A multiplicative lift for every Gram matrix with the specified Frobenius. -/
theorem automorphism_lifts
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ f : J.specialSubgroup →* J.specialSubgroup,
      ∀ x, J.specialToProjective (f x) = a (J.specialToProjective x) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J p hcard hfixed
  let es := FormTransport.specialEquiv J C hC
  let ep := FormTransport.projectiveEquiv J C hC
  have hcompat (x : J.specialSubgroup) :
      ep (J.specialToProjective x) = (FormTransport.standardForm J).specialToProjective (es x) := by
    apply Subtype.ext
    simp only [ep, es, FormTransport.projectiveEquiv_apply,
      HermitianForm.specialToProjective_apply_val, FormTransport.specialEquiv_apply,
      map_mul, map_inv]
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    ep.symm.isSimpleGroup
  obtain ⟨f, hf⟩ := standard_automorphism_lifts (FormTransport.standardForm J) rfl
    hp ho hcard hfixed (MulAut.congr ep a)
  refine ⟨(es.symm.toMonoidHom.comp f).comp es.toMonoidHom, fun x => ?_⟩
  apply ep.injective
  rw [hcompat]
  change (FormTransport.standardForm J).specialToProjective (es (es.symm (f (es x)))) = _
  rw [es.apply_symm_apply, hf, ← hcompat]
  simp [MulAut.congr_apply]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
