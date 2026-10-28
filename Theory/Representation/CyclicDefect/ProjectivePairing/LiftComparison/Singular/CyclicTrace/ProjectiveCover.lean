module

public import Theory.Representation.IntegralSpectralTrace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Integral singular traces from finite projective covers

A finite projective group-algebra module splits off a finite free cover. In the
standard coefficient basis of that cover, every nonidentity group element acts
without fixed basis vectors. The splitting idempotent commutes with the action.
For commuting prime-power and prime-to-prime parts, the integral Fourier
projectors and permutation-summand trace theorem in `IntegralSpectralTrace`
therefore give trace zero on the projected cover. Cyclic invariance of the
rectangular trace transports this exact value to the original module.

This proves the vanishing clause of Feit, *The Representation Theory of Finite
Groups*, IV.2.5 (printed p.144), in the split integral setting used in IV.3.3.
The residue-field map in this reusable statement must be surjective and detect
units. The actual integral lift supplies these conditions through its canonical
residue field in the importing `CyclicTrace` module.
-/

public section

open Module
open scoped Classical
noncomputable section
namespace Representation.CyclicDefect.ProjectivePairing.Singular.CyclicTrace
variable {R G : Type*} [CommRing R] [Group G]

private def coverPerm (n : ℕ) : G →* Equiv.Perm (Σ _ : Fin n, G) where
  toFun g := Equiv.sigmaCongrRight (fun _ => Equiv.mulLeft g)
  map_one' := by
    apply _root_.Equiv.ext
    rintro ⟨i, x⟩
    change (⟨i, 1 * x⟩ : Σ _ : Fin n, G) = ⟨i, x⟩
    rw [one_mul]
  map_mul' g h := by
    apply _root_.Equiv.ext
    rintro ⟨i, x⟩
    change (⟨i, (g * h) * x⟩ : Σ _ : Fin n, G) = ⟨i, g * (h * x)⟩
    rw [mul_assoc]

private def coverRep (n : ℕ) : Representation R G (Fin n → MonoidAlgebra R G) :=
  (Algebra.lsmul R R (Fin n → MonoidAlgebra R G)).toMonoidHom.comp
    (MonoidAlgebra.of R G)

private def coverBasis (n : ℕ) : Basis (Σ _ : Fin n, G) R (Fin n → MonoidAlgebra R G) :=
  Pi.basis (fun _ => MonoidAlgebra.basis G R)

private theorem coverRep_basis (n : ℕ) (g : G) (j : Σ _ : Fin n, G) :
    coverRep (R := R) n g (coverBasis n j) = coverBasis n (coverPerm n g j) := by
  classical
  rw [show coverPerm n g j = ⟨j.1, g * j.2⟩ from rfl]
  ext1 i
  change ((MonoidAlgebra.of R G g) * coverBasis n j i) = _
  simp only [coverBasis, Pi.basis_apply, MonoidAlgebra.basis_apply]
  by_cases hij : i = j.1
  · subst i
    simp [MonoidAlgebra.of_apply]
  · simp [Pi.single_eq_of_ne hij]

variable [Fintype G]

private theorem coverRep_matrix (n : ℕ) (g : G) :
    LinearMap.toMatrix (coverBasis n) (coverBasis n) (coverRep (R := R) n g) =
      (coverPerm n g⁻¹).permMatrix R := by
  classical
  ext i j
  simp only [LinearMap.toMatrix_apply, coverRep_basis, Basis.repr_self,
    Finsupp.single_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  apply propext
  rw [map_inv, _root_.Equiv.Perm.inv_def, _root_.Equiv.symm_apply_eq, eq_comm]


private theorem trace_cover_projector {k : Type*} [Field k] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (n : ℕ) (E : Module.End (MonoidAlgebra R G) (Fin n → MonoidAlgebra R G))
    (hE : IsIdempotentElem E) (t v : G) (ht : t ≠ 1)
    {a : ℕ} (hta : t ^ (p ^ a) = 1) (htv : Commute t v)
    {m : ℕ} (hm : m ≠ 0) (hvm : v ^ m = 1)
    (hmunit : IsUnit (m : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ m) :
    LinearMap.trace R _ (coverRep n (t * v) * E.restrictScalars R) = 0 := by
  classical
  let b := coverBasis (R := R) (G := G) n
  let L : G →* Matrix (Σ _ : Fin n, G) (Σ _ : Fin n, G) R :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (coverRep n)
  let P := LinearMap.toMatrix b b (E.restrictScalars R)
  let σ := coverPerm n t⁻¹
  have hσ : σ ^ (p ^ a) = 1 := by
    dsimp [σ]
    rw [← map_pow, inv_pow, hta, inv_one, map_one]
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    have hx' : t⁻¹ * x.2 = x.2 := congrArg Sigma.snd hx
    exact ht (inv_eq_one.mp (mul_right_cancel (b := x.2) (by simpa using hx')))
  have hmatrix (x : G) : (coverPerm n x⁻¹).permMatrix R = L x :=
    (coverRep_matrix n x).symm
  have hP : IsIdempotentElem P := by
    have hE' : IsIdempotentElem (E.restrictScalars R) := by
      change (E.restrictScalars R).comp (E.restrictScalars R) = E.restrictScalars R
      rw [← LinearMap.restrictScalars_comp, show E.comp E = E from hE]
    exact hE'.map (LinearMap.toMatrixAlgEquiv b)
  have hLP (x : G) : Commute (L x) P := by
    have hc : Commute (coverRep (R := R) n x) (E.restrictScalars R) := by
      apply LinearMap.ext
      intro w
      exact (E.map_smul (MonoidAlgebra.of R G x) w).symm
    exact hc.map (LinearMap.toMatrixAlgEquiv b)
  have hvpow : L v ^ m = 1 := by rw [← map_pow, hvm, map_one]
  have hz := Matrix.trace_permMatrix_mul_mul_eq_zero_of_prime
    f hsurj hf σ hσ hfix (L v) P hP
    (by simpa only [σ, hmatrix] using hLP t) (hLP v)
    (by simpa only [σ, hmatrix] using htv.map L)
    hm hvpow hmunit ζ hζ
  rw [show σ.permMatrix R = L t from hmatrix t, ← map_mul] at hz
  rw [LinearMap.trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
  exact hz

/-- A finite projective representation has zero integral trace on the product
of a nonidentity prime-power element and a commuting split unit-order element. -/
theorem trace_mul_eq_zero_of_projective {k V : Type*} [Field k] [IsDomain R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (ρ : Representation R G V) [Module.Projective (MonoidAlgebra R G) ρ.asModule]
    (t v : G) (ht : t ≠ 1) {a : ℕ} (hta : t ^ (p ^ a) = 1) (htv : Commute t v)
    {m : ℕ} (hm : m ≠ 0) (hvm : v ^ m = 1)
    (hmunit : IsUnit (m : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ m) :
    LinearMap.trace R V (ρ (t * v)) = 0 := by
  let : Module.Finite (MonoidAlgebra R G) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨n, q, i, _, _, hqi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra R G) ρ.asModule
  let E := i.comp q
  have hE : IsIdempotentElem E := by
    change (i.comp q).comp (i.comp q) = i.comp q
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc q i q, hqi,
      LinearMap.id_comp]
  have hz := trace_cover_projector f hsurj hf n E hE t v ht hta htv
    hm hvm hmunit ζ hζ
  let i' : V →ₗ[R] (Fin n → MonoidAlgebra R G) :=
    (i.restrictScalars R).comp ρ.asModuleEquiv.symm.toLinearMap
  let q' : (Fin n → MonoidAlgebra R G) →ₗ[R] V :=
    ρ.asModuleEquiv.toLinearMap.comp (q.restrictScalars R)
  have hqi' : q'.comp i' = LinearMap.id := by
    apply LinearMap.ext
    intro w
    change ρ.asModuleEquiv (q (i (ρ.asModuleEquiv.symm w))) = w
    rw [← LinearMap.comp_apply, hqi, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  have heq : coverRep n (t * v) * E.restrictScalars R = i'.comp ((ρ (t * v)).comp q') := by
    apply LinearMap.ext
    intro w
    change MonoidAlgebra.of R G (t * v) • i (q w) =
      i (ρ.asModuleEquiv.symm (ρ (t * v) (ρ.asModuleEquiv (q w))))
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply,
      i.map_smul]
  rw [heq, LinearMap.trace_comp_comm' ((ρ (t * v)).comp q') i',
    LinearMap.comp_assoc, hqi', LinearMap.comp_id] at hz
  exact hz

end Representation.CyclicDefect.ProjectivePairing.Singular.CyclicTrace
