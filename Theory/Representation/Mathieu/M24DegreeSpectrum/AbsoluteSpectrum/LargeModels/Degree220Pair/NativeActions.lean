module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Inputs
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Generators
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Native quotient and dual construction of the two degree-220 actions

A surjection from the actual fifth exterior power of the Golay code has a
kernel invariant under the two standard generators. These generate the full
Witt-design carrier, so the kernel is an actual subrepresentation. Transport
its quotient through the first isomorphism theorem to obtain the prescribed
220a matrices. Taking inverse transposes gives the contragredient action;
the checked change of coordinates then yields the prescribed 220b matrices.

`nativeRealizationsExist_of_exterior_and_certificates` separates the native
exterior coordinates from the seven finite matrix identities. The unconditional
`nativeRealizationsExist` discharges both inputs using their independent proofs,
producing the two marked native actions without an irreducibility premise.

Sources: James, J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1. The explicit
construction and conventions are recorded in `NativeActions/source/README.md`.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
open Sporadic.Mathieu
open NativeActions

/-- The literal quotient action realizes the 220a matrices. -/
theorem exists_first_of_exterior_and_certificates
    (C : ExteriorCoordinates) (h : MatrixCertificates) :
    ∃ ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2), Realizes false ρ := by
  let σ : Representation (ZMod 2) M24 (Fin 462 → ZMod 2) :=
    C.equiv.conjRingEquiv.toMonoidHom.comp exteriorRepresentation
  let P : (Fin 462 → ZMod 2) →ₗ[ZMod 2] (Fin 220 → ZMod 2) := Matrix.toLin' projection
  have hP : Function.Surjective P := by
    intro v
    refine ⟨Matrix.toLin' sectionMatrix v, ?_⟩
    change (Matrix.toLin' projection ∘ₗ Matrix.toLin' sectionMatrix) v = v
    rw [← Matrix.toLin'_mul, h.projection_section, Matrix.toLin'_one]
    rfl
  have hA : P.comp (σ generatorA) = (Matrix.toLin' (matrixA false)).comp P := by
    apply LinearMap.toMatrix'.injective
    simp only [LinearMap.toMatrix'_comp, P, LinearMap.toMatrix'_toLin']
    change projection * LinearMap.toMatrix' (C.equiv.conjRingEquiv (exteriorRepresentation generatorA)) = _
    rw [C.first, h.projection_A]
  have hB : P.comp (σ generatorB) = (Matrix.toLin' (matrixB false)).comp P := by
    apply LinearMap.toMatrix'.injective
    simp only [LinearMap.toMatrix'_comp, P, LinearMap.toMatrix'_toLin']
    change projection * LinearMap.toMatrix' (C.equiv.conjRingEquiv (exteriorRepresentation generatorB)) = _
    rw [C.second, h.projection_B]
  let K : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker P
      apply_mem_toSubmodule := by
        intro g
        apply Submonoid.induction_of_closure_eq_top_left
          (motive := fun g => ∀ v, v ∈ LinearMap.ker P → σ g v ∈ LinearMap.ker P)
          native_generators_monoid_closure g
        · intro v hv
          simpa only [map_one, Module.End.one_apply] using hv
        · rintro _ (rfl | rfl) y ih v hv
          · change P (σ (generatorA * y) v) = 0
            rw [map_mul, Module.End.mul_apply, ← LinearMap.comp_apply, hA, LinearMap.comp_apply]
            rw [show P (σ y v) = 0 from ih v hv, map_zero]
          · change P (σ (generatorB * y) v) = 0
            rw [map_mul, Module.End.mul_apply, ← LinearMap.comp_apply, hB, LinearMap.comp_apply]
            rw [show P (σ y v) = 0 from ih v hv, map_zero] }
  let e := P.quotKerEquivOfSurjective hP
  let ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2) :=
    e.conjRingEquiv.toMonoidHom.comp K.quotientRepresentation
  have hq (g : M24) (v : Fin 462 → ZMod 2) : ρ g (P v) = P (σ g v) := by
    change e (K.quotientRepresentation g (e.symm (P v))) = _
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    exact P.quotKerEquivOfSurjective_apply_mk hP (σ g v)
  refine ⟨ρ, ?_, ?_⟩
  · have he : ρ generatorA = Matrix.toLin' (matrixA false) := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := hP v
      rw [hq]
      exact congrArg (fun f => f w) hA
    rw [he, LinearMap.toMatrix'_toLin']
  · have he : ρ generatorB = Matrix.toLin' (matrixB false) := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := hP v
      rw [hq]
      exact congrArg (fun f => f w) hB
    rw [he, LinearMap.toMatrix'_toLin']

private theorem generatorA_inverse : generatorA⁻¹ = generatorA := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change m24GeneratorA * m24GeneratorA = 1
  rw [← pow_two, ← m24GeneratorA_order, pow_orderOf_eq_one]

private theorem generatorB_inverse : generatorB⁻¹ = generatorB ^ 2 := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change m24GeneratorB ^ 2 * m24GeneratorB = 1
  rw [← pow_succ]
  change m24GeneratorB ^ 3 = 1
  rw [← m24GeneratorB_order, pow_orderOf_eq_one]

/-- The contragredient in standard dual coordinates, conjugated by the checked matrix. -/
def conjugateDual (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2))
    (h : MatrixCertificates) : Representation (ZMod 2) M24 (Fin 220 → ZMod 2) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun g := dualChange * (LinearMap.toMatrix' (ρ g⁻¹)).transpose * dualChangeInverse
      map_one' := by simp [h.dual_left]
      map_mul' g k := by
        simp only [mul_inv_rev, map_mul, LinearMap.toMatrix'_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc dualChangeInverse dualChange,
          h.dual_right, Matrix.one_mul] }

/-- The checked dual comparison preserves both marked native generators. -/
theorem conjugateDual_realizes (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2))
    (hρ : Realizes false ρ) (h : MatrixCertificates) : Realizes true (conjugateDual ρ h) := by
  constructor
  · change LinearMap.toMatrix' (Matrix.toLin' _) = _
    rw [LinearMap.toMatrix'_toLin']
    change dualChange * (LinearMap.toMatrix' (ρ generatorA⁻¹)).transpose * dualChangeInverse = _
    rw [generatorA_inverse, hρ.1, h.dual_A,
      Matrix.mul_assoc, h.dual_left, Matrix.mul_one]
  · change LinearMap.toMatrix' (Matrix.toLin' _) = _
    rw [LinearMap.toMatrix'_toLin']
    change dualChange * (LinearMap.toMatrix' (ρ generatorB⁻¹)).transpose * dualChangeInverse = _
    rw [generatorB_inverse, map_pow]
    have hp : LinearMap.toMatrix' (ρ generatorB ^ 2) =
        LinearMap.toMatrix' (ρ generatorB) ^ 2 :=
      map_pow LinearMap.toMatrixAlgEquiv' (ρ generatorB) 2
    rw [hp, hρ.2, h.dual_B, Matrix.mul_assoc, h.dual_left, Matrix.mul_one]

/-- Actual application of both construction inputs to the published pair contract. -/
theorem nativeRealizationsExist_of_exterior_and_certificates
    (C : ExteriorCoordinates) (h : MatrixCertificates) : NativeRealizationsExist := by
  obtain ⟨ρ, hρ⟩ := exists_first_of_exterior_and_certificates C h
  refine ⟨fun second => if second then conjugateDual ρ h else ρ, ?_⟩
  intro second
  cases second
  · exact hρ
  · exact conjugateDual_realizes ρ hρ h

/-- Both literal ATLAS matrix pairs act on the full native Witt-design M24,
with the prescribed matrices at its two marked generators. -/
theorem nativeRealizationsExist : NativeRealizationsExist := by
  obtain ⟨C⟩ := nonempty_exteriorCoordinates
  exact nativeRealizationsExist_of_exterior_and_certificates C matrixCertificates

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
