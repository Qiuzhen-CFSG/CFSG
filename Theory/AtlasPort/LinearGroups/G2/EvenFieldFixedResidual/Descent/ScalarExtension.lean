module

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.AtlasPort.Algebra.SplitOctonion.BasisChecks
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Scalar extension of the split-octonion automorphism model

For a subfield K of F, include the eight coordinates and extend a K-linear
map by its standard-basis images. Extension respects composition and the
identity, hence carries linear equivalences to linear equivalences. The
integral split-octonion table commutes with inclusion; bilinearity then
proves that extension preserves octonion multiplication.

This supplies the inverse map for coefficient descent in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(4), printed p.1171.
The multiplication table and basis criterion are from the imported licensed
ATLAS port. No associativity of octonion multiplication is assumed.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.EvenFieldFixedResidual.Descent
variable {F : Type*} [Field F] (K : Subfield F)

/-- Coordinate inclusion through the actual subfield embedding. -/
def includeCoefficients : Carrier K →ₗ[K] Carrier F where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem includeCoefficients_apply (x : Carrier K) (i : Fin 8) :
    includeCoefficients K x i = (x i : F) := rfl

theorem includeCoefficients_injective : Function.Injective (includeCoefficients K) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

@[simp] theorem includeCoefficients_basis (i : Fin 8) :
    includeCoefficients K (basisVector i) = basisVector i := by
  ext j
  by_cases h : j = i <;> simp [basisVector, h]

@[simp] theorem includeCoefficients_mul (x y : Carrier K) :
    includeCoefficients K (mul x y) = mul (includeCoefficients K x) (includeCoefficients K y) := by
  ext i
  fin_cases i <;> rfl

/-- Extend a linear map by its eight standard-basis images. -/
noncomputable def extendLinear (g : Carrier K →ₗ[K] Carrier K) : Carrier F →ₗ[F] Carrier F :=
  (Pi.basisFun F (Fin 8)).constr F (fun i => includeCoefficients K (g (basisVector i)))

@[simp] theorem extendLinear_basis (g : Carrier K →ₗ[K] Carrier K) (i : Fin 8) :
    extendLinear K g (basisVector i) = includeCoefficients K (g (basisVector i)) := by
  simpa only [extendLinear, Pi.basisFun_apply, basisVector] using
    (Pi.basisFun F (Fin 8)).constr_basis F
      (fun j => includeCoefficients K (g (basisVector j))) i

@[simp] theorem extendLinear_include (g : Carrier K →ₗ[K] Carrier K) (x : Carrier K) :
    extendLinear K g (includeCoefficients K x) = includeCoefficients K (g x) := by
  have h : ((extendLinear K g).restrictScalars K).comp (includeCoefficients K) =
      (includeCoefficients K).comp g := by
    apply (Pi.basisFun K (Fin 8)).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Pi.basisFun_apply]
    change extendLinear K g (includeCoefficients K (basisVector i)) = _
    rw [includeCoefficients_basis, extendLinear_basis]
    rfl
  exact LinearMap.congr_fun h x

@[simp] theorem extendLinear_id : extendLinear K LinearMap.id = LinearMap.id := by
  apply linearMap_ext
  intro i
  simp

@[simp] theorem extendLinear_comp (g h : Carrier K →ₗ[K] Carrier K) :
    extendLinear K (g.comp h) = (extendLinear K g).comp (extendLinear K h) := by
  apply linearMap_ext
  intro i
  simp

/-- Extending a map and its inverse gives an actual linear equivalence. -/
noncomputable def extendEquiv (g : Carrier K ≃ₗ[K] Carrier K) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := extendLinear K g.toLinearMap
  invFun := extendLinear K g.symm.toLinearMap
  left_inv x := by
    have h := extendLinear_comp K g.symm.toLinearMap g.toLinearMap
    rw [g.symm_comp, extendLinear_id] at h
    exact (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := extendLinear_comp K g.toLinearMap g.symm.toLinearMap
    rw [g.comp_symm, extendLinear_id] at h
    exact (LinearMap.congr_fun h x).symm

/-- Scalar extension in the full multiplication-preserving automorphism model. -/
noncomputable def extendAutomorphism (g : Model K) : Model F :=
  ⟨extendEquiv K g.val, by
    apply map_mul_of_basis
    intro i j
    change extendLinear K g.val.toLinearMap (mul (basisVector i) (basisVector j)) = _
    rw [← includeCoefficients_basis K i, ← includeCoefficients_basis K j,
      ← includeCoefficients_mul, extendLinear_include]
    change includeCoefficients K (g.val (mul (basisVector i) (basisVector j))) = _
    rw [automorphism_mul, includeCoefficients_mul]
    congr 1 <;> exact (extendLinear_include K _ _).symm⟩

end Atlas.G2.EvenFieldFixedResidual.Descent
