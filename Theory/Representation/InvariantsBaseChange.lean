module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Theory.Representation.ScalarDescent

/-!
# Modular Invariants and Scalar Extension

For a finite acting group, taking invariant vectors commutes with arbitrary
extension of the coefficient field, including in defining characteristic.
In particular the dimension of invariants is preserved by scalar extension.

Realize invariants as the kernel of the finite family of equations
rho(g)v - v = 0. Tensoring identifies the target with functions to the extended
space because the group is finite, and flat base change preserves the kernel.
The corresponding subtype equivalence and tensor-product finrank formula give
the dimension statement; no averaging or invertibility of the group order is
used.

These results justify descent of fixed-space dimensions in
Alperin--Brauer--Gorenstein II.4, Lemma 18(ii), article pp. 45--46. They were
originally proved in SL2/FaithfulDimension and are reexported there unchanged.
-/

open scoped TensorProduct

namespace Representation

private def fixedDifference
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) : V →ₗ[F] (G → V) where
  toFun := fun v g => rho g v - v
  map_add' := by
    intro v w
    ext g
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' := by
    intro a v
    ext g
    simp [smul_sub]

private theorem fixedDifference_ker
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) :
    (fixedDifference rho).ker = rho.invariants := by
  ext v
  simp only [LinearMap.mem_ker, mem_invariants]
  constructor
  · intro hv g
    have hvg := congrFun hv g
    exact sub_eq_zero.mp hvg
  · intro hv
    ext g
    exact sub_eq_zero.mpr (hv g)

private theorem fixedDifference_baseChange
    {F E G V : Type*} [Field F] [Field E] [Algebra F E]
    [Group G] [Fintype G] [DecidableEq G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) :
    (TensorProduct.piRight F E E (fun _ : G => V)).toLinearMap.comp
        ((fixedDifference rho).baseChange E) =
      fixedDifference (extendScalars E rho) := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero =>
      ext g
      simp [fixedDifference]
  | tmul a v =>
      ext g
      simp [fixedDifference, extendScalars_apply, TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- For a finite group, invariant subspaces commute with arbitrary field
extension, including in modular characteristic. -/
public theorem invariants_extendScalars_eq_baseChange_of_finite
    {F E G V : Type*} [Field F] [Field E] [Algebra F E]
    [Group G] [Finite G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) :
    (extendScalars E rho).invariants = rho.invariants.baseChange E := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [← fixedDifference_ker, ← fixedDifference_ker]
  rw [← fixedDifference_baseChange rho]
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  exact (LinearMap.baseChange_ker_eq (fixedDifference rho)).symm

/-- The dimension of the invariant subspace is unchanged by field extension
for a finite acting group, including in modular characteristic. -/
public theorem finrank_invariants_extendScalars_eq_of_finite
    {F E G V : Type*} [Field F] [Field E] [Algebra F E]
    [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (rho : Representation F G V) :
    Module.finrank E (extendScalars E rho).invariants =
      Module.finrank F rho.invariants := by
  rw [invariants_extendScalars_eq_baseChange_of_finite]
  let f := Submodule.toBaseChange E rho.invariants
  have hf_injective : Function.Injective f := by
    intro x y hxy
    have hcoe := congrArg Subtype.val hxy
    change rho.invariants.subtype.baseChange E x =
      rho.invariants.subtype.baseChange E y at hcoe
    have hsubtype : Function.Injective rho.invariants.subtype :=
      fun u v huv => Subtype.ext huv
    apply Module.Flat.lTensor_preserves_injective_linearMap
      rho.invariants.subtype hsubtype
    simpa only [LinearMap.baseChange_eq_ltensor] using hcoe
  let e : E ⊗[F] rho.invariants ≃ₗ[E] rho.invariants.baseChange E :=
    LinearEquiv.ofBijective f
      ⟨hf_injective, Submodule.toBaseChange_surjective E rho.invariants⟩
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange (R := E) (S := F)
    (M' := rho.invariants)

end Representation
