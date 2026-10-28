module

public import Theory.AlgebraicGroup.RootSystems.F4RootLattice
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The integral Weyl action in fundamental F4 coordinates

The determinant-one F4 Cartan matrix identifies the integral root span with
all four fundamental coordinates. Restrict the actual real Weyl action to the
root span and transport it through this identification. The resulting action
is faithful, has the literal simple-reflection formula, and retains an
injective equivariant realization in the original real root space.

This is the common lattice interface for semisimple torus stabilizers and
fundamental-character invariants; it assumes no centralizer or conjugacy
classification. Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*,
§3, with the standard F4 Cartan calculation.
-/

open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
public noncomputable section
abbrev Weyl := typeF4RootPairing.weylGroup
abbrev Weight := Fin 4 → ℤ

private theorem span_stable (w : Weyl) (x : Vec 4) (hx : x ∈ (typeF4RootPairing.rootSpan ℤ)) : w • x ∈ (typeF4RootPairing.rootSpan ℤ) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, rfl⟩ := hy
    rw [typeF4RootPairing.weylGroup_apply_root]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem (typeF4RootPairing.rootSpan ℤ) ihx ihy
  | smul a x hx ih =>
    have he : w • (a • x) = a • (w • x) :=
      map_zsmul ((RootPairing.Equiv.weightHom typeF4RootPairing w.val).toAddMonoidHom) a x
    rw [he]
    exact Submodule.smul_mem (typeF4RootPairing.rootSpan ℤ) a ih

private def spanAction (w : Weyl) : (typeF4RootPairing.rootSpan ℤ) ≃ₗ[ℤ] (typeF4RootPairing.rootSpan ℤ) where
  toFun x := ⟨w • x.val, span_stable w x.val x.property⟩
  invFun x := ⟨w⁻¹ • x.val, span_stable w⁻¹ x.val x.property⟩
  left_inv x := Subtype.ext (inv_smul_smul w x.val)
  right_inv x := Subtype.ext (smul_inv_smul w x.val)
  map_add' x y := Subtype.ext (smul_add w x.val y.val)
  map_smul' a x := by
    apply Subtype.ext
    exact map_zsmul ((RootPairing.Equiv.weightHom typeF4RootPairing w.val).toAddMonoidHom) _ _

private def rootBasis : Module.Basis (Fin 4) ℤ (typeF4RootPairing.rootSpan ℤ) :=
  typeF4RootPairing_base.toWeightBasisInt.reindex typeF4RootPairing_baseEquiv.symm

private theorem rootBasis_apply (i : Fin 4) : rootBasis i = typeF4RootPairing.rootSpanMem ℤ (typeF4SimpleRootIndex i) := by
  apply Subtype.ext
  simp [rootBasis]

private def inverseCartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,3,4,2; 3,6,8,4; 2,4,6,3; 1,2,3,2]

private theorem inverseCartan_mul : inverseCartan * typeF4CartanMatrix = 1 := by
  decide +kernel

private theorem mul_inverseCartan : typeF4CartanMatrix * inverseCartan = 1 := by
  decide +kernel

private def cartanEquiv : Weight ≃ₗ[ℤ] Weight where
  __ := typeF4CartanMatrix.transpose.mulVecLin
  invFun := inverseCartan.transpose.mulVec
  left_inv x := by
    change inverseCartan.transpose.mulVec (typeF4CartanMatrix.transpose.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, mul_inverseCartan, Matrix.transpose_one,
      Matrix.one_mulVec]
  right_inv x := by
    change typeF4CartanMatrix.transpose.mulVec (inverseCartan.transpose.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, inverseCartan_mul, Matrix.transpose_one,
      Matrix.one_mulVec]

/-- Integral weights are their pairings with the four numbered simple coroots. -/
def coordinates : (typeF4RootPairing.rootSpan ℤ) →ₗ[ℤ] Weight :=
  LinearMap.pi (fun i => typeF4RootPairing.coroot'In ℤ (typeF4SimpleRootIndex i))

@[simp] theorem coordinates_root (r : typeF4Roots) (i : Fin 4) :
    coordinates (typeF4RootPairing.rootSpanMem ℤ r) i = typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :=
  typeF4RootPairing.coroot'In_rootSpanMem_eq_pairingIn (typeF4SimpleRootIndex i) r ℤ

private theorem coordinates_eq : coordinates =
    cartanEquiv.toLinearMap.comp rootBasis.equivFun.toLinearMap := by
  apply rootBasis.ext
  intro j
  ext i
  change coordinates (rootBasis j) i =
    typeF4CartanMatrix.transpose.mulVec (rootBasis.equivFun (rootBasis j)) i
  have hc : coordinates (rootBasis j) i = typeF4CartanMatrix j i := by
    rw [rootBasis_apply, coordinates_root]
    exact typeF4RootPairing_base_cartan_apply j i
  rw [hc]
  simp [Module.Basis.equivFun_self, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- F4's determinant-one Cartan matrix identifies its root lattice with all
fundamental coordinates, rather than a proper sublattice. -/
def coordinateEquiv : (typeF4RootPairing.rootSpan ℤ) ≃ₗ[ℤ] Weight := rootBasis.equivFun.trans cartanEquiv

@[simp] theorem coordinateEquiv_apply (x : (typeF4RootPairing.rootSpan ℤ)) : coordinateEquiv x = coordinates x := by
  rw [coordinates_eq]
  rfl

/-- The actual standard F4 Weyl representation on the full integral weight
lattice in numbered fundamental coordinates. -/
def representation : Weyl →* (Weight ≃ₗ[ℤ] Weight) where
  toFun w := coordinateEquiv.symm.trans ((spanAction w).trans coordinateEquiv)
  map_one' := by
    apply LinearEquiv.ext
    intro a
    change coordinateEquiv (spanAction 1 (coordinateEquiv.symm a)) = a
    have h : spanAction 1 (coordinateEquiv.symm a) = coordinateEquiv.symm a := by
      apply Subtype.ext
      exact one_smul _ _
    rw [h, coordinateEquiv.apply_symm_apply]
  map_mul' v w := by
    apply LinearEquiv.ext
    intro a
    change coordinateEquiv (spanAction (v*w) (coordinateEquiv.symm a)) =
      coordinateEquiv (spanAction v (coordinateEquiv.symm (coordinateEquiv (spanAction w (coordinateEquiv.symm a)))))
    rw [coordinateEquiv.symm_apply_apply]
    apply congrArg coordinateEquiv
    apply Subtype.ext
    exact mul_smul v w _

/-- The actual real weight-space realization of the integral coordinates. -/
def realization : Weight →ₗ[ℤ] Vec 4 := (typeF4RootPairing.rootSpan ℤ).subtype.comp coordinateEquiv.symm.toLinearMap

theorem realization_injective : Function.Injective realization :=
  Subtype.val_injective.comp coordinateEquiv.symm.injective

theorem realization_representation (w : Weyl) (a : Weight) :
    realization (representation w a) = w • realization a := by
  change (coordinateEquiv.symm (coordinateEquiv (spanAction w (coordinateEquiv.symm a)))).val = _
  rw [coordinateEquiv.symm_apply_apply]
  rfl

/-- The root weight vector used by the actual F4 characters. -/
@[expose] def rootWeight (r : typeF4Roots) : Weight := fun i => typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)

/-- Integral Weyl action preserves the actual root labels. -/
theorem representation_root (w : Weyl) (r : typeF4Roots) :
    representation w (rootWeight r) = rootWeight (typeF4RootPairing.weylGroupToPerm w r) := by
  have hr : rootWeight r = coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r) := by
    ext i
    simp [rootWeight]
  rw [hr]
  change coordinateEquiv (spanAction w (coordinateEquiv.symm (coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r)))) = _
  rw [coordinateEquiv.symm_apply_apply]
  have h : spanAction w (typeF4RootPairing.rootSpanMem ℤ r) = typeF4RootPairing.rootSpanMem ℤ (typeF4RootPairing.weylGroupToPerm w r) := by
    apply Subtype.ext
    exact typeF4RootPairing.weylGroup_apply_root w r
  rw [h]
  ext i
  simp [rootWeight]

/-- The numbered simple reflection has the original Cartan formula on every
integral weight, with no torus-action or connectedness premise. -/
theorem representation_simple (i : Fin 4) (a : Weight) :
    representation (RootPairing.weylGroup.ofIdx typeF4RootPairing (typeF4SimpleRootIndex i)) a =
      a - a i • rootWeight (typeF4SimpleRootIndex i) := by
  let x := coordinateEquiv.symm a
  have hx : coordinates x = a := by
    rw [← coordinateEquiv_apply, coordinateEquiv.apply_symm_apply]
  have hs : spanAction (RootPairing.weylGroup.ofIdx typeF4RootPairing (typeF4SimpleRootIndex i)) x =
      x - coordinates x i • typeF4RootPairing.rootSpanMem ℤ (typeF4SimpleRootIndex i) := by
    apply Subtype.ext
    change typeF4RootPairing.reflection (typeF4SimpleRootIndex i) x.val =
      x.val - coordinates x i • typeF4RootPairing.root (typeF4SimpleRootIndex i)
    rw [typeF4RootPairing.reflection_apply]
    congr 1
    have hi := typeF4RootPairing.algebraMap_coroot'In_apply ℤ (typeF4SimpleRootIndex i) x
    change algebraMap ℤ ℝ (coordinates x i) = _ at hi
    rw [← hi]
    exact (Int.cast_smul_eq_zsmul ℝ _ _)
  change coordinateEquiv (spanAction (RootPairing.weylGroup.ofIdx typeF4RootPairing (typeF4SimpleRootIndex i)) x) = _
  rw [hs, map_sub, map_smul, coordinateEquiv.apply_symm_apply, hx]
  congr 2
  ext j
  simp [rootWeight]

@[simp] theorem rootWeight_simple (i j : Fin 4) :
    rootWeight (typeF4SimpleRootIndex i) j = typeF4CartanMatrix i j :=
  typeF4RootPairing_base_cartan_apply i j

@[simp] theorem realization_root (r : typeF4Roots) :
    realization (rootWeight r) = typeF4RootPairing.root r := by
  have hr : rootWeight r = coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r) := by
    ext i
    simp [rootWeight]
  rw [hr]
  change (coordinateEquiv.symm (coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r))).val = _
  rw [coordinateEquiv.symm_apply_apply]

theorem realization_coroot (a : Weight) (i : Fin 4) :
    typeF4RootPairing.toLinearMap (realization a) (typeF4RootPairing.coroot (typeF4SimpleRootIndex i)) = (a i : ℝ) := by
  have h := typeF4RootPairing.algebraMap_coroot'In_apply ℤ (typeF4SimpleRootIndex i)
    (coordinateEquiv.symm a)
  have hc : coordinates (coordinateEquiv.symm a) = a := by
    rw [← coordinateEquiv_apply, coordinateEquiv.apply_symm_apply]
  change algebraMap ℤ ℝ (coordinates (coordinateEquiv.symm a) i) = _ at h
  rw [hc] at h
  exact h.symm

theorem representation_injective : Function.Injective representation := by
  intro v w h
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective typeF4RootPairing
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro r
  simp only [RootPairing.Base.toWeightBasis_apply]
  have he := congrArg (fun f : Weight ≃ₗ[ℤ] Weight => realization (f (rootWeight r))) h
  change v • typeF4RootPairing.root r = w • typeF4RootPairing.root r
  simpa only [realization_representation, realization_root] using he

end
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
