module

public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.Coordinates

/-!
# Projective curves in a different basis

Changing from a torus weight basis to the basis of the original Chevalley model
is an actual projective linear morphism. Thus the explicit coordinate curves
keep the original action, orbit and stabilizer throughout.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]

def projectiveBasisChange
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E) :
    Morphism (projectiveSpace k E) (projectiveSpace k E) :=
  (Morphism.rightSection (ofAffine (glVarietyOf k E)) (projectiveSpace k E)
    ((affinePointEquiv (glVarietyOf k E)).symm
      ((glPointEquivOf k E b₀).symm
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (b₀.equivFun.trans b.equivFun.symm))))).comp
    (projectiveLinearMorphicAction (k := k) E).actionMorphism

set_option backward.isDefEq.respectTransparency false in
theorem projectiveBasisChange_vector
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E) (v : E) (hv : v ≠ 0) :
    projectiveBasisChange b₀ b
        (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)) =
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv) := by
  let g := (glPointEquivOf k E b₀).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (b₀.equivFun.trans b.equivFun.symm))
  let q := projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)
  have hact : projectiveBasisChange b₀ b q =
      (projectiveLinearMorphicAction (k := k) E).toMulAction.smul g q := by
    change (projectiveLinearMorphicAction (k := k) E).actionMorphism
      (Morphism.rightSection _ _ ((affinePointEquiv _).symm g) q) = _
    exact (congrArg (fun z : Point (prod (ofAffine (glVarietyOf k E)) (projectiveSpace k E)) =>
      (projectiveLinearMorphicAction (k := k) E).actionMorphism z)
      (Morphism.rightSection_apply _ _ _ q)).trans
      ((projectiveLinearMorphicAction (k := k) E).actionMorphism_apply g q)
  apply (projectiveSpacePointEquivOf b₀).injective
  rw [hact, projectiveLinearMorphicAction_projectiveSpacePointEquivOf,
    projectiveSpacePointEquivOf_projectivePointOfVector b₀ v hv]
  have hq : q = projectivePointOfVector (b₀.equivFun (b₀.equivFun.symm (b.equivFun v)))
      (b₀.equivFun.map_ne_zero_iff.mpr
        (b₀.equivFun.symm.map_ne_zero_iff.mpr (b.equivFun.map_ne_zero_iff.mpr hv))) := by
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  rw [hq, projectiveSpacePointEquivOf_projectivePointOfVector b₀ _
    (b₀.equivFun.symm.map_ne_zero_iff.mpr (b.equivFun.map_ne_zero_iff.mpr hv)),
    Projectivization.map_mk]
  congr 1
  change ((glPointEquivOf k E b₀) g).1 (b₀.equivFun.symm (b.equivFun v)) = v
  rw [show (glPointEquivOf k E b₀) g =
    LinearMap.GeneralLinearGroup.ofLinearEquiv (b₀.equivFun.trans b.equivFun.symm) by
      exact (glPointEquivOf k E b₀).apply_symm_apply _]
  change b.equivFun.symm (b₀.equivFun (b₀.equivFun.symm (b.equivFun v))) = v
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

/-- The same basis change on a literal homogeneous coordinate vector. -/
theorem projectiveBasisChange_coordinates
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (v : Fin (Module.finrank k E) → k) (hv : v ≠ 0) :
    projectiveBasisChange b₀ b (projectivePointOfVector v hv) =
      projectivePointOfVector (b₀.equivFun (b.equivFun.symm v))
        (b₀.equivFun.map_ne_zero_iff.mpr (b.equivFun.symm.map_ne_zero_iff.mpr hv)) := by
  have h := projectiveBasisChange_vector b₀ b (b.equivFun.symm v)
    (b.equivFun.symm.map_ne_zero_iff.mpr hv)
  simpa only [LinearEquiv.apply_symm_apply] using h

end Theory.AlgebraicGroup.Variety.Geometric
