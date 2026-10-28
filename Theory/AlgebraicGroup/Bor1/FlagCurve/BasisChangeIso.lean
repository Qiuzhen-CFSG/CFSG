module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.BasisChange
public import Theory.AlgebraicGroup.Bor1.MorphicActionSchemeLaws

/-!
# Changing the basis of the original projective embedding

The literal basis-change morphism is a translation in the regular projective
linear action, hence a scheme isomorphism over the original field. This
preserves the original closed curve while making its torus weights explicit.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]

private theorem Morphism.eq_of_apply_eq
    {V W : Geometric k} (f g : Morphism V W)
    (h : ∀ x : Point V, f x = g x) : f = g := by
  have : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  apply Morphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq W.structureMap
      (Set.univ : Set V.toScheme) isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Point V :=
      ⟨pointOfClosedPoint V.structureMap x hx,
        pointOfClosedPoint_comp V.structureMap x hx⟩
    have hp_apply : p.1 (IsLocalRing.closedPoint k) = x := by
      change pointOfClosedPoint V.structureMap x hx
          (IsLocalRing.closedPoint k) = x
      exact pointOfClosedPoint_apply V.structureMap x hx _
    calc
      f.hom x = f.hom (p.1 (IsLocalRing.closedPoint k)) := by
        exact congrArg f.hom hp_apply.symm
      _ = g.hom (p.1 (IsLocalRing.closedPoint k)) := by
        change (f p).1 (IsLocalRing.closedPoint k) =
          (g p).1 (IsLocalRing.closedPoint k)
        rw [h p]
      _ = g.hom x := by
        exact congrArg g.hom hp_apply
  · exact f.commutes.trans g.commutes.symm

set_option backward.isDefEq.respectTransparency false in
theorem projectiveBasisChange_isIso
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E) :
    IsIso (projectiveBasisChange b₀ b).hom := by
  let A := projectiveLinearMorphicAction (k := k) E
  let g := (glPointEquivOf k E b₀).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (b₀.equivFun.trans b.equivFun.symm))
  have h : projectiveBasisChange b₀ b = A.translationMorphism g := by
    apply Morphism.eq_of_apply_eq
    intro p
    rw [A.translationMorphism_apply]
    change A.actionMorphism (Morphism.rightSection _ _ ((affinePointEquiv _).symm g) p) = _
    exact (congrArg (fun z => A.actionMorphism z)
      (Morphism.rightSection_apply _ _ _ p)).trans (A.actionMorphism_apply g p)
  rw [h, ← A.translationIso_hom]
  infer_instance

end Theory.AlgebraicGroup.Variety.Geometric
