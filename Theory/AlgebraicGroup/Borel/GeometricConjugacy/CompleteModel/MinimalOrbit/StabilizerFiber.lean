module

public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitRange
public import Theory.AlgebraicGroup.Bor1.MorphicActionPointStabilizer
public import Mathlib.AlgebraicGeometry.Fiber
public import Theory.AlgebraicGroup.Variety.GeometricDimension

/-!
# Scheme fibres of an orbit map and the reduced point stabilizer

The affine geometric inclusion of a closed subgroup is a closed immersion, since
restriction of polynomial functions is surjective. For the point stabilizer, its
scheme-point range is precisely the orbit fibre support at the selected point.
Both supports are closed in a Jacobson scheme; equality is checked on closed
points using the actual stabilizer equation.

This gives a homeomorphism from the reduced affine stabilizer carrier to the
scheme-theoretic fibre. Left translations transport it to every rational fibre
in the orbit, so all such fibres have the same topological Krull dimension as
the stabilizer. These are homeomorphisms of underlying spaces, not asserted
isomorphisms of schemes: inseparable orbit maps can have nonreduced fibres.

This is the fibre comparison in the orbit–stabilizer dimension argument used by
Borel, *Linear Algebraic Groups*, §11.1; see `refs/KGroup/Bor1/Chapter4.tex`. It
does not assert the remaining dimension formula for a non-affine target.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology
open Theory.AlgebraicGroup

universe u

namespace Theory.AlgebraicGroup.Variety.Geometric

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
/-- The geometric inclusion of an actual closed subgroup is a closed immersion. -/
public theorem ofAffine_closedSubgroup_inclusion_isClosedImmersion (H : ClosedSubgroup G) :
    IsClosedImmersion (ofAffine_morphism H.inclusion.toVariety).hom := by
  apply IsClosedImmersion.spec_of_surjective
  change Function.Surjective (ofAffinePullback H.inclusion.toVariety)
  exact (coordinateRingAlgEquivPolynomialFunction H.carrierVariety).symm.surjective.comp
    (H.restrictionRingHom_surjective.comp
      (coordinateRingAlgEquivPolynomialFunction G).surjective)

/-- The rational range of the geometric inclusion is exactly the original subgroup. -/
public theorem ofAffine_closedSubgroup_inclusion_point_range (H : ClosedSubgroup G) (p : Point (ofAffine G)) :
    p ∈ Set.range (ofAffine_morphism H.inclusion.toVariety) ↔
      affinePointEquiv G p ∈ H.toSubgroup := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [affinePointEquiv_ofAffine_morphism]
    exact (H.pointEquiv (affinePointEquiv H.carrierVariety q)).property
  · intro hp
    have hpRange : affinePointEquiv G p ∈ Set.range H.inclusion.onPoints := by
      rw [H.range_inclusion]
      exact hp
    obtain ⟨q, hq⟩ := hpRange
    refine ⟨(affinePointEquiv H.carrierVariety).symm q, ?_⟩
    apply (affinePointEquiv G).injective
    rw [affinePointEquiv_ofAffine_morphism, Equiv.apply_symm_apply]
    exact hq

private noncomputable def affineLeftTranslationIso
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (ofAffine G).toScheme ≅ (ofAffine G).toScheme where
  hom := (ofAffine_morphism (leftMulMorphism G g)).hom
  inv := (ofAffine_morphism (leftMulMorphism G g⁻¹)).hom
  hom_inv_id := by
    have h : (leftMulMorphism G g⁻¹).comp (leftMulMorphism G g) =
        Theory.AlgebraicGroup.Variety.Morphism.id G := by
      apply Theory.AlgebraicGroup.Variety.Morphism.ext
      funext h
      simp only [Theory.AlgebraicGroup.Variety.Morphism.comp,
        leftMulMorphism_apply, Theory.AlgebraicGroup.Variety.Morphism.id]
      simp
    have hc := congrArg Morphism.hom
      (ofAffine_morphism_comp (leftMulMorphism G g⁻¹) (leftMulMorphism G g))
    rw [h, ofAffine_morphism_id] at hc
    exact hc.symm
  inv_hom_id := by
    have h : (leftMulMorphism G g).comp (leftMulMorphism G g⁻¹) =
        Theory.AlgebraicGroup.Variety.Morphism.id G := by
      apply Theory.AlgebraicGroup.Variety.Morphism.ext
      funext h
      simp only [Theory.AlgebraicGroup.Variety.Morphism.comp,
        leftMulMorphism_apply, Theory.AlgebraicGroup.Variety.Morphism.id]
      simp
    have hc := congrArg Morphism.hom
      (ofAffine_morphism_comp (leftMulMorphism G g) (leftMulMorphism G g⁻¹))
    rw [h, ofAffine_morphism_id] at hc
    exact hc.symm

namespace MorphicAction

variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

/-- The reduced point stabilizer and the scheme orbit fibre have the same closed support. -/
public theorem pointStabilizer_inclusion_range_eq_orbit_fiber :
    Set.range (ofAffine_morphism (A.pointStabilizer x).inclusion.toVariety).hom =
      (A.orbitMorphismAt x).hom ⁻¹' {x.1 (IsLocalRing.closedPoint k)} := by
  let H := A.pointStabilizer x
  let i := ofAffine_morphism H.inclusion.toVariety
  let f := A.orbitMorphismAt x
  let : IsClosedImmersion i.hom := ofAffine_closedSubgroup_inclusion_isClosedImmersion H
  let : JacobsonSpace (ofAffine G).toScheme :=
    LocallyOfFiniteType.jacobsonSpace (ofAffine G).structureMap
  have hI : IsClosed (Set.range i.hom) := i.hom.isClosedEmbedding.isClosed_range
  have hF : IsClosed (f.hom ⁻¹' {x.1 (IsLocalRing.closedPoint k)}) :=
    (pointEquivClosedPoint X.structureMap x).2.preimage f.hom.continuous
  change Set.range i.hom = f.hom ⁻¹' {x.1 (IsLocalRing.closedPoint k)}
  rw [← closure_inter_closedPoints hI, ← closure_inter_closedPoints hF]
  congr 1
  ext z
  by_cases hz : z ∈ closedPoints (ofAffine G).toScheme
  · let p : Point (ofAffine G) :=
      (pointEquivClosedPoint (ofAffine G).structureMap).symm ⟨z, hz⟩
    have hp : p.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint (ofAffine G).structureMap).apply_symm_apply
        ⟨z, hz⟩)
    simp only [Set.mem_inter_iff, hz, and_true]
    rw [← hp, ← i.point_mem_range_iff_closedPoint_mem_range]
    rw [ofAffine_closedSubgroup_inclusion_point_range]
    change affinePointEquiv G p ∈ (A.pointStabilizer x).toSubgroup ↔ _
    rw [A.mem_pointStabilizer]
    have hfp : f p = A.toMulAction.smul (affinePointEquiv G p) x := by
      simpa only [Equiv.symm_apply_apply] using
        A.orbitMorphismAt_apply x (affinePointEquiv G p)
    change _ ↔ (f p).1 (IsLocalRing.closedPoint k) = x.1 (IsLocalRing.closedPoint k)
    rw [← hfp]
    constructor
    · intro h
      rw [h]
    · intro h
      exact (pointEquivClosedPoint X.structureMap).injective (Subtype.ext h)
  · simp only [Set.mem_inter_iff, hz, and_false]

/-- The underlying scheme orbit fibre is homeomorphic to the reduced point stabilizer. -/
public noncomputable def pointStabilizerFiberHomeomorph :
    (ofAffine (A.pointStabilizer x).carrierVariety).toScheme ≃ₜ
      (A.orbitMorphismAt x).hom.fiber (x.1 (IsLocalRing.closedPoint k)) := by
  let i := ofAffine_morphism (A.pointStabilizer x).inclusion.toVariety
  let : IsClosedImmersion i.hom := ofAffine_closedSubgroup_inclusion_isClosedImmersion _
  exact i.hom.isClosedEmbedding.isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (A.pointStabilizer_inclusion_range_eq_orbit_fiber x)) |>.trans
      ((A.orbitMorphismAt x).hom.fiberHomeo _).symm

/-- Nilpotents in the scheme orbit fibre do not change its dimension. -/
public theorem pointStabilizer_fiber_dimension :
    topologicalKrullDim ((A.orbitMorphismAt x).hom.fiber (x.1 (IsLocalRing.closedPoint k))) =
      dimension (ofAffine (A.pointStabilizer x).carrierVariety) :=
  (A.pointStabilizerFiberHomeomorph x).isHomeomorph.topologicalKrullDim_eq.symm

/-- Left translation identifies the underlying fibres at the selected point and its translate. -/
public noncomputable def orbitFiberTranslationHomeomorph
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitMorphismAt x).hom.fiber (x.1 (IsLocalRing.closedPoint k)) ≃ₜ
      (A.orbitMorphismAt x).hom.fiber
        ((A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k)) := by
  let f := A.orbitMorphismAt x
  let e := Scheme.homeoOfIso (affineLeftTranslationIso g)
  let t := A.translationMorphism g
  let F : Set (ofAffine G).toScheme := f.hom ⁻¹' {x.1 (IsLocalRing.closedPoint k)}
  let Fg : Set (ofAffine G).toScheme :=
    f.hom ⁻¹' {(A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k)}
  have hequiv (w : (ofAffine G).toScheme) :
      f.hom (e w) = t.hom (f.hom w) := by
    have h := congrArg (fun m : Morphism (ofAffine G) X => m.hom w)
      (A.translationMorphism_comp_orbitMorphismAt x g)
    exact h.symm
  have hgx : t.hom (x.1 (IsLocalRing.closedPoint k)) =
      (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) :=
    A.translationMorphism_hom_closedPoint g x
  have himage : e '' F = Fg := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change f.hom (e w) = _
      change f.hom w = x.1 (IsLocalRing.closedPoint k) at hw
      rw [hequiv, hw, hgx]
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      change f.hom (e.symm z) = x.1 (IsLocalRing.closedPoint k)
      have hinj : Function.Injective t.hom :=
        (Scheme.homeoOfIso (A.translationIso g)).injective
      apply hinj
      rw [← hequiv, e.apply_symm_apply, hgx]
      exact hz
  exact (f.hom.fiberHomeo _).trans (e.image F) |>.trans
    (Homeomorph.setCongr himage) |>.trans (f.hom.fiberHomeo _).symm

/-- Every rational orbit fibre is homeomorphic to the actual reduced point stabilizer. -/
public noncomputable def orbitFiberStabilizerHomeomorph
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (ofAffine (A.pointStabilizer x).carrierVariety).toScheme ≃ₜ
      (A.orbitMorphismAt x).hom.fiber
        ((A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k)) :=
  (A.pointStabilizerFiberHomeomorph x).trans (A.orbitFiberTranslationHomeomorph x g)

/-- All rational fibres in the orbit have the geometric dimension of its reduced point stabilizer. -/
public theorem orbitFiber_dimension_eq_pointStabilizer (g : Theory.AlgebraicGroup.Variety.Point G) :
    topologicalKrullDim ((A.orbitMorphismAt x).hom.fiber
      ((A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k))) =
        dimension (ofAffine (A.pointStabilizer x).carrierVariety) :=
  (A.orbitFiberStabilizerHomeomorph x g).isHomeomorph.topologicalKrullDim_eq.symm

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric
