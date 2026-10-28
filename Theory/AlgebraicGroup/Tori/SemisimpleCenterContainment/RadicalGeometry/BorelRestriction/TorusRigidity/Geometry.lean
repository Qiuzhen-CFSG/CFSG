module

public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Mathlib.Topology.Connected.Clopen
public import Theory.AlgebraicGroup.Variety.AffineDuality
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism

/-!
# Geometric ingredients for rigidity of torus families

A regular map from a connected geometric variety with finite rational image is
constant: the finitely many closed fibres cover the source by density of closed
points, and connectedness forces a single fibre. We also recover a presented
affine morphism from a morphism of the associated affine schemes using Spec
full faithfulness and affine duality. This keeps the slices of a geometric
family regular in the existing algebraic-character API.

These are the geometric steps used in Borel, *Linear Algebraic Groups*, §8.10.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem Morphism.finite_range_constant {V W : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism V W) (hV : IsConnected V)
    (hf : (Set.range f).Finite) (x y : Point V) : f x = f y := by
  let : ConnectedSpace V.toScheme := hV
  let c : Point W → W.toScheme := fun w => w.1 (IsLocalRing.closedPoint k)
  let R : Set W.toScheme := c '' Set.range f
  have hRc (z : W.toScheme) (hz : z ∈ R) : IsClosed ({z} : Set W.toScheme) := by
    obtain ⟨w, _, rfl⟩ := hz
    exact (pointEquivClosedPoint W.structureMap w).property
  have hR : IsClosed R := by
    have h := (hf.image c).isClosed_biUnion (fun z hz => hRc z hz)
    convert h using 1
    ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, rfl⟩⟩
    · intro hz
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hwR, hzw⟩ := Set.mem_iUnion.mp hw
      exact (Set.mem_singleton_iff.mp hzw) ▸ hwR
  have hrange : Set.range f.hom ⊆ R := by
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have hU : IsOpen (f.hom ⁻¹' Rᶜ) := hR.isOpen_compl.preimage f.hom.continuous
    obtain ⟨t, ht⟩ := exists_point_closedPoint_mem_of_isOpen V hU ⟨z, hz⟩
    exact ht ⟨f t, ⟨t, rfl⟩, rfl⟩
  let a := c (f x)
  have ha : a ∈ R := ⟨f x, ⟨x, rfl⟩, rfl⟩
  have hRest : IsClosed (R \ {a}) := by
    have h := (hf.image c).sdiff.isClosed_biUnion (fun z (hz : z ∈ R \ {a}) => hRc z hz.1)
    convert h using 1
    ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, rfl⟩⟩
    · intro hz
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hwR, hzw⟩ := Set.mem_iUnion.mp hw
      exact (Set.mem_singleton_iff.mp hzw) ▸ hwR
  have hcompl : (f.hom ⁻¹' {a})ᶜ = f.hom ⁻¹' (R \ {a}) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_sdiff]
    exact ⟨fun hz => ⟨hrange ⟨z, rfl⟩, hz⟩, fun hz => hz.2⟩
  have hclopen : IsClopen (f.hom ⁻¹' {a}) :=
    ⟨(hRc a ha).preimage f.hom.continuous,
      isClosed_compl_iff.mp (hcompl ▸ hRest.preimage f.hom.continuous)⟩
  have huniv : f.hom ⁻¹' {a} = Set.univ :=
    (isClopen_iff.mp hclopen).resolve_left (by
      intro he
      have hx : x.1 (IsLocalRing.closedPoint k) ∈ f.hom ⁻¹' {a} := rfl
      simp [he] at hx)
  have hya : c (f y) = c (f x) := by
    have hy : y.1 (IsLocalRing.closedPoint k) ∈ f.hom ⁻¹' {a} := by rw [huniv]; trivial
    exact hy
  apply (pointEquivClosedPoint W.structureMap).injective
  exact Subtype.ext hya.symm

end Theory.AlgebraicGroup.Variety.Geometric

open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k]

public noncomputable def geometricAffinePullback {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) : coordinateRing W →ₐ[k] coordinateRing V where
  toRingHom := (Spec.preimage f.hom).hom
  commutes' := fun r => by
    have h : CommRingCat.ofHom (algebraMap k (coordinateRing W)) ≫ Spec.preimage f.hom =
        CommRingCat.ofHom (algebraMap k (coordinateRing V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change Spec.map (Spec.preimage f.hom) ≫ (ofAffine W).structureMap =
        (ofAffine V).structureMap
      exact (congrArg (fun q => q ≫ (ofAffine W).structureMap)
        (Spec.map_preimage f.hom)).trans f.commutes
    exact congr($h r)

public noncomputable def Morphism.toPresentedAffine {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) : Variety.Morphism V W :=
  Variety.Morphism.ofPolynomialFunctionAlgHom
    ((coordinateRingAlgEquivPolynomialFunction V).toAlgHom.comp
      ((geometricAffinePullback f).comp
        (coordinateRingAlgEquivPolynomialFunction W).symm.toAlgHom))

public theorem Morphism.ofAffine_toPresentedAffine {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) : ofAffine_morphism f.toPresentedAffine = f := by
  have h : ofAffinePullback f.toPresentedAffine = geometricAffinePullback f := by
    unfold ofAffinePullback Morphism.toPresentedAffine
    rw [Variety.Morphism.pullbackAlgHom_ofPolynomialFunctionAlgHom]
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
  apply Morphism.ext
  change Spec.map (CommRingCat.ofHom (ofAffinePullback f.toPresentedAffine).toRingHom) = f.hom
  rw [h]
  exact Spec.map_preimage f.hom

public theorem Morphism.toPresentedAffine_apply [IsAlgClosed k] {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) (x : Variety.Point V) :
    f.toPresentedAffine.toFun x = affinePointEquiv W (f ((affinePointEquiv V).symm x)) := by
  have h := affinePointEquiv_ofAffine_morphism f.toPresentedAffine
    ((affinePointEquiv V).symm x)
  rw [f.ofAffine_toPresentedAffine, Equiv.apply_symm_apply] at h
  exact h.symm
end Theory.AlgebraicGroup.Variety.Geometric
