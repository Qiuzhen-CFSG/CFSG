module
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism

/-!
# Recovering presented affine morphisms from scheme morphisms

The full faithfulness of `Spec` turns a geometric morphism between two affine
presentations into its coordinate-algebra homomorphism. Affine duality then
recovers a polynomial morphism of the original presentations. The resulting
scheme map and point map agree exactly with the input.

This supplies the affine endpoint after gluing the local maps in the
projective-line automorphism construction of Borel, §10.8.
-/

open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section

private def geometricAffinePullback {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) : coordinateRing W →ₐ[k] coordinateRing V where
  toRingHom := (Spec.preimage f.hom).hom
  commutes' r := by
    have h := congrArg Spec.preimage f.commutes
    change Spec.preimage (f.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing W)))) =
      Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing V)))) at h
    erw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h
    exact congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of (coordinateRing V) => φ.hom r) h

def presentedOfGeometric {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) : Variety.Morphism V W :=
  Variety.Morphism.ofPolynomialFunctionAlgHom
    ((coordinateRingAlgEquivPolynomialFunction V).toAlgHom.comp
      ((geometricAffinePullback f).comp (coordinateRingAlgEquivPolynomialFunction W).symm.toAlgHom))

omit [IsAlgClosed k] in
lemma ofAffine_presentedOfGeometric {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) :
    ofAffine_morphism (presentedOfGeometric f) = f := by
  apply Morphism.ext
  change Spec.map (CommRingCat.ofHom (ofAffinePullback (presentedOfGeometric f)).toRingHom) = f.hom
  rw [← Spec.map_preimage f.hom]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (coordinateRingAlgEquivPolynomialFunction V).symm
    ((presentedOfGeometric f).pullbackAlgHom
      (coordinateRingAlgEquivPolynomialFunction W a)) = _
  rw [presentedOfGeometric, Variety.Morphism.pullbackAlgHom_ofPolynomialFunctionAlgHom]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rfl

lemma presentedOfGeometric_apply {V W : Variety k}
    (f : Morphism (ofAffine V) (ofAffine W)) (x : Point (ofAffine V)) :
    (presentedOfGeometric f).toFun (affinePointEquiv V x) = affinePointEquiv W (f x) := by
  calc
    _ = affinePointEquiv W (ofAffine_morphism (presentedOfGeometric f) x) :=
      (affinePointEquiv_ofAffine_morphism (presentedOfGeometric f) x).symm
    _ = _ := by rw [ofAffine_presentedOfGeometric]

end
end Theory.AlgebraicGroup.Variety.Geometric
