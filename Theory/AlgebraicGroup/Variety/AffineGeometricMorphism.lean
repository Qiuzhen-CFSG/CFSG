module

public import Theory.AlgebraicGroup.Variety.AffineDuality
public import Theory.AlgebraicGroup.Variety.MorphicAction
public import Theory.AlgebraicGroup.Variety.Zariski

/-!
# Presented affine morphisms as geometric morphisms

This module is the affine-to-geometric bridge used by the Bor1 geometric orbit
arguments.  A polynomial morphism of presented affine varieties induces the
contravariant map on reduced coordinate rings, hence a morphism between the
associated affine schemes `Geometric.ofAffine`.  The construction is functorial:
identities, compositions, structure maps, and rational points agree with the
existing presented APIs through `affinePointEquiv`.

The module also records the product comparison needed to turn a presented
morphism `V x W -> X` into a geometric morphism
`ofAffine V x ofAffine W -> ofAffine X`.  The comparison is the standard affine
pullback isomorphism `Spec (A tensor_k B)` composed with the coordinate-ring
equivalence for the repository's product presentation.  Its projection and
rational-point formulas are stated explicitly.

Finally, closed subsets of an affine geometric variety are transported back to
Zariski-closed subsets of presented rational points by evaluating the
corresponding section at the closed point of `Spec k`.  This is the point-prime
bridge needed for equalizer and preimage arguments such as point stabilizers of
morphic actions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

namespace Theory.AlgebraicGroup.Variety

universe u

variable {k : Type u} [Field k]

namespace Geometric

/-- Geometric morphisms are determined by their underlying scheme morphism. -/
public theorem Morphism.ext {V W : Geometric k} {f g : Morphism V W}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

namespace Morphism

@[simp]
public theorem id_apply_point {V : Geometric k} (x : Point V) :
    id V x = x := by
  apply Subtype.ext
  change (x : Point V).1 ≫ 𝟙 V.toScheme = (x : Point V).1
  simp

@[simp]
public theorem comp_apply_point {U V W : Geometric k}
    (f : Morphism U V) (g : Morphism V W) (x : Point U) :
    comp f g x = g (f x) := by
  apply Subtype.ext
  rfl

/-- The constant geometric morphism with value a rational point. -/
public noncomputable def const (V : Geometric k) {W : Geometric k}
    (y : Point W) : Morphism V W where
  hom := V.structureMap ≫ y.1
  commutes := by
    rw [Category.assoc, y.2, Category.comp_id]

@[simp]
public theorem const_apply (V : Geometric k) {W : Geometric k}
    (y : Point W) (x : Point V) :
    const V y x = y := by
  apply Subtype.ext
  change ((x : Point V).1 ≫ V.structureMap) ≫ (y : Point W).1 = (y : Point W).1
  simpa using congrArg (fun q => q ≫ (y : Point W).1) (x : Point V).2

/-- Pair two geometric morphisms into a product. -/
public noncomputable def pair [IsAlgClosed k] {X Y Z : Geometric k}
    (f : Morphism X Y) (g : Morphism X Z) : Morphism X (prod Y Z) where
  hom := pullback.lift f.hom g.hom (by rw [f.commutes, g.commutes])
  commutes := by
    change pullback.lift f.hom g.hom _ ≫
        pullback.fst Y.structureMap Z.structureMap ≫ Y.structureMap =
      X.structureMap
    rw [pullback.lift_fst_assoc, f.commutes]

@[simp]
public theorem pair_apply [IsAlgClosed k] {X Y Z : Geometric k}
    (f : Morphism X Y) (g : Morphism X Z) (x : Point X) :
    pair f g x = prodPoint (f x) (g x) := by
  apply Subtype.ext
  change (x : Point X).1 ≫ pullback.lift f.hom g.hom _ =
    pullback.lift ((f x) : Point Y).1 ((g x) : Point Z).1 _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- The section of the first projection through a fixed point of the second factor. -/
public noncomputable def leftSection [IsAlgClosed k] (V W : Geometric k)
    (y : Point W) : Morphism V (prod V W) :=
  pair (id V) (const V y)

@[simp]
public theorem leftSection_apply [IsAlgClosed k] (V W : Geometric k)
    (y : Point W) (x : Point V) :
    leftSection V W y x = prodPoint x y := by
  rw [leftSection, pair_apply]
  rw [id_apply_point, const_apply]

/-- The section of the second projection through a fixed point of the first factor. -/
public noncomputable def rightSection [IsAlgClosed k] (V W : Geometric k)
    (x : Point V) : Morphism W (prod V W) :=
  pair (const W x) (id W)

@[simp]
public theorem rightSection_apply [IsAlgClosed k] (V W : Geometric k)
    (x : Point V) (y : Point W) :
    rightSection V W x y = prodPoint x y := by
  rw [rightSection, pair_apply]
  rw [const_apply, id_apply_point]

end Morphism

/-- Public alias for a constant point-valued geometric morphism. -/
public noncomputable abbrev constantPointMorphism (V X : Geometric k) (x : Point X) :
    Morphism V X :=
  Morphism.const V x

@[simp]
public theorem constantPointMorphism_apply (V X : Geometric k) (x : Point X)
    (y : Point V) :
    constantPointMorphism V X x y = x :=
  Morphism.const_apply V x y

/-- Public alias for the section `v |-> (v, x)` of a geometric product. -/
public noncomputable abbrev productPointSection [IsAlgClosed k]
    (V X : Geometric k) (x : Point X) : Morphism V (prod V X) :=
  Morphism.leftSection V X x

@[simp]
public theorem productPointSection_apply [IsAlgClosed k]
    (V X : Geometric k) (x : Point X) (y : Point V) :
    productPointSection V X x y = prodPoint y x :=
  Morphism.leftSection_apply V X x y

/-- The coordinate-ring pullback induced by a presented affine morphism. -/
public noncomputable def ofAffinePullback {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W) :
    Theory.AlgebraicGroup.coordinateRing W →ₐ[k]
      Theory.AlgebraicGroup.coordinateRing V :=
  (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).symm.toAlgHom.comp
    (f.pullbackAlgHom.comp
      (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction W).toAlgHom)

@[simp]
public theorem ofAffinePullback_algebraMap
    {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W) (r : k) :
    ofAffinePullback f (algebraMap k (Theory.AlgebraicGroup.coordinateRing W) r) =
      algebraMap k (Theory.AlgebraicGroup.coordinateRing V) r :=
  (ofAffinePullback f).commutes r

@[simp]
public theorem ofAffinePullback_id (V : Theory.AlgebraicGroup.Variety k) :
    ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.id V) =
      AlgHom.id k (Theory.AlgebraicGroup.coordinateRing V) := by
  apply AlgHom.ext
  intro a
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).injective
  simp [ofAffinePullback, Theory.AlgebraicGroup.Variety.Morphism.pullbackAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackRingHom_id]

@[simp]
public theorem ofAffinePullback_comp
    {U V W : Theory.AlgebraicGroup.Variety k}
    (g : Theory.AlgebraicGroup.Variety.Morphism V W)
    (f : Theory.AlgebraicGroup.Variety.Morphism U V) :
    ofAffinePullback (g.comp f) =
      (ofAffinePullback f).comp (ofAffinePullback g) := by
  apply AlgHom.ext
  intro a
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction U).injective
  simp [ofAffinePullback, Theory.AlgebraicGroup.Variety.Morphism.pullbackAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackRingHom_comp]

/-- A presented affine morphism induces the corresponding morphism of affine schemes. -/
public noncomputable def ofAffine_morphism
    {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W) :
    Morphism (ofAffine V) (ofAffine W) where
  hom := Spec.map (CommRingCat.ofHom (ofAffinePullback f).toRingHom)
  commutes := by
    change Spec.map (CommRingCat.ofHom (ofAffinePullback f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (Theory.AlgebraicGroup.coordinateRing W))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Theory.AlgebraicGroup.coordinateRing V)))
    rw [← Spec.map_comp]
    rw [Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change ofAffinePullback f
        (algebraMap k (Theory.AlgebraicGroup.coordinateRing W) r) =
      algebraMap k (Theory.AlgebraicGroup.coordinateRing V) r
    exact (ofAffinePullback f).commutes r

@[simp]
public theorem ofAffine_morphism_id (V : Theory.AlgebraicGroup.Variety k) :
    ofAffine_morphism (Theory.AlgebraicGroup.Variety.Morphism.id V) =
      Morphism.id (ofAffine V) := by
  apply Morphism.ext
  change Spec.map (CommRingCat.ofHom
      (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.id V)).toRingHom) =
    𝟙 (Spec (.of (Theory.AlgebraicGroup.coordinateRing V)))
  rw [ofAffinePullback_id]
  exact Spec.map_id _

@[simp]
public theorem ofAffine_morphism_comp
    {U V W : Theory.AlgebraicGroup.Variety k}
    (g : Theory.AlgebraicGroup.Variety.Morphism V W)
    (f : Theory.AlgebraicGroup.Variety.Morphism U V) :
    ofAffine_morphism (g.comp f) =
      Morphism.comp (ofAffine_morphism f) (ofAffine_morphism g) := by
  apply Morphism.ext
  change Spec.map (CommRingCat.ofHom (ofAffinePullback (g.comp f)).toRingHom) =
    Spec.map (CommRingCat.ofHom (ofAffinePullback f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ofAffinePullback g).toRingHom)
  rw [ofAffinePullback_comp, ← Spec.map_comp]
  rfl

public theorem coordinateRingPointAlgHomEquiv_apply
    [IsAlgClosed k] (V : Theory.AlgebraicGroup.Variety k)
    (x : Theory.AlgebraicGroup.Variety.Point V) :
    coordinateRingPointAlgHomEquiv V x =
      Theory.AlgebraicGroup.coordinatePointAlgHom V x := by
  rfl

public theorem coordinateRingPointAlgHomEquiv_morphism_apply
    [IsAlgClosed k] {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W)
    (x : Theory.AlgebraicGroup.Variety.Point V) :
    coordinateRingPointAlgHomEquiv W (f.toFun x) =
      (coordinateRingPointAlgHomEquiv V x).comp (ofAffinePullback f) := by
  apply AlgHom.ext
  intro a
  simp [coordinateRingPointAlgHomEquiv_apply, ofAffinePullback,
    Theory.AlgebraicGroup.coordinatePointAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackRingHom_apply,
    Theory.AlgebraicGroup.Variety.PolynomialFunction.pullback]
  rfl

public theorem affinePointAlgHomEquiv_ofAffine_morphism
    [IsAlgClosed k] {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W)
    (p : Point (ofAffine V)) :
    affinePointAlgHomEquiv W (ofAffine_morphism f p) =
      (affinePointAlgHomEquiv V p).comp (ofAffinePullback f) := by
  apply AlgHom.ext
  intro a
  change (Spec.preimage
      ((p : Point (ofAffine V)).1 ≫
        Spec.map (CommRingCat.ofHom (ofAffinePullback f).toRingHom))).hom a =
    (Spec.preimage (p : Point (ofAffine V)).1).hom ((ofAffinePullback f).toRingHom a)
  erw [Spec.preimage_comp, Spec.preimage_map]
  rfl

@[simp]
public theorem coordinateRingPointAlgHomEquiv_affinePointEquiv
    [IsAlgClosed k] (V : Theory.AlgebraicGroup.Variety k)
    (p : Point (ofAffine V)) :
    coordinateRingPointAlgHomEquiv V (affinePointEquiv V p) =
      affinePointAlgHomEquiv V p := by
  change coordinateRingPointAlgHomEquiv V
      ((coordinateRingPointAlgHomEquiv V).symm ((affinePointAlgHomEquiv V) p)) =
    affinePointAlgHomEquiv V p
  exact Equiv.apply_symm_apply (coordinateRingPointAlgHomEquiv V)
    ((affinePointAlgHomEquiv V) p)

public theorem affinePointEquiv_ofAffine_morphism
    [IsAlgClosed k] {V W : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism V W)
    (p : Point (ofAffine V)) :
    affinePointEquiv W (ofAffine_morphism f p) =
      f.toFun (affinePointEquiv V p) := by
  apply (coordinateRingPointAlgHomEquiv W).injective
  calc
    coordinateRingPointAlgHomEquiv W (affinePointEquiv W (ofAffine_morphism f p))
        = affinePointAlgHomEquiv W (ofAffine_morphism f p) :=
        coordinateRingPointAlgHomEquiv_affinePointEquiv W (ofAffine_morphism f p)
    _ = (affinePointAlgHomEquiv V p).comp (ofAffinePullback f) :=
        affinePointAlgHomEquiv_ofAffine_morphism f p
    _ = ((coordinateRingPointAlgHomEquiv V) (affinePointEquiv V p)).comp
          (ofAffinePullback f) := by
        rw [coordinateRingPointAlgHomEquiv_affinePointEquiv]
    _ = coordinateRingPointAlgHomEquiv W (f.toFun (affinePointEquiv V p)) :=
        (coordinateRingPointAlgHomEquiv_morphism_apply f (affinePointEquiv V p)).symm

public theorem coordinateRing_prod_equiv_tensorProduct_includeLeft
    (V W : Theory.AlgebraicGroup.Variety k)
    (a : Theory.AlgebraicGroup.coordinateRing V) :
    Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W
        (a ⊗ₜ[k] 1) =
      (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
          (Theory.AlgebraicGroup.Variety.prod V W)).symm
        (Theory.AlgebraicGroup.polynomialFunctionLeft V W
          (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V a)) := by
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (Theory.AlgebraicGroup.Variety.prod V W)).injective
  apply Theory.AlgebraicGroup.Variety.PolynomialFunction.ext
  intro z
  rw [AlgEquiv.apply_symm_apply,
    Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct_tmul_apply]
  have hone : (1 : Theory.AlgebraicGroup.Variety.PolynomialFunction W)
      (Theory.AlgebraicGroup.Variety.prodPointEquiv V W z).2 = (1 : k) := by
    rw [← (algebraMap k
      (Theory.AlgebraicGroup.Variety.PolynomialFunction W)).map_one]
    exact Theory.AlgebraicGroup.polynomialFunction_algebraMap_apply W 1 _
  simp [Theory.AlgebraicGroup.polynomialFunctionLeft_apply, hone]

public theorem coordinateRing_prod_equiv_tensorProduct_includeRight
    (V W : Theory.AlgebraicGroup.Variety k)
    (b : Theory.AlgebraicGroup.coordinateRing W) :
    Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W
        (1 ⊗ₜ[k] b) =
      (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
          (Theory.AlgebraicGroup.Variety.prod V W)).symm
        (Theory.AlgebraicGroup.polynomialFunctionRight V W
          (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction W b)) := by
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (Theory.AlgebraicGroup.Variety.prod V W)).injective
  apply Theory.AlgebraicGroup.Variety.PolynomialFunction.ext
  intro z
  rw [AlgEquiv.apply_symm_apply,
    Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct_tmul_apply]
  have hone : (1 : Theory.AlgebraicGroup.Variety.PolynomialFunction V)
      (Theory.AlgebraicGroup.Variety.prodPointEquiv V W z).1 = (1 : k) := by
    rw [← (algebraMap k
      (Theory.AlgebraicGroup.Variety.PolynomialFunction V)).map_one]
    exact Theory.AlgebraicGroup.polynomialFunction_algebraMap_apply V 1 _
  simp [Theory.AlgebraicGroup.polynomialFunctionRight_apply, hone]

@[simp]
public theorem ofAffinePullback_fst (V W : Theory.AlgebraicGroup.Variety k)
    (a : Theory.AlgebraicGroup.coordinateRing V) :
    ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.fst V W) a =
      Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W
        (a ⊗ₜ[k] 1) := by
  rw [coordinateRing_prod_equiv_tensorProduct_includeLeft]
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (Theory.AlgebraicGroup.Variety.prod V W)).injective
  apply Theory.AlgebraicGroup.Variety.PolynomialFunction.ext
  intro z
  simp [ofAffinePullback, Theory.AlgebraicGroup.Variety.Morphism.pullbackAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackRingHom_apply,
    Theory.AlgebraicGroup.Variety.PolynomialFunction.pullback]
  rfl

@[simp]
public theorem ofAffinePullback_snd (V W : Theory.AlgebraicGroup.Variety k)
    (b : Theory.AlgebraicGroup.coordinateRing W) :
    ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.snd V W) b =
      Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W
        (1 ⊗ₜ[k] b) := by
  rw [coordinateRing_prod_equiv_tensorProduct_includeRight]
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (Theory.AlgebraicGroup.Variety.prod V W)).injective
  apply Theory.AlgebraicGroup.Variety.PolynomialFunction.ext
  intro z
  simp [ofAffinePullback, Theory.AlgebraicGroup.Variety.Morphism.pullbackAlgHom,
    Theory.AlgebraicGroup.Variety.Morphism.pullbackRingHom_apply,
    Theory.AlgebraicGroup.Variety.PolynomialFunction.pullback]
  rfl

/-- The scheme product of two affine presentations maps to the affine presentation
of their custom product. -/
public noncomputable def ofAffineProductComparison
    [IsAlgClosed k] (V W : Theory.AlgebraicGroup.Variety k) :
    Morphism (prod (ofAffine V) (ofAffine W))
      (ofAffine (Theory.AlgebraicGroup.Variety.prod V W)) where
  hom :=
    (pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom)
  commutes := by
    change ((pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
        (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (Theory.AlgebraicGroup.coordinateRing
            (Theory.AlgebraicGroup.Variety.prod V W)))) =
      pullback.fst (ofAffine V).structureMap (ofAffine W).structureMap ≫
        (ofAffine V).structureMap
    rw [Category.assoc, ← Spec.map_comp]
    have hbase :
        CommRingCat.ofHom
              (algebraMap k (Theory.AlgebraicGroup.coordinateRing
                (Theory.AlgebraicGroup.Variety.prod V W))) ≫
          CommRingCat.ofHom
              (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom =
          CommRingCat.ofHom
            (algebraMap k
              (TensorProduct k (Theory.AlgebraicGroup.coordinateRing V)
                (Theory.AlgebraicGroup.coordinateRing W))) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.commutes r
    rw [hbase]
    change (pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
        (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k
            (TensorProduct k (Theory.AlgebraicGroup.coordinateRing V)
              (Theory.AlgebraicGroup.coordinateRing W)))) =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (Theory.AlgebraicGroup.coordinateRing V))))
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (Theory.AlgebraicGroup.coordinateRing W)))) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (Theory.AlgebraicGroup.coordinateRing V)))
    exact pullbackSpecIso_hom_base k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)

@[simp]
public theorem ofAffineProductComparison_fst
    [IsAlgClosed k] (V W : Theory.AlgebraicGroup.Variety k) :
    Morphism.comp (ofAffineProductComparison V W)
        (ofAffine_morphism (Theory.AlgebraicGroup.Variety.Morphism.fst V W)) =
      fst (ofAffine V) (ofAffine W) := by
  apply Morphism.ext
  change ((pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom
        (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.fst V W)).toRingHom) =
    pullback.fst (ofAffine V).structureMap (ofAffine W).structureMap
  rw [Category.assoc, ← Spec.map_comp]
  let iLeft : Theory.AlgebraicGroup.coordinateRing V →+*
      Theory.AlgebraicGroup.coordinateRing V ⊗[k]
        Theory.AlgebraicGroup.coordinateRing W :=
    Algebra.TensorProduct.includeLeftRingHom
      (R := k) (A := Theory.AlgebraicGroup.coordinateRing V)
      (B := Theory.AlgebraicGroup.coordinateRing W)
  have hleft :
        CommRingCat.ofHom
            (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.fst V W)).toRingHom ≫
        CommRingCat.ofHom
            (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom =
        CommRingCat.ofHom
          (R := Theory.AlgebraicGroup.coordinateRing V)
          (S := Theory.AlgebraicGroup.coordinateRing V ⊗[k]
            Theory.AlgebraicGroup.coordinateRing W) iLeft := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm
        (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.fst V W) a) =
      iLeft a
    rw [ofAffinePullback_fst]
    simp [iLeft, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [hleft]
  change (pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
      Spec.map (CommRingCat.ofHom
        (R := Theory.AlgebraicGroup.coordinateRing V)
        (S := Theory.AlgebraicGroup.coordinateRing V ⊗[k]
          Theory.AlgebraicGroup.coordinateRing W) iLeft) =
    pullback.fst (ofAffine V).structureMap (ofAffine W).structureMap
  exact pullbackSpecIso_hom_fst k (Theory.AlgebraicGroup.coordinateRing V)
    (Theory.AlgebraicGroup.coordinateRing W)

@[simp]
public theorem ofAffineProductComparison_snd
    [IsAlgClosed k] (V W : Theory.AlgebraicGroup.Variety k) :
    Morphism.comp (ofAffineProductComparison V W)
        (ofAffine_morphism (Theory.AlgebraicGroup.Variety.Morphism.snd V W)) =
      snd (ofAffine V) (ofAffine W) := by
  apply Morphism.ext
  change ((pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom
        (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.snd V W)).toRingHom) =
    pullback.snd (ofAffine V).structureMap (ofAffine W).structureMap
  rw [Category.assoc, ← Spec.map_comp]
  let iRight : Theory.AlgebraicGroup.coordinateRing W →+*
      Theory.AlgebraicGroup.coordinateRing V ⊗[k]
        Theory.AlgebraicGroup.coordinateRing W :=
    (Algebra.TensorProduct.includeRight :
      Theory.AlgebraicGroup.coordinateRing W →ₐ[k]
        Theory.AlgebraicGroup.coordinateRing V ⊗[k]
          Theory.AlgebraicGroup.coordinateRing W).toRingHom
  have hright :
        CommRingCat.ofHom
            (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.snd V W)).toRingHom ≫
        CommRingCat.ofHom
            (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm.toRingHom =
        CommRingCat.ofHom
          (R := Theory.AlgebraicGroup.coordinateRing W)
          (S := Theory.AlgebraicGroup.coordinateRing V ⊗[k]
            Theory.AlgebraicGroup.coordinateRing W) iRight := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change (Theory.AlgebraicGroup.coordinateRing_prod_equiv_tensorProduct V W).symm
        (ofAffinePullback (Theory.AlgebraicGroup.Variety.Morphism.snd V W) b) =
      iRight b
    rw [ofAffinePullback_snd]
    simp [iRight, Algebra.TensorProduct.includeRight_apply]
  rw [hright]
  change (pullbackSpecIso k (Theory.AlgebraicGroup.coordinateRing V)
      (Theory.AlgebraicGroup.coordinateRing W)).hom ≫
      Spec.map (CommRingCat.ofHom
        (R := Theory.AlgebraicGroup.coordinateRing W)
        (S := Theory.AlgebraicGroup.coordinateRing V ⊗[k]
          Theory.AlgebraicGroup.coordinateRing W) iRight) =
    pullback.snd (ofAffine V).structureMap (ofAffine W).structureMap
  exact pullbackSpecIso_hom_snd k (Theory.AlgebraicGroup.coordinateRing V)
    (Theory.AlgebraicGroup.coordinateRing W)

public theorem affinePointEquiv_ofAffineProductComparison_prodPoint
    [IsAlgClosed k] (V W : Theory.AlgebraicGroup.Variety k)
    (x : Point (ofAffine V)) (y : Point (ofAffine W)) :
    affinePointEquiv (Theory.AlgebraicGroup.Variety.prod V W)
        (ofAffineProductComparison V W (prodPoint x y)) =
      (Theory.AlgebraicGroup.Variety.prodPointEquiv V W).symm
        (affinePointEquiv V x, affinePointEquiv W y) := by
  apply (Theory.AlgebraicGroup.Variety.prodPointEquiv V W).injective
  apply Prod.ext
  · have hleft :
        ofAffine_morphism (Theory.AlgebraicGroup.Variety.Morphism.fst V W)
            (ofAffineProductComparison V W (prodPoint x y)) = x := by
      apply Subtype.ext
      change ((prodPoint x y).1 ≫ (ofAffineProductComparison V W).hom) ≫
          (ofAffine_morphism
            (Theory.AlgebraicGroup.Variety.Morphism.fst V W)).hom = x.1
      rw [Category.assoc]
      have hhom := congrArg Morphism.hom (ofAffineProductComparison_fst V W)
      change (ofAffineProductComparison V W).hom ≫
          (ofAffine_morphism
            (Theory.AlgebraicGroup.Variety.Morphism.fst V W)).hom =
        (fst (ofAffine V) (ofAffine W)).hom at hhom
      rw [hhom]
      exact congrArg Subtype.val (fst_prodPoint x y)
    simp only [Equiv.apply_symm_apply]
    change (Theory.AlgebraicGroup.Variety.Morphism.fst V W).toFun
        (affinePointEquiv (Theory.AlgebraicGroup.Variety.prod V W)
          (ofAffineProductComparison V W (prodPoint x y))) =
      affinePointEquiv V x
    rw [← affinePointEquiv_ofAffine_morphism
      (Theory.AlgebraicGroup.Variety.Morphism.fst V W)
      (ofAffineProductComparison V W (prodPoint x y)), hleft]
  · have hright :
        ofAffine_morphism (Theory.AlgebraicGroup.Variety.Morphism.snd V W)
            (ofAffineProductComparison V W (prodPoint x y)) = y := by
      apply Subtype.ext
      change ((prodPoint x y).1 ≫ (ofAffineProductComparison V W).hom) ≫
          (ofAffine_morphism
            (Theory.AlgebraicGroup.Variety.Morphism.snd V W)).hom = y.1
      rw [Category.assoc]
      have hhom := congrArg Morphism.hom (ofAffineProductComparison_snd V W)
      change (ofAffineProductComparison V W).hom ≫
          (ofAffine_morphism
            (Theory.AlgebraicGroup.Variety.Morphism.snd V W)).hom =
        (snd (ofAffine V) (ofAffine W)).hom at hhom
      rw [hhom]
      exact congrArg Subtype.val (snd_prodPoint x y)
    simp only [Equiv.apply_symm_apply]
    change (Theory.AlgebraicGroup.Variety.Morphism.snd V W).toFun
        (affinePointEquiv (Theory.AlgebraicGroup.Variety.prod V W)
          (ofAffineProductComparison V W (prodPoint x y))) =
      affinePointEquiv W y
    rw [← affinePointEquiv_ofAffine_morphism
      (Theory.AlgebraicGroup.Variety.Morphism.snd V W)
      (ofAffineProductComparison V W (prodPoint x y)), hright]

/-- A presented morphism out of a presented affine product, viewed on the
geometric product of the associated affine schemes. -/
public noncomputable def ofAffineProductMorphism
    [IsAlgClosed k] {V W X : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism
      (Theory.AlgebraicGroup.Variety.prod V W) X) :
    Morphism (prod (ofAffine V) (ofAffine W)) (ofAffine X) :=
  Morphism.comp (ofAffineProductComparison V W) (ofAffine_morphism f)

public theorem affinePointEquiv_ofAffineProductMorphism_prodPoint
    [IsAlgClosed k] {V W X : Theory.AlgebraicGroup.Variety k}
    (f : Theory.AlgebraicGroup.Variety.Morphism
      (Theory.AlgebraicGroup.Variety.prod V W) X)
    (x : Point (ofAffine V)) (y : Point (ofAffine W)) :
    affinePointEquiv X (ofAffineProductMorphism f (prodPoint x y)) =
      f.toFun ((Theory.AlgebraicGroup.Variety.prodPointEquiv V W).symm
        (affinePointEquiv V x, affinePointEquiv W y)) := by
  simpa [ofAffineProductMorphism, Morphism.comp_apply_point,
    affinePointEquiv_ofAffineProductComparison_prodPoint] using
      affinePointEquiv_ofAffine_morphism f
        (ofAffineProductComparison V W (prodPoint x y))

/-- The affine closed point attached to a presented point is the coordinate-ring
comap of the presented point-prime. -/
public theorem affinePointEquiv_symm_closedPoint_eq_pointPrime
    [IsAlgClosed k] (V : Theory.AlgebraicGroup.Variety k)
    (x : Theory.AlgebraicGroup.Variety.Point V) :
    ((affinePointEquiv V).symm x).1 (IsLocalRing.closedPoint k) =
      PrimeSpectrum.comap
        (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).toRingHom
        (V.pointPrime x) := by
  change PrimeSpectrum.comap (coordinateRingPointAlgHomEquiv V x).toRingHom
      (IsLocalRing.closedPoint k) =
    PrimeSpectrum.comap
      (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).toRingHom
      (V.pointPrime x)
  apply PrimeSpectrum.ext
  ext a
  change (coordinateRingPointAlgHomEquiv V x a) ∈
      (IsLocalRing.closedPoint k).asIdeal ↔
    Theory.AlgebraicGroup.polynomialFunctionPointAlgHom V x
        (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V a) = 0
  have hclosedPointIdeal : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) := by
    change IsLocalRing.maximalIdeal k = (⊥ : Ideal k)
    rw [IsLocalRing.maximalIdeal_eq_bot]
  rw [hclosedPointIdeal, Ideal.mem_bot, coordinateRingPointAlgHomEquiv_apply]
  rfl

/-- Closed subsets of an affine geometric variety pull back to Zariski-closed
subsets of the presented affine points. -/
public theorem isZariskiClosed_ofAffine_closedPoint_preimage
    [IsAlgClosed k] {G : Theory.AlgebraicGroup.Variety k}
    (S : Set (ofAffine G).toScheme) (hS : IsClosed S) :
    IsZariskiClosed G {g : Theory.AlgebraicGroup.Variety.Point G |
      (((affinePointEquiv G).symm g).1 (IsLocalRing.closedPoint k)) ∈ S} := by
  let S' : Set (PrimeSpectrum (Theory.AlgebraicGroup.coordinateRing G)) := S
  have hS' : IsClosed S' := by
    change IsClosed (S : Set (PrimeSpectrum (Theory.AlgebraicGroup.coordinateRing G))) at hS
    exact hS
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal S').mp hS'
  refine ⟨{p | Ideal.Quotient.mk
      (Theory.AlgebraicGroup.vanishingIdeal
        (Set.univ : Set (Theory.AlgebraicGroup.Variety.Point G))) p ∈ I}, ?_⟩
  ext g
  let xg : PrimeSpectrum (Theory.AlgebraicGroup.coordinateRing G) :=
    PrimeSpectrum.comap (Theory.AlgebraicGroup.coordinatePointAlgHom G g).toRingHom
      (IsLocalRing.closedPoint k)
  change xg ∈ S' ↔
    ∀ p,
    Ideal.Quotient.mk
      (Theory.AlgebraicGroup.vanishingIdeal
        (Set.univ : Set (Theory.AlgebraicGroup.Variety.Point G))) p ∈ I →
      Theory.AlgebraicGroup.evalPolynomial g.val p = 0
  rw [hI]
  rw [PrimeSpectrum.mem_zeroLocus]
  dsimp [xg]
  have hclosedPointIdeal : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) := by
    change IsLocalRing.maximalIdeal k = (⊥ : Ideal k)
    rw [IsLocalRing.maximalIdeal_eq_bot]
  constructor
  · intro hIle p hp
    have hpker :
        (Theory.AlgebraicGroup.coordinatePointAlgHom G g)
          (Ideal.Quotient.mk
            (Theory.AlgebraicGroup.vanishingIdeal
              (Set.univ : Set (Theory.AlgebraicGroup.Variety.Point G))) p) ∈
          (IsLocalRing.closedPoint k).asIdeal :=
      hIle hp
    rw [hclosedPointIdeal] at hpker
    rw [Ideal.mem_bot] at hpker
    rw [Theory.AlgebraicGroup.coordinatePointAlgHom_apply,
      Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction_mk] at hpker
    simpa [Theory.AlgebraicGroup.evaluationRingHom,
      Theory.AlgebraicGroup.Variety.PolynomialFunction.ofPolynomial,
      Theory.AlgebraicGroup.Variety.PolynomialFunction.toFun] using hpker
  · intro hvan a ha
    refine Quotient.inductionOn a ?_ ha
    intro p hp
    rw [hclosedPointIdeal]
    change (Theory.AlgebraicGroup.coordinatePointAlgHom G g)
        (Ideal.Quotient.mk
          (Theory.AlgebraicGroup.vanishingIdeal
            (Set.univ : Set (Theory.AlgebraicGroup.Variety.Point G))) p) ∈
        (⊥ : Ideal k)
    rw [Ideal.mem_bot]
    rw [Theory.AlgebraicGroup.coordinatePointAlgHom_apply,
      Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction_mk]
    simpa [Theory.AlgebraicGroup.evaluationRingHom,
      Theory.AlgebraicGroup.Variety.PolynomialFunction.ofPolynomial,
      Theory.AlgebraicGroup.Variety.PolynomialFunction.toFun] using hvan p hp

namespace Morphism

/-- The map to the product used to test equality of two morphisms. -/
public noncomputable def equalizerPair {V X : Geometric k} (f g : Morphism V X) :
    V.toScheme ⟶ pullback X.structureMap X.structureMap :=
  pullback.lift f.hom g.hom (by rw [f.commutes, g.commutes])

public theorem diagonal_preimage_isClosed {V X : Geometric k} (f g : Morphism V X) :
    IsClosed {y : V.toScheme |
      f.equalizerPair g y ∈ Set.range (pullback.diagonal X.structureMap)} := by
  have hdiag : IsClosed (Set.range (pullback.diagonal X.structureMap)) :=
    (pullback.diagonal X.structureMap).isClosedMap.isClosed_range
  exact hdiag.preimage (f.equalizerPair g).continuous

public theorem mem_diagonal_preimage_iff_apply_eq
    [IsAlgClosed k] {V X : Geometric k} (f g : Morphism V X) (y : Point V) :
    f.equalizerPair g (y.1 (IsLocalRing.closedPoint k)) ∈
        Set.range (pullback.diagonal X.structureMap) ↔
      f y = g y := by
  constructor
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    apply ext_of_apply_closedPoint_eq X.structureMap (f y).2 (g y).2
    change (y.1 ≫ f.hom) (IsLocalRing.closedPoint k) =
      (y.1 ≫ g.hom) (IsLocalRing.closedPoint k)
    have hfst := congrArg (fun q => (pullback.fst X.structureMap X.structureMap) q) hz
    have hsnd := congrArg (fun q => (pullback.snd X.structureMap X.structureMap) q) hz
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      pullback.diagonal_fst, Morphism.equalizerPair,
      pullback.lift_fst] at hfst
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      pullback.diagonal_snd, Morphism.equalizerPair,
      pullback.lift_snd] at hsnd
    have hfz : f.hom (y.1 (IsLocalRing.closedPoint k)) = z := by
      simpa using hfst.symm
    have hgz : g.hom (y.1 (IsLocalRing.closedPoint k)) = z := by
      simpa using hsnd.symm
    exact hfz.trans hgz.symm
  · intro hfg
    refine ⟨(f y).1 (IsLocalRing.closedPoint k), ?_⟩
    have hfg' : (f y).1 = (g y).1 := congrArg Subtype.val hfg
    have hpull :
        (f y).1 ≫ pullback.diagonal X.structureMap =
          y.1 ≫ f.equalizerPair g := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        rw [Category.assoc, Morphism.equalizerPair, pullback.lift_fst]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        rw [Category.assoc, Morphism.equalizerPair, pullback.lift_snd]
        exact hfg'
    change ((f y).1 ≫ pullback.diagonal X.structureMap) (IsLocalRing.closedPoint k) =
      (y.1 ≫ f.equalizerPair g) (IsLocalRing.closedPoint k)
    exact congrArg (fun h : Spec (.of k) ⟶ pullback X.structureMap X.structureMap =>
      h (IsLocalRing.closedPoint k)) hpull

public theorem preimage_isZariskiClosed_ofAffine
    [IsAlgClosed k] {G : Theory.AlgebraicGroup.Variety k} {X : Geometric k}
    (f : Morphism (ofAffine G) X) {S : Set X.toScheme} (hS : IsClosed S) :
    IsZariskiClosed G {g : Theory.AlgebraicGroup.Variety.Point G |
      ((f ((affinePointEquiv G).symm g)).1 (IsLocalRing.closedPoint k)) ∈ S} := by
  have hpre : IsClosed (f.hom ⁻¹' S) := hS.preimage f.hom.continuous
  convert isZariskiClosed_ofAffine_closedPoint_preimage (G := G)
      (f.hom ⁻¹' S) hpre using 1
  ext g
  rfl

public theorem equalizer_isZariskiClosed_ofAffine
    [IsAlgClosed k] {G : Theory.AlgebraicGroup.Variety k} {X : Geometric k}
    (f g : Morphism (ofAffine G) X) :
    IsZariskiClosed G {x : Theory.AlgebraicGroup.Variety.Point G |
      f ((affinePointEquiv G).symm x) = g ((affinePointEquiv G).symm x)} := by
  let S : Set (ofAffine G).toScheme :=
    {y | f.equalizerPair g y ∈ Set.range (pullback.diagonal X.structureMap)}
  have hS : IsClosed S := by
    dsimp [S]
    exact diagonal_preimage_isClosed f g
  have hZ := isZariskiClosed_ofAffine_closedPoint_preimage (G := G) S hS
  convert hZ using 1
  ext x
  change f ((affinePointEquiv G).symm x) = g ((affinePointEquiv G).symm x) ↔
    ((((affinePointEquiv G).symm x).1 (IsLocalRing.closedPoint k)) ∈ S)
  dsimp [S]
  rw [mem_diagonal_preimage_iff_apply_eq]

end Morphism

namespace MorphicAction

/-- The orbit morphism at a rational point, obtained by restricting the action
along the section `g |-> (g, x)`. -/
public noncomputable def orbitMorphismAt
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    [IsAlgClosed k] (A : MorphicAction G X) (x : Point X) :
    Morphism (ofAffine G) X :=
  (productPointSection (ofAffine G) X x).comp A.actionMorphism

public theorem orbitMorphismAt_apply
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    [IsAlgClosed k] (A : MorphicAction G X) (x : Point X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    A.orbitMorphismAt x ((affinePointEquiv G).symm g) =
      A.toMulAction.smul g x := by
  unfold orbitMorphismAt
  rw [Morphism.comp_apply_point, productPointSection_apply]
  exact A.actionMorphism_apply g x

end MorphicAction

end Geometric

end Theory.AlgebraicGroup.Variety
