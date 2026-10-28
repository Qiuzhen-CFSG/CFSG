module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Variety.MorphicAction

/-!
# Closed point stabilizers for morphic actions

This module proves the stabilizer part of the Bor1 morphic-action geometry interface.  For a
morphic action of a presented affine algebraic group `G` on a scheme-backed variety `X`, the
stabilizer of a rational point `x : X.Point` is cut out by the equalizer of the orbit morphism
`g |-> g • x` and the constant morphism with value `x`.

The proof uses only the public `MorphicAction` data.  The orbit-at-`x` morphism is obtained by
precomposing the action morphism `G x X -> X` with the section `g |-> (g, x)`.  Since `X` is a
separated finite-type variety, its diagonal is closed; the equalizer is the inverse image of this
diagonal under the pair of morphisms.  A small bridge then translates the resulting closed subset
of the affine scheme `ofAffine G` back into the repository's polynomial `IsZariskiClosed` predicate
on `Variety.Point G`.  The subgroup laws are exactly those of the ordinary point-action
`MulAction.stabilizer`; no orbit, normality, completeness, or fixed-point certificates are added
to `MorphicAction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem isZariskiClosed_ofAffine_closedPoint_preimage
    {G : Theory.AlgebraicGroup.Variety k}
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

private noncomputable def constantPointMorphism (V X : Geometric k) (x : Point X) :
    Morphism V X where
  hom := V.structureMap ≫ x.1
  commutes := by
    rw [Category.assoc, x.2, Category.comp_id]

omit [IsAlgClosed k] in
@[simp] private theorem constantPointMorphism_apply (V X : Geometric k) (x : Point X)
    (y : Point V) :
    constantPointMorphism V X x y = x := by
  apply Subtype.ext
  change y.1 ≫ V.structureMap ≫ x.1 = x.1
  rw [← Category.assoc, y.2, Category.id_comp]

private noncomputable def productPointSection (V X : Geometric k) (x : Point X) :
    Morphism V (prod V X) where
  hom := pullback.lift (𝟙 V.toScheme) (V.structureMap ≫ x.1) (by
    rw [Category.id_comp, Category.assoc, x.2, Category.comp_id])
  commutes := by
    change pullback.lift (𝟙 V.toScheme) (V.structureMap ≫ x.1) _ ≫
        pullback.fst V.structureMap X.structureMap ≫ V.structureMap =
      V.structureMap
    rw [pullback.lift_fst_assoc, Category.id_comp]

@[simp] private theorem productPointSection_apply (V X : Geometric k) (x : Point X)
    (y : Point V) :
    productPointSection V X x y = prodPoint y x := by
  apply Subtype.ext
  change y.1 ≫ pullback.lift (𝟙 V.toScheme) (V.structureMap ≫ x.1) _ =
    pullback.lift y.1 x.1 _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [← Category.assoc, y.2, Category.id_comp]

private noncomputable def MorphicAction.orbitMorphismAt
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X) : Morphism (ofAffine G) X :=
  (productPointSection (ofAffine G) X x).comp A.actionMorphism

private theorem MorphicAction.orbitMorphismAt_apply
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    A.orbitMorphismAt x ((affinePointEquiv G).symm g) =
      A.toMulAction.smul g x := by
  unfold MorphicAction.orbitMorphismAt
  change A.actionMorphism
      (productPointSection (ofAffine G) X x ((affinePointEquiv G).symm g)) =
    A.toMulAction.smul g x
  rw [productPointSection_apply]
  exact A.actionMorphism_apply g x

private noncomputable def Morphism.equalizerPair {V X : Geometric k} (f g : Morphism V X) :
    V.toScheme ⟶ pullback X.structureMap X.structureMap :=
  pullback.lift f.hom g.hom (by rw [f.commutes, g.commutes])

omit [IsAlgClosed k] in
private theorem Morphism.diagonal_preimage_isClosed {V X : Geometric k} (f g : Morphism V X) :
    IsClosed {y : V.toScheme |
      f.equalizerPair g y ∈ Set.range (pullback.diagonal X.structureMap)} := by
  have hdiag : IsClosed (Set.range (pullback.diagonal X.structureMap)) :=
    (pullback.diagonal X.structureMap).isClosedMap.isClosed_range
  exact hdiag.preimage (f.equalizerPair g).continuous

private theorem Morphism.mem_diagonal_preimage_iff_apply_eq
    {V X : Geometric k} (f g : Morphism V X) (y : Point V) :
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

public theorem MorphicAction.pointStabilizer_isZariskiClosed
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X) :
    IsZariskiClosed G
      ((@MulAction.stabilizer
          (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x :
          Subgroup (Theory.AlgebraicGroup.Variety.Point G)) :
        Set (Theory.AlgebraicGroup.Variety.Point G)) := by
  let f := A.orbitMorphismAt x
  let c := constantPointMorphism (ofAffine G) X x
  let S : Set (ofAffine G).toScheme :=
    {y | f.equalizerPair c y ∈ Set.range (pullback.diagonal X.structureMap)}
  have hS : IsClosed S := by
    dsimp [S]
    exact Morphism.diagonal_preimage_isClosed f c
  have hZ := isZariskiClosed_ofAffine_closedPoint_preimage (G := G) S hS
  convert hZ using 1
  ext g
  change g ∈ (@MulAction.stabilizer
      (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x :
      Subgroup (Theory.AlgebraicGroup.Variety.Point G)) ↔
    ((((affinePointEquiv G).symm g).1 (IsLocalRing.closedPoint k)) ∈ S)
  change A.toMulAction.smul g x = x ↔
    ((((affinePointEquiv G).symm g).1 (IsLocalRing.closedPoint k)) ∈ S)
  dsimp [S, f, c]
  rw [Morphism.mem_diagonal_preimage_iff_apply_eq]
  rw [MorphicAction.orbitMorphismAt_apply, constantPointMorphism_apply]
  rfl

public theorem MorphicAction.pointStabilizer_isClosed
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X) :
    IsClosed
      (((@MulAction.stabilizer
          (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x :
          Subgroup (Theory.AlgebraicGroup.Variety.Point G)) :
        Set (Theory.AlgebraicGroup.Variety.Point G))) := by
  rw [Theory.AlgebraicGroup.Variety.isClosed_iff_isZariskiClosed]
  exact A.pointStabilizer_isZariskiClosed x

public def MorphicAction.pointStabilizer
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (@MulAction.stabilizer
      (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x)
    (A.pointStabilizer_isZariskiClosed x)

public theorem MorphicAction.pointStabilizer_toSubgroup
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X) :
    (A.pointStabilizer x).toSubgroup =
      (@MulAction.stabilizer
        (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x) := rfl

public theorem MorphicAction.mem_pointStabilizer
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] {X : Geometric k}
    (A : MorphicAction G X) (x : Point X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    g ∈ (A.pointStabilizer x).toSubgroup ↔ A.toMulAction.smul g x = x := by
  change g ∈ (@MulAction.stabilizer
      (Theory.AlgebraicGroup.Variety.Point G) (Point X) _ A.toMulAction x) ↔
    A.toMulAction.smul g x = x
  rfl

end Theory.AlgebraicGroup.Variety.Geometric
