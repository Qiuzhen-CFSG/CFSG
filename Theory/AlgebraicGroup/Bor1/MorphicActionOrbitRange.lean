module

public import Theory.AlgebraicGroup.Bor1.MorphicActionSchemeLaws
public import Theory.AlgebraicGroup.Variety.ClosedLocus
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage

/-!
# Equivariance of morphic-action orbit ranges

For a morphic action, translating the target after the orbit morphism at `x`
equals precomposing by left translation on the affine group scheme.  The proof
checks the action law on rational points and promotes it to a scheme-morphism
identity by closed-point extensionality.  Affine left translations by `g` and
`g⁻¹` are inverse, so the underlying scheme-point range of the orbit morphism
is translation-stable, as is its topological closure.

The closure is equipped with its reduced scheme-theoretic image structure.
Target translations restrict to this carrier; the restrictions for `g` and
`g⁻¹` are inverse and hence preserve its smooth locus.  This is the precise
translation package used in the orbit-smoothness proof surrounding Borovoi,
*Linear Algebraic Groups*, Chapter 1, Proposition 1.8.  It uses no quotient
descent and does not identify the scheme-point range with the separately
defined rational-point orbit support.
-/

set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace MorphicAction

omit [IsAlgClosed k] in
private theorem leftMulMorphism_inv_comp
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹).comp
        (Theory.AlgebraicGroup.leftMulMorphism G g) =
      Theory.AlgebraicGroup.Variety.Morphism.id G := by
  apply Theory.AlgebraicGroup.Variety.Morphism.ext
  funext h
  simp only [Theory.AlgebraicGroup.Variety.Morphism.comp,
    Theory.AlgebraicGroup.leftMulMorphism_apply,
    Theory.AlgebraicGroup.Variety.Morphism.id]
  simp

omit [IsAlgClosed k] in
private theorem leftMulMorphism_comp_inv
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (Theory.AlgebraicGroup.leftMulMorphism G g).comp
        (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹) =
      Theory.AlgebraicGroup.Variety.Morphism.id G := by
  apply Theory.AlgebraicGroup.Variety.Morphism.ext
  funext h
  simp only [Theory.AlgebraicGroup.Variety.Morphism.comp,
    Theory.AlgebraicGroup.leftMulMorphism_apply,
    Theory.AlgebraicGroup.Variety.Morphism.id]
  simp

private noncomputable def sourceLeftTranslationIso
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (ofAffine G).toScheme ≅ (ofAffine G).toScheme where
  hom := (ofAffine_morphism
    (Theory.AlgebraicGroup.leftMulMorphism G g)).hom
  inv := (ofAffine_morphism
    (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹)).hom
  hom_inv_id := by
    have h := congrArg Morphism.hom
      (ofAffine_morphism_comp
        (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹)
        (Theory.AlgebraicGroup.leftMulMorphism G g))
    rw [leftMulMorphism_inv_comp, ofAffine_morphism_id] at h
    exact h.symm
  inv_hom_id := by
    have h := congrArg Morphism.hom
      (ofAffine_morphism_comp
        (Theory.AlgebraicGroup.leftMulMorphism G g)
        (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹))
    rw [leftMulMorphism_comp_inv, ofAffine_morphism_id] at h
    exact h.symm

private theorem morphism_eq_of_point_eq
    {V W : Geometric k} (f g : Morphism V W)
    (h : ∀ x : Point V, f x = g x) : f = g := by
  letI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  apply Morphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq W.structureMap
      (Set.univ : Set V.toScheme) isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Point V :=
      ⟨pointOfClosedPoint V.structureMap x hx,
        pointOfClosedPoint_comp V.structureMap x hx⟩
    have hp : p.1 (IsLocalRing.closedPoint k) = x := by
      exact pointOfClosedPoint_apply V.structureMap x hx _
    calc
      f.hom x = f.hom (p.1 (IsLocalRing.closedPoint k)) := congrArg f.hom hp.symm
      _ = g.hom (p.1 (IsLocalRing.closedPoint k)) := by
        change (f p).1 (IsLocalRing.closedPoint k) =
          (g p).1 (IsLocalRing.closedPoint k)
        rw [h p]
      _ = g.hom x := congrArg g.hom hp
  · exact f.commutes.trans g.commutes.symm

omit [IsAlgClosed k] in
/-- A map from a reduced geometric variety factors through a reduced closed
subvariety as soon as its underlying range lands in the closed support. -/
private noncomputable def restrictToClosedSubvariety
    {V W : Geometric k} (C : ClosedSubvariety V) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) :
    Morphism W C.toGeometric := by
  haveI : QuasiCompact (f.hom ≫ V.structureMap) :=
    f.commutes.symm ▸ inferInstance
  letI : QuasiCompact f.hom := QuasiCompact.of_comp f.hom V.structureMap
  let Z : Closeds V.toScheme :=
    ⟨Set.range C.inclusion.hom,
      C.inclusion.hom.isClosedEmbedding.isClosed_range⟩
  have hvanish : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.hom.ker :=
    vanishingIdeal_le_ker_of_isReduced Z f.hom hf
  have hCvanish : C.inclusion.hom.ker ≤
      Scheme.IdealSheafData.vanishingIdeal Z := by
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    exact C.inclusion.hom.range_subset_ker_support
  have hker : C.inclusion.hom.ker ≤ f.hom.ker := hCvanish.trans hvanish
  exact
    { hom := IsClosedImmersion.lift C.inclusion.hom f.hom hker
      commutes := by
        rw [← C.inclusion.commutes, ← Category.assoc,
          IsClosedImmersion.lift_fac, f.commutes] }

omit [IsAlgClosed k] in
@[simp]
private theorem restrictToClosedSubvariety_inclusion
    {V W : Geometric k} (C : ClosedSubvariety V) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) :
    Morphism.comp (restrictToClosedSubvariety C f hf) C.inclusion = f := by
  apply Morphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- Target translation after the orbit morphism is source left translation
before the orbit morphism. -/
public theorem translationMorphism_comp_orbitMorphismAt
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism.comp (A.orbitMorphismAt x) (A.translationMorphism g) =
      Morphism.comp
        (ofAffine_morphism (Theory.AlgebraicGroup.leftMulMorphism G g))
        (A.orbitMorphismAt x) := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  apply morphism_eq_of_point_eq
  intro h
  rw [Morphism.comp_apply_point, Morphism.comp_apply_point]
  let p : Theory.AlgebraicGroup.Variety.Point G := affinePointEquiv G h
  have hp : h = (affinePointEquiv G).symm p := by
    exact ((affinePointEquiv G).symm_apply_apply h).symm
  have hsource :
      ofAffine_morphism (Theory.AlgebraicGroup.leftMulMorphism G g) h =
        (affinePointEquiv G).symm (g * p) := by
    apply (affinePointEquiv G).injective
    rw [affinePointEquiv_ofAffine_morphism]
    simp only [Equiv.apply_symm_apply]
    exact Theory.AlgebraicGroup.leftMulMorphism_apply G g p
  have horbit : A.orbitMorphismAt x h = A.toMulAction.smul p x := by
    rw [hp, A.orbitMorphismAt_apply]
  have h1 :
      A.translationMorphism g (A.orbitMorphismAt x h) =
        A.toMulAction.smul g (A.orbitMorphismAt x h) :=
    A.translationMorphism_apply g _
  have h2 :
      A.toMulAction.smul g (A.orbitMorphismAt x h) =
        A.toMulAction.smul g (A.toMulAction.smul p x) :=
    congrArg (A.toMulAction.smul g) horbit
  have h3 :
      A.toMulAction.smul g (A.toMulAction.smul p x) =
        A.toMulAction.smul (g * p) x :=
    (mul_smul g p x).symm
  have h4 :
      A.toMulAction.smul (g * p) x =
        A.orbitMorphismAt x ((affinePointEquiv G).symm (g * p)) :=
    (A.orbitMorphismAt_apply x (g * p)).symm
  have h5 :
      A.orbitMorphismAt x ((affinePointEquiv G).symm (g * p)) =
        A.orbitMorphismAt x
          (ofAffine_morphism (Theory.AlgebraicGroup.leftMulMorphism G g) h) :=
    congrArg (A.orbitMorphismAt x) hsource.symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Translation preserves the underlying scheme-point range of an orbit
morphism exactly. -/
public theorem translationMorphism_image_orbitMorphismAt_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom '' Set.range (A.orbitMorphismAt x).hom =
      Set.range (A.orbitMorphismAt x).hom := by
  let Lg := ofAffine_morphism
    (Theory.AlgebraicGroup.leftMulMorphism G g)
  have hequiv := congrArg Morphism.hom
    (A.translationMorphism_comp_orbitMorphismAt x g)
  have hsurj : Function.Surjective Lg.hom := by
    change Function.Surjective (sourceLeftTranslationIso g).hom
    exact (Scheme.homeoOfIso (sourceLeftTranslationIso g)).surjective
  ext y
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨Lg.hom z, ?_⟩
    have h := congrArg (fun q => q z) hequiv
    simpa only [Morphism.comp, Scheme.Hom.comp_apply] using h.symm
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hsurj z
    refine ⟨(A.orbitMorphismAt x).hom w, ⟨w, rfl⟩, ?_⟩
    have h := congrArg (fun q => q w) hequiv
    change (A.translationMorphism g).hom ((A.orbitMorphismAt x).hom w) =
      (A.orbitMorphismAt x).hom (Lg.hom w) at h
    rw [hw] at h
    exact h

/-- Translation preserves the topological closure of the scheme-point orbit
range. -/
public theorem translationMorphism_image_orbitMorphismAt_rangeClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom ''
        closure (Set.range (A.orbitMorphismAt x).hom) =
      closure (Set.range (A.orbitMorphismAt x).hom) := by
  rw [A.translationMorphism_image_closure,
    A.translationMorphism_image_orbitMorphismAt_range]

/-- The reduced scheme-theoretic range closure of the orbit morphism. -/
@[expose]
public noncomputable def orbitMorphismRangeClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    ClosedSubvariety X :=
  (A.orbitMorphismAt x).schemeTheoreticRangeClosure

/-- The reduced orbit-range closure has the expected topological support. -/
@[simp]
public theorem orbitMorphismRangeClosure_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set.range (A.orbitMorphismRangeClosure x).inclusion.hom =
      closure (Set.range (A.orbitMorphismAt x).hom) := by
  unfold orbitMorphismRangeClosure
  exact (A.orbitMorphismAt x).range_schemeTheoreticRangeClosure_inclusion

/-- Ambient translation preserves the support of the reduced orbit-range
closure. -/
public theorem translationMorphism_image_orbitMorphismRangeClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom ''
        Set.range (A.orbitMorphismRangeClosure x).inclusion.hom =
      Set.range (A.orbitMorphismRangeClosure x).inclusion.hom := by
  rw [A.orbitMorphismRangeClosure_range,
    A.translationMorphism_image_orbitMorphismAt_rangeClosure]

/-- Translation restricted to the canonical reduced orbit-range closure. -/
public noncomputable def orbitMorphismRangeClosureTranslation
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism (A.orbitMorphismRangeClosure x).toGeometric
      (A.orbitMorphismRangeClosure x).toGeometric := by
  apply restrictToClosedSubvariety (A.orbitMorphismRangeClosure x)
    (Morphism.comp
      (A.orbitMorphismRangeClosure x).inclusion
      (A.translationMorphism g))
  rintro _ ⟨z, rfl⟩
  change (A.translationMorphism g).hom
      ((A.orbitMorphismRangeClosure x).inclusion.hom z) ∈
    Set.range (A.orbitMorphismRangeClosure x).inclusion.hom
  have hz : (A.orbitMorphismRangeClosure x).inclusion.hom z ∈
      closure (Set.range (A.orbitMorphismAt x).hom) := by
    rw [← A.orbitMorphismRangeClosure_range x]
    exact Set.mem_range_self z
  rw [A.orbitMorphismRangeClosure_range,
    ← A.translationMorphism_image_orbitMorphismAt_rangeClosure x g]
  exact ⟨_, hz, rfl⟩

/-- Restricted translation followed by the carrier inclusion is ambient
translation after the inclusion. -/
@[simp]
public theorem orbitMorphismRangeClosureTranslation_inclusion
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism.comp (A.orbitMorphismRangeClosureTranslation x g)
        (A.orbitMorphismRangeClosure x).inclusion =
      Morphism.comp (A.orbitMorphismRangeClosure x).inclusion
        (A.translationMorphism g) := by
  unfold orbitMorphismRangeClosureTranslation
  exact restrictToClosedSubvariety_inclusion _ _ _

/-- Restricted translation by `g` is an automorphism, with inverse the
restriction of translation by `g⁻¹`. -/
@[expose]
public noncomputable def orbitMorphismRangeClosureTranslationIso
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitMorphismRangeClosure x).toGeometric.toScheme ≅
      (A.orbitMorphismRangeClosure x).toGeometric.toScheme where
  hom := (A.orbitMorphismRangeClosureTranslation x g).hom
  inv := (A.orbitMorphismRangeClosureTranslation x g⁻¹).hom
  hom_inv_id := by
    let C := A.orbitMorphismRangeClosure x
    apply (cancel_mono C.inclusion.hom).mp
    have hg := congrArg Morphism.hom
      (A.orbitMorphismRangeClosureTranslation_inclusion x g)
    have hinv := congrArg Morphism.hom
      (A.orbitMorphismRangeClosureTranslation_inclusion x g⁻¹)
    have hcancel := congrArg Morphism.hom
      (A.translationMorphism_comp_inv g)
    change (A.orbitMorphismRangeClosureTranslation x g).hom ≫
        C.inclusion.hom = C.inclusion.hom ≫
          (A.translationMorphism g).hom at hg
    change (A.orbitMorphismRangeClosureTranslation x g⁻¹).hom ≫
        C.inclusion.hom = C.inclusion.hom ≫
          (A.translationMorphism g⁻¹).hom at hinv
    change (A.translationMorphism g).hom ≫
        (A.translationMorphism g⁻¹).hom = 𝟙 X.toScheme at hcancel
    rw [Category.assoc, hinv, ← Category.assoc, hg, Category.assoc,
      hcancel, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    let C := A.orbitMorphismRangeClosure x
    apply (cancel_mono C.inclusion.hom).mp
    have hg := congrArg Morphism.hom
      (A.orbitMorphismRangeClosureTranslation_inclusion x g)
    have hinv := congrArg Morphism.hom
      (A.orbitMorphismRangeClosureTranslation_inclusion x g⁻¹)
    have hcancel := congrArg Morphism.hom
      (A.translationMorphism_inv_comp g)
    change (A.orbitMorphismRangeClosureTranslation x g).hom ≫
        C.inclusion.hom = C.inclusion.hom ≫
          (A.translationMorphism g).hom at hg
    change (A.orbitMorphismRangeClosureTranslation x g⁻¹).hom ≫
        C.inclusion.hom = C.inclusion.hom ≫
          (A.translationMorphism g⁻¹).hom at hinv
    change (A.translationMorphism g⁻¹).hom ≫
        (A.translationMorphism g).hom = 𝟙 X.toScheme at hcancel
    rw [Category.assoc, hg, ← Category.assoc, hinv, Category.assoc,
      hcancel, Category.comp_id, Category.id_comp]

/-- Restricted translation preserves the smooth locus of the reduced
orbit-range closure under inverse image. -/
public theorem orbitMorphismRangeClosureTranslation_preimage_smoothLocus
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitMorphismRangeClosureTranslation x g).hom ⁻¹ᵁ
        (A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus =
      (A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus := by
  let e := A.orbitMorphismRangeClosureTranslationIso x g
  letI : IsIso (A.orbitMorphismRangeClosureTranslation x g).hom := by
    change IsIso e.hom
    infer_instance
  simpa only [(A.orbitMorphismRangeClosureTranslation x g).commutes] using
    (Scheme.Hom.preimage_smoothLocus_eq
      (A.orbitMorphismRangeClosureTranslation x g).hom
      (A.orbitMorphismRangeClosure x).toGeometric.structureMap)

/-- Restricted translation preserves the underlying set of the smooth locus
of the reduced orbit-range closure. -/
public theorem orbitMorphismRangeClosureTranslation_image_smoothLocus
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitMorphismRangeClosureTranslation x g).hom ''
        ((A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus :
          Set (A.orbitMorphismRangeClosure x).toGeometric.toScheme) =
      (A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus := by
  let e := A.orbitMorphismRangeClosureTranslationIso x g
  have hpre :
      (A.orbitMorphismRangeClosureTranslation x g).hom ⁻¹'
          ((A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus :
            Set (A.orbitMorphismRangeClosure x).toGeometric.toScheme) =
        (A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus := by
    rw [← Scheme.Hom.coe_preimage]
    exact congrArg SetLike.coe
      (A.orbitMorphismRangeClosureTranslation_preimage_smoothLocus x g)
  calc
    (A.orbitMorphismRangeClosureTranslation x g).hom ''
        ((A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus :
          Set (A.orbitMorphismRangeClosure x).toGeometric.toScheme) =
      (A.orbitMorphismRangeClosureTranslation x g).hom ''
        ((A.orbitMorphismRangeClosureTranslation x g).hom ⁻¹'
          ((A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus :
            Set (A.orbitMorphismRangeClosure x).toGeometric.toScheme)) := by
        rw [hpre]
    _ = (A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus :=
      Set.image_preimage_eq _ (by
        change Function.Surjective e.hom
        exact (Scheme.homeoOfIso e).surjective)

end MorphicAction

end Theory.AlgebraicGroup.Variety.Geometric
