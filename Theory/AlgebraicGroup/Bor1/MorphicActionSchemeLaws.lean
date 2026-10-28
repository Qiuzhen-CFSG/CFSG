module

public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.AffineGroupScheme

/-!
# Scheme laws for morphic actions

A morphic action of an affine algebraic group on a geometric variety restricts,
at each rational group point, to a regular self-map of the variety.  This module
proves that these translations satisfy the unit and multiplication laws as
scheme morphisms and that translation by the inverse group point is an inverse
morphism.  Consequently every translation is a scheme automorphism.

The essential input is the public action morphism and its rational-point formula.
The point-level action laws give the desired identities on rational points; since
the schemes are reduced and of finite type over an algebraically closed field,
Mathlib's closed-point extensionality promotes those identities to scheme
morphisms.  The resulting homeomorphisms transport rational orbit supports and
their Zariski closures.  The smooth locus is stable because smooth loci pull back
along scheme isomorphisms.

This is the translation package used in the orbit-geometry arguments surrounding
Borovoi, *Linear Algebraic Groups*, Chapter 1, Proposition 1.8.  The affine group
scheme realization is supplied by `ofAffine_grpObj`; quotient descent and
stabilizer arguments belong to later modules.
-/

set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem Morphism.eq_of_apply_eq
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

namespace MorphicAction

/-- Translation of `X` by a fixed rational point of the acting group. -/
public noncomputable def translationMorphism
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) : Morphism X X :=
  (Morphism.rightSection (ofAffine G) X ((affinePointEquiv G).symm g)).comp
    A.actionMorphism

@[simp]
public theorem translationMorphism_apply
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X) :
    A.translationMorphism g x = A.toMulAction.smul g x := by
  unfold translationMorphism
  rw [Morphism.comp_apply_point, Morphism.rightSection_apply]
  exact A.actionMorphism_apply g x

public theorem translationMorphism_one
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) :
    A.translationMorphism 1 = Morphism.id X := by
  apply Morphism.eq_of_apply_eq
  intro x
  rw [translationMorphism_apply, Morphism.id_apply_point]
  exact A.toMulAction.one_smul x

public theorem translationMorphism_mul
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g h : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism.comp (A.translationMorphism h) (A.translationMorphism g) =
      A.translationMorphism (g * h) := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  apply Morphism.eq_of_apply_eq
  intro x
  rw [Morphism.comp_apply_point, translationMorphism_apply,
    translationMorphism_apply, translationMorphism_apply]
  exact (mul_smul g h x).symm

public theorem translationMorphism_comp_inv
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism.comp (A.translationMorphism g) (A.translationMorphism g⁻¹) =
      Morphism.id X := by
  rw [A.translationMorphism_mul]
  simp only [inv_mul_cancel]
  exact A.translationMorphism_one

public theorem translationMorphism_inv_comp
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism.comp (A.translationMorphism g⁻¹) (A.translationMorphism g) =
      Morphism.id X := by
  rw [A.translationMorphism_mul]
  simp only [mul_inv_cancel]
  exact A.translationMorphism_one

/-- Translation by `g` is a scheme automorphism with inverse translation by `g⁻¹`. -/
@[expose]
public noncomputable def translationIso
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) : X.toScheme ≅ X.toScheme where
  hom := (A.translationMorphism g).hom
  inv := (A.translationMorphism g⁻¹).hom
  hom_inv_id := congrArg Morphism.hom (A.translationMorphism_comp_inv g)
  inv_hom_id := congrArg Morphism.hom (A.translationMorphism_inv_comp g)

@[simp]
public theorem translationIso_hom
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationIso g).hom = (A.translationMorphism g).hom := rfl

@[simp]
public theorem translationIso_inv
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationIso g).inv = (A.translationMorphism g⁻¹).hom := rfl

/-- On underlying scheme points, translation carries the closed point of x
to the closed point of g acting on x. -/
public theorem translationMorphism_hom_closedPoint
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X) :
    (A.translationMorphism g).hom
        (x.1 (IsLocalRing.closedPoint k)) =
      (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) := by
  have h := congrArg
    (fun y : Point X => y.1 (IsLocalRing.closedPoint k))
    (A.translationMorphism_apply g x)
  calc
    (A.translationMorphism g).hom
        (x.1 (IsLocalRing.closedPoint k)) =
      (x.1 ≫ (A.translationMorphism g).hom)
        (IsLocalRing.closedPoint k) :=
          (Scheme.Hom.comp_apply x.1 (A.translationMorphism g).hom _).symm
    _ = (A.toMulAction.smul g x).1
        (IsLocalRing.closedPoint k) := h

/-- The support in the underlying scheme of a set of rational points. -/
public noncomputable def rationalPointSupport {X : Geometric k}
    (S : Set (Point X)) : Set X.toScheme :=
  (fun x : Point X => x.1 (IsLocalRing.closedPoint k)) '' S

omit [IsAlgClosed k] in
/-- The support of rational points is their image on the underlying scheme. -/
public theorem rationalPointSupport_eq_closedPoint_image {X : Geometric k}
    (S : Set (Point X)) :
    rationalPointSupport S =
      (fun x : Point X => x.1 (IsLocalRing.closedPoint k)) '' S := by
  rfl

/-- Translation transports rational-point support to the support of the
pointwise translated set. -/
public theorem translationMorphism_image_rationalPointSupport
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (S : Set (Point X)) :
    (A.translationMorphism g).hom '' rationalPointSupport S =
      rationalPointSupport
        ((fun x => A.toMulAction.smul g x) '' S) := by
  rw [rationalPointSupport, rationalPointSupport,
    Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  exact A.translationMorphism_hom_closedPoint g x

/-- The underlying support of the rational-point orbit of x. -/
public noncomputable def orbitSupport
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set X.toScheme :=
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  rationalPointSupport
    (MulAction.orbit (Theory.AlgebraicGroup.Variety.Point G) x)

/-- The orbit support is the support of the explicit rational-point orbit range. -/
public theorem orbitSupport_eq_rationalPointSupport_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    A.orbitSupport x =
      rationalPointSupport
        (Set.range (fun g : Theory.AlgebraicGroup.Variety.Point G =>
          A.toMulAction.smul g x)) := by
  unfold orbitSupport
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  simp only [MulAction.orbit]
  congr 1

/-- The closed support obtained as the Zariski closure of a rational-point
orbit. -/
public noncomputable def orbitClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Closeds X.toScheme :=
  ⟨closure (A.orbitSupport x), isClosed_closure⟩

/-- Every translation preserves the underlying support of an orbit. -/
public theorem translationMorphism_image_orbitSupport
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X) :
    (A.translationMorphism g).hom '' A.orbitSupport x =
      A.orbitSupport x := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  rw [orbitSupport, A.translationMorphism_image_rationalPointSupport]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact MulAction.mem_orbit_of_mem_orbit g hz
  · intro hy
    refine ⟨g⁻¹ • y, MulAction.mem_orbit_of_mem_orbit g⁻¹ hy, ?_⟩
    exact smul_inv_smul g y

/-- A scheme translation commutes with taking topological closure. -/
public theorem translationMorphism_image_closure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (S : Set X.toScheme) :
    (A.translationMorphism g).hom '' closure S =
      closure ((A.translationMorphism g).hom '' S) := by
  rw [← A.translationIso_hom g]
  simpa only [Scheme.coe_homeoOfIso] using
    (Scheme.homeoOfIso (A.translationIso g)).image_closure S

/-- Every translation preserves the Zariski closure of a rational-point
orbit. -/
public theorem translationMorphism_image_orbitClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X) :
    (A.translationMorphism g).hom '' (A.orbitClosure x : Set X.toScheme) =
      (A.orbitClosure x : Set X.toScheme) := by
  change (A.translationMorphism g).hom '' closure (A.orbitSupport x) =
    closure (A.orbitSupport x)
  rw [A.translationMorphism_image_closure,
    A.translationMorphism_image_orbitSupport]

/-- The smooth locus of X over k is preserved under inverse image by every
translation. -/
public theorem translationMorphism_preimage_smoothLocus
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom ⁻¹ᵁ X.structureMap.smoothLocus =
      X.structureMap.smoothLocus := by
  let e := A.translationIso g
  letI : IsIso (A.translationMorphism g).hom := by
    change IsIso e.hom
    infer_instance
  simpa only [(A.translationMorphism g).commutes] using
    (Scheme.Hom.preimage_smoothLocus_eq
      (A.translationMorphism g).hom X.structureMap)

/-- Every translation preserves the underlying support of the smooth locus of
X over k. -/
public theorem translationMorphism_image_smoothLocus
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom ''
        (X.structureMap.smoothLocus : Set X.toScheme) =
      (X.structureMap.smoothLocus : Set X.toScheme) := by
  let e := A.translationIso g
  have hpre :
      (A.translationMorphism g).hom ⁻¹'
          (X.structureMap.smoothLocus : Set X.toScheme) =
        (X.structureMap.smoothLocus : Set X.toScheme) := by
    rw [← Scheme.Hom.coe_preimage]
    exact congrArg SetLike.coe (A.translationMorphism_preimage_smoothLocus g)
  calc
    (A.translationMorphism g).hom ''
        (X.structureMap.smoothLocus : Set X.toScheme) =
      (A.translationMorphism g).hom ''
        ((A.translationMorphism g).hom ⁻¹'
          (X.structureMap.smoothLocus : Set X.toScheme)) := by
        rw [hpre]
    _ = (X.structureMap.smoothLocus : Set X.toScheme) :=
      Set.image_preimage_eq _
        (by
          change Function.Surjective e.hom
          exact (Scheme.homeoOfIso e).surjective)

end MorphicAction

end Theory.AlgebraicGroup.Variety.Geometric
