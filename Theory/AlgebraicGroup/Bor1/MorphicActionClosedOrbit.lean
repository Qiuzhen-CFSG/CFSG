module

public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitGeometry
public import Theory.AlgebraicGroup.Bor1.MorphicActionPointStabilizer
public import Theory.AlgebraicGroup.Bor1.GeometricQuotientDescent
public import Theory.AlgebraicGroup.Variety.ReducedProduct
public import Theory.AlgebraicGroup.Variety.BijectiveNormalization

/-!
# Geometric orbit descent through affine algebraic-group quotients

For a morphic action on a reduced separated finite-type geometric variety,
the orbit morphism at a rational point descends through the affine quotient
by its stabilizer whenever the quotient data of Bor1 1.1.2(b) is available.
In particular, the normal-stabilizer quotient construction supplies exactly
the data used here. The descended morphism agrees with the action on rational
points under the canonical equivalence with the presented affine points.

The essential reduction is scheme kernel-pair invariance. Equality under the
quotient projection puts the ratio of two group points in the point stabilizer,
so their orbit images agree. The quotient projection is smooth by its
surjective identity differential. Its kernel pair is therefore smooth over the
field and reduced; closed-point extensionality promotes this point calculation
to equality of scheme morphisms. The faithfully flat quotient descent theorem
then constructs the geometric orbit morphism without adding certificates to
the action structure.

Source: Borel, *Linear Algebraic Groups* (Bor1), 1.7--1.8 for orbit maps and
stabilizers, and the quotient-to-orbit morphism in the proof of 10.4. This is the
descent step underlying the normal closed-orbit representation used there.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem affine_smooth_reduced {Z : Scheme} (q : Z ⟶ Spec (.of k))
    [IsAffine Z] [Smooth q] : IsReduced Z := by
  have hsm : q.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let φ : k →+* Γ(Z, ⊤) := q.appTop.hom.comp e.symm.toRingHom
  have hφ : φ.Smooth :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective e.symm.bijective) hsm
  letI : Algebra k Γ(Z, ⊤) := φ.toAlgebra
  letI : Algebra.Smooth k Γ(Z, ⊤) := RingHom.Smooth.toAlgebra hφ
  letI : IsReduced Γ(Z, ⊤) :=
    Bor1.isReduced_of_smooth_of_field (K := k) (A := Γ(Z, ⊤))
  exact isReduced_of_isAffine_isReduced Z

private theorem ofAffine_morphism_smooth
    {G Q : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (π : AlgebraicGroup.Morphism G Q)
    (hπ : Function.Surjective (identityTangentMorphismLinearMap π)) :
    Smooth (ofAffine_morphism π.toVariety).hom := by
  have hsm := Bor1.pullbackRingHom_smooth_of_tangent_surjective π hπ
  have hleft := RingHom.Smooth.of_bijective
    (f := (coordinateRingAlgEquivPolynomialFunction Q).toRingHom)
    (coordinateRingAlgEquivPolynomialFunction Q).bijective
  have hright := RingHom.Smooth.of_bijective
    (f := (coordinateRingAlgEquivPolynomialFunction G).symm.toRingHom)
    (coordinateRingAlgEquivPolynomialFunction G).symm.bijective
  have h := RingHom.Smooth.comp (RingHom.Smooth.comp hleft hsm) hright
  exact HasRingHomProperty.Spec_iff.mpr h

private theorem orbit_eq_of_projection_eq
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X)
    (D : Bor1.Theorem112BQuotientData (A.pointStabilizer x))
    (g h : Theory.AlgebraicGroup.Variety.Point G)
    (heq : D.projectionToVariety.toFun g = D.projectionToVariety.toFun h) :
    A.toMulAction.smul g x = A.toMulAction.smul h x := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) := A.toMulAction
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  rw [← D.projection_toVariety] at heq
  change D.projection.onPoints g = D.projection.onPoints h at heq
  have hker : g⁻¹ * h ∈ D.projection.kernel := by
    change D.projection.onPoints (g⁻¹ * h) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  rw [D.kernel_eq] at hker
  have hfix := (A.mem_pointStabilizer x (g⁻¹ * h)).mp hker
  change g • x = h • x
  calc
    g • x = g • ((g⁻¹ * h) • x) := congrArg (g • ·) hfix.symm
    _ = h • x := by rw [← mul_smul, mul_inv_cancel_left]

private theorem orbitMorphism_kernel_pair_equal
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X)
    (D : Bor1.Theorem112BQuotientData (A.pointStabilizer x)) :
    pullback.fst (Bor1.affineGeometricMorphism D.projectionToVariety).hom
        (Bor1.affineGeometricMorphism D.projectionToVariety).hom ≫
          (A.orbitMorphismAt x).hom =
      pullback.snd (Bor1.affineGeometricMorphism D.projectionToVariety).hom
        (Bor1.affineGeometricMorphism D.projectionToVariety).hom ≫
          (A.orbitMorphismAt x).hom := by
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  rw [Bor1.affineGeometricMorphism_eq_ofAffine_morphism, ← D.projection_toVariety]
  let πg := ofAffine_morphism D.projection.toVariety
  let V := ofAffine G
  let P := pullback πg.hom πg.hom
  let r : P ⟶ V.toScheme := pullback.fst πg.hom πg.hom
  let s : P ⟶ V.toScheme := pullback.snd πg.hom πg.hom
  let p : P ⟶ Spec (.of k) := r ≫ V.structureMap
  letI : Smooth πg.hom := ofAffine_morphism_smooth D.projection D.tangentSurjective
  letI : Smooth V.structureMap := ofAffine_smooth G
  letI : Smooth p := by dsimp [p, r]; infer_instance
  letI : IsAffine P := by dsimp [P, πg, ofAffine]; infer_instance
  letI : IsReduced P := affine_smooth_reduced p
  have hscomm : s ≫ V.structureMap = p := by
    dsimp [p, r, s]
    rw [← πg.commutes, ← Category.assoc, ← pullback.condition, Category.assoc]
  apply AlgebraicGeometry.ext_of_apply_eq X.structureMap
    (Set.univ : Set P) isOpen_univ.isLocallyClosed dense_univ
  · intro z _ hz
    let ρ := pointOfClosedPoint p z hz
    have hρ : ρ ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z hz
    let g : Point V := ⟨ρ ≫ r, by rw [Category.assoc]; exact hρ⟩
    let h : Point V := ⟨ρ ≫ s, by rw [Category.assoc, hscomm]; exact hρ⟩
    have hpoints : πg g = πg h := by
      apply Subtype.ext
      change (ρ ≫ r) ≫ πg.hom = (ρ ≫ s) ≫ πg.hom
      rw [Category.assoc, Category.assoc]
      exact congrArg (ρ ≫ ·) (pullback.condition (f := πg.hom) (g := πg.hom))
    have hπpoints := congrArg (affinePointEquiv D.quotient) hpoints
    rw [affinePointEquiv_ofAffine_morphism,
      affinePointEquiv_ofAffine_morphism] at hπpoints
    rw [D.projection_toVariety] at hπpoints
    have horbit := orbit_eq_of_projection_eq A x D
      (affinePointEquiv G g) (affinePointEquiv G h) hπpoints
    have hfg : (A.orbitMorphismAt x) g = (A.orbitMorphismAt x) h := by
      rw [← (affinePointEquiv G).symm_apply_apply g,
        ← (affinePointEquiv G).symm_apply_apply h,
        orbitMorphismAt_apply, orbitMorphismAt_apply]
      exact horbit
    have hzρ : ρ (IsLocalRing.closedPoint k) = z :=
      pointOfClosedPoint_apply p z hz _
    have heval := congrArg (fun y : Point X => y.1 (IsLocalRing.closedPoint k)) hfg
    change (A.orbitMorphismAt x).hom (r (ρ (IsLocalRing.closedPoint k))) =
      (A.orbitMorphismAt x).hom (s (ρ (IsLocalRing.closedPoint k))) at heval
    rw [hzρ] at heval
    exact heval
  · change (r ≫ (A.orbitMorphismAt x).hom) ≫ X.structureMap =
      (s ≫ (A.orbitMorphismAt x).hom) ≫ X.structureMap
    rw [Category.assoc, Category.assoc, (A.orbitMorphismAt x).commutes]
    exact hscomm.symm

/-- A geometric orbit map descends through the affine stabilizer quotient. -/
public theorem exists_descended_orbit_morphism
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X)
    (D : Bor1.Theorem112BQuotientData (A.pointStabilizer x)) :
    ∃ u : Morphism (ofAffine D.quotient) X,
      (Bor1.affineGeometricMorphism D.projectionToVariety).comp u =
        A.orbitMorphismAt x ∧
      ∀ g : Theory.AlgebraicGroup.Variety.Point G,
        u ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g)) =
          A.toMulAction.smul g x := by
  obtain ⟨u, hu, _⟩ := Bor1.descend_geometric_morphism_of_kernel_pair_equal
    D (A.orbitMorphismAt x) (orbitMorphism_kernel_pair_equal A x D)
  refine ⟨u, hu.1, ?_⟩
  intro g
  simpa only [orbitMorphismAt_apply] using hu.2.2 g

/-- A normal point stabilizer supplies an affine quotient and its orbit morphism. -/
public theorem exists_quotient_orbit_morphism
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X)
    (hN : (A.pointStabilizer x).toSubgroup.Normal) :
    ∃ D : Bor1.Theorem112BQuotientData (A.pointStabilizer x),
      ∃ u : Morphism (ofAffine D.quotient) X,
        (Bor1.affineGeometricMorphism D.projectionToVariety).comp u =
          A.orbitMorphismAt x ∧
        ∀ g : Theory.AlgebraicGroup.Variety.Point G,
          u ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g)) =
            A.toMulAction.smul g x := by
  let D := Bor1.theorem_1_1_2_b_quotientData (A.pointStabilizer x) hN
  exact ⟨D, exists_descended_orbit_morphism A x D⟩

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
