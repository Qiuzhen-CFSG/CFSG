module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.StabilizerFiber
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.DimensionBridge
public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitGeometry
import all Theory.AlgebraicGroup.Bor1.MorphicActionOrbitGeometry

/-!
# The orbit map onto its locally closed carrier

The existing orbit morphism factors through the open orbit in its reduced
closure. The factor is surjective on scheme points and rational points.
Its scheme fibres are homeomorphic to those of the original orbit map, hence
to the actual reduced point stabilizer over rational points. Translations
restrict to homeomorphisms and act transitively on the closed points.

Only underlying spaces of fibres are compared: no reducedness or separability
of the orbit morphism is assumed. This supplies the geometric input for the
orbit dimension argument in Borel, *Linear Algebraic Groups*, §§1.8 and 11.1
(`refs/KGroup/Bor1/Chapter1.tex` and `Chapter4.tex`). The internal import is an
intentional continuation of the existing orbit-carrier construction.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology
open Theory.AlgebraicGroup

universe u
namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

/-- The actual orbit morphism, with codomain restricted to its locally closed carrier. -/
public noncomputable def toOrbitSubvariety :
    Morphism (ofAffine G) (A.orbitSubvariety x).toGeometric :=
  restrictToOpenSubvariety
    ⟨Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom,
      A.orbitRangeClosure_range_isOpen x⟩
    (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure (Set.Subset.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion recovers the original scheme orbit morphism. -/
public theorem toOrbitSubvariety_comp_inclusion :
    (A.toOrbitSubvariety x).hom ≫ (A.orbitSubvariety x).inclusion.hom =
      (A.orbitMorphismAt x).hom := by
  change (restrictToOpenSubvariety _ _ _).hom ≫
    ((orbitOpenCarrier A x).inclusion.hom ≫ (A.orbitMorphismRangeClosure x).inclusion.hom) = _
  rw [← Category.assoc]
  have h := congrArg Morphism.hom (restrictToOpenSubvariety_inclusion
    ⟨Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom,
      A.orbitRangeClosure_range_isOpen x⟩
    (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure (Set.Subset.refl _))
  change (restrictToOpenSubvariety _ _ _).hom ≫ (orbitOpenCarrier A x).inclusion.hom = _ at h
  rw [h]
  exact (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure_comp_inclusion

/-- The factor onto the orbit is surjective on all scheme points. -/
public theorem toOrbitSubvariety_surjective :
    Function.Surjective (A.toOrbitSubvariety x).hom := by
  intro z
  have hz : (A.orbitSubvariety x).inclusion.hom z ∈
      Set.range (A.orbitMorphismAt x).hom := by
    rw [← A.orbitSubvariety_range x]
    exact Set.mem_range_self _
  obtain ⟨g, hg⟩ := hz
  refine ⟨g, (A.orbitSubvariety x).inclusion.hom.isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, A.toOrbitSubvariety_comp_inclusion]
  exact hg

/-- Every rational point of the orbit is reached by a rational group element. -/
public theorem toOrbitSubvariety_surjective_points :
    Function.Surjective (A.toOrbitSubvariety x) := by
  intro y
  apply ((A.toOrbitSubvariety x).point_mem_range_iff_closedPoint_mem_range y).mpr
  exact A.toOrbitSubvariety_surjective x _

/-- Factoring through the orbit carrier preserves the underlying scheme fibres. -/
public noncomputable def toOrbitSubvarietyFiberHomeomorph
    (y : (A.orbitSubvariety x).toGeometric.toScheme) :
    (A.toOrbitSubvariety x).hom.fiber y ≃ₜ
      (A.orbitMorphismAt x).hom.fiber ((A.orbitSubvariety x).inclusion.hom y) := by
  apply ((A.toOrbitSubvariety x).hom.fiberHomeo y).trans
  apply Homeomorph.trans _ ((A.orbitMorphismAt x).hom.fiberHomeo _).symm
  apply Homeomorph.setCongr
  ext g
  change (A.toOrbitSubvariety x).hom g = y ↔
    (A.orbitMorphismAt x).hom g = (A.orbitSubvariety x).inclusion.hom y
  rw [← A.toOrbitSubvariety_comp_inclusion x, Scheme.Hom.comp_apply]
  exact (A.orbitSubvariety x).inclusion.hom.isEmbedding.injective.eq_iff.symm

/-- A rational fibre of the factored orbit map has the topology of the reduced stabilizer. -/
public noncomputable def toOrbitSubvarietyFiberStabilizerHomeomorph
    (y : Point (A.orbitSubvariety x).toGeometric) :
    (ofAffine (A.pointStabilizer x).carrierVariety).toScheme ≃ₜ
      (A.toOrbitSubvariety x).hom.fiber (y.1 (IsLocalRing.closedPoint k)) := by
  let g := (A.toOrbitSubvariety_surjective_points x y).choose
  have hg : (A.toOrbitSubvariety x) g = y :=
    (A.toOrbitSubvariety_surjective_points x y).choose_spec
  rw [← hg]
  apply Homeomorph.trans _ (A.toOrbitSubvarietyFiberHomeomorph x _).symm
  have hval : (A.orbitSubvariety x).inclusion.hom
      (((A.toOrbitSubvariety x) g).1 (IsLocalRing.closedPoint k)) =
      ((A.toMulAction.smul (affinePointEquiv G g) x).1 (IsLocalRing.closedPoint k)) := by
    have h := congrArg (fun f : (ofAffine G).toScheme ⟶ X.toScheme =>
      (g.1 ≫ f) (IsLocalRing.closedPoint k)) (A.toOrbitSubvariety_comp_inclusion x)
    change (A.orbitSubvariety x).inclusion.hom _ =
      ((A.orbitMorphismAt x) g).1 (IsLocalRing.closedPoint k) at h
    rw [show (A.orbitMorphismAt x) g = A.toMulAction.smul (affinePointEquiv G g) x from
      by simpa using A.orbitMorphismAt_apply x (affinePointEquiv G g)] at h
    exact h
  rw [hval]
  exact A.orbitFiberStabilizerHomeomorph x (affinePointEquiv G g)

/-- Every rational orbit fibre has the cardinal-valued dimension of the actual stabilizer. -/
public theorem toOrbitSubvariety_fiber_dimension
    (y : Point (A.orbitSubvariety x).toGeometric) :
    topologicalKrullDim ((A.toOrbitSubvariety x).hom.fiber
      (y.1 (IsLocalRing.closedPoint k))) =
      (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) := by
  rw [← (A.toOrbitSubvarietyFiberStabilizerHomeomorph x y).isHomeomorph.topologicalKrullDim_eq]
  exact MinimalOrbit.ofAffine_group_dimension _

/-- Translations restrict to homeomorphisms of the actual locally closed orbit. -/
public noncomputable def orbitSubvarietyTranslationHomeomorph
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitSubvariety x).toGeometric.toScheme ≃ₜ
      (A.orbitSubvariety x).toGeometric.toScheme := by
  let j := (A.orbitSubvariety x).inclusion.hom.isEmbedding.toHomeomorph
  let e := Scheme.homeoOfIso (A.translationIso g)
  have h : e '' Set.range (A.orbitSubvariety x).inclusion.hom =
      Set.range (A.orbitSubvariety x).inclusion.hom := by
    rw [A.orbitSubvariety_range]
    exact A.translationMorphism_image_orbitMorphismAt_range x g
  exact j.trans ((e.image _).trans (Homeomorph.setCongr h)) |>.trans j.symm

/-- The restricted translation agrees with ambient translation after inclusion. -/
public theorem orbitSubvarietyTranslationHomeomorph_inclusion
    (g : Theory.AlgebraicGroup.Variety.Point G)
    (y : (A.orbitSubvariety x).toGeometric.toScheme) :
    (A.orbitSubvariety x).inclusion.hom (A.orbitSubvarietyTranslationHomeomorph x g y) =
      (A.translationMorphism g).hom ((A.orbitSubvariety x).inclusion.hom y) := by
  unfold orbitSubvarietyTranslationHomeomorph
  exact congrArg Subtype.val ((A.orbitSubvariety x).inclusion.hom.isEmbedding.toHomeomorph.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
/-- The closed points of the actual orbit carrier are homogeneous. -/
public theorem orbitSubvariety_closedPoint_transitive :
    ∀ a ∈ closedPoints (A.orbitSubvariety x).toGeometric.toScheme,
      ∀ b ∈ closedPoints (A.orbitSubvariety x).toGeometric.toScheme,
        ∃ e : (A.orbitSubvariety x).toGeometric.toScheme ≃ₜ
          (A.orbitSubvariety x).toGeometric.toScheme, e a = b := by
  intro a ha b hb
  let O := A.orbitSubvariety x
  let y : Point O.toGeometric := (pointEquivClosedPoint O.toGeometric.structureMap).symm ⟨a, ha⟩
  let z : Point O.toGeometric := (pointEquivClosedPoint O.toGeometric.structureMap).symm ⟨b, hb⟩
  have hy : y.1 (IsLocalRing.closedPoint k) = a :=
    congrArg Subtype.val ((pointEquivClosedPoint O.toGeometric.structureMap).apply_symm_apply ⟨a, ha⟩)
  have hz : z.1 (IsLocalRing.closedPoint k) = b :=
    congrArg Subtype.val ((pointEquivClosedPoint O.toGeometric.structureMap).apply_symm_apply ⟨b, hb⟩)
  obtain ⟨u, hu⟩ := A.toOrbitSubvariety_surjective_points x y
  obtain ⟨v, hv⟩ := A.toOrbitSubvariety_surjective_points x z
  let uG := affinePointEquiv G u
  let vG := affinePointEquiv G v
  let g := vG * uG⁻¹
  have hinc (w : Point (ofAffine G)) :
      O.inclusion ((A.toOrbitSubvariety x) w) = (A.orbitMorphismAt x) w := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).trans (congrArg (fun f => w.1 ≫ f)
      (A.toOrbitSubvariety_comp_inclusion x))
  have hu' : O.inclusion y = A.toMulAction.smul uG x := by
    rw [← hu, hinc]
    simpa [uG] using A.orbitMorphismAt_apply x uG
  have hv' : O.inclusion z = A.toMulAction.smul vG x := by
    rw [← hv, hinc]
    simpa [vG] using A.orbitMorphismAt_apply x vG
  have hpoint : A.translationMorphism g (O.inclusion y) = O.inclusion z := by
    rw [A.translationMorphism_apply, hu', hv']
    let : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) := A.toMulAction
    change g • (uG • x) = vG • x
    simp [g, ← mul_smul]
  refine ⟨A.orbitSubvarietyTranslationHomeomorph x g, ?_⟩
  apply O.inclusion.hom.isEmbedding.injective
  rw [A.orbitSubvarietyTranslationHomeomorph_inclusion, ← hy, ← hz]
  exact congrArg (fun q : Point X => q.1 (IsLocalRing.closedPoint k)) hpoint

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
