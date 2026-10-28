module

public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.ClosedLocus
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage

/-!
# Fixed-point incidence and completeness

For a regular action of an affine algebraic group on a geometric variety `X`,
the pairs `(g, x)` satisfying `g • x = x` form a reduced closed equalizer in
`G × X`. Its projection has exactly the elements with a rational fixed point
as its rational-point image. If `X` is complete, this projection has closed
image, including on the presented affine group's Zariski points.

This supplies the incidence and closed-image steps of Borel, *Linear Algebraic
Groups*, §11.9(1), `refs/KGroup/Bor1/Chapter4.tex`. It uses genuine universal
closedness and the rational-point/scheme-point range comparison; it does not
assert density or existence of fixed points.
-/

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The reduced closed variety of pairs `(g, x)` with `g • x = x`. -/
@[expose] public noncomputable def fixedPointIncidence {X : Variety.Geometric k}
    (A : MorphicAction G X) : ClosedSubvariety (Variety.Geometric.prod (ofAffine G) X) :=
  reducedEqualizer A.actionMorphism (snd (ofAffine G) X)

/-- Projection of the fixed-point incidence variety to the acting group. -/
@[expose] public noncomputable def incidenceProjection {X : Variety.Geometric k}
    (A : MorphicAction G X) :
    Variety.Geometric.Morphism (fixedPointIncidence A).toGeometric (ofAffine G) :=
  (fixedPointIncidence A).inclusion.comp (fst (ofAffine G) X)

/-- The incidence projection has exactly the group elements fixing a rational point as its image. -/
public theorem mem_incidenceProjection_range_iff {X : Variety.Geometric k}
    (A : MorphicAction G X) (g : Variety.Point G) :
    (affinePointEquiv G).symm g ∈ Set.range (incidenceProjection A) ↔
      ∃ x : Point X, A.toMulAction.smul g x = x := by
  constructor
  · rintro ⟨z, hz⟩
    let y : Point (Variety.Geometric.prod (ofAffine G) X) :=
      (fixedPointIncidence A).inclusion z
    have hfix : A.actionMorphism y = snd (ofAffine G) X y := by
      exact (point_mem_reducedEqualizer_iff _ _ y).mpr
        ⟨z, rfl, fun w hw => by
          apply Subtype.ext
          exact (cancel_mono (fixedPointIncidence A).inclusion.hom).mp
            (congrArg Subtype.val hw)⟩
    have hy : y = prodPoint ((affinePointEquiv G).symm g) (snd (ofAffine G) X y) := by
      have heq := (prodPointEquiv (ofAffine G) X).symm_apply_apply y
      change prodPoint (fst (ofAffine G) X y) (snd (ofAffine G) X y) = y at heq
      rw [show fst (ofAffine G) X y = (affinePointEquiv G).symm g from hz] at heq
      exact heq.symm
    refine ⟨snd (ofAffine G) X y, ?_⟩
    exact (A.actionMorphism_apply g _).symm.trans
      ((congrArg A.actionMorphism hy.symm).trans hfix)
  · rintro ⟨x, hx⟩
    have heq : A.actionMorphism (prodPoint ((affinePointEquiv G).symm g) x) =
        snd (ofAffine G) X (prodPoint ((affinePointEquiv G).symm g) x) := by
      rw [A.actionMorphism_apply, snd_prodPoint, hx]
    obtain ⟨z, hz, -⟩ := (point_mem_reducedEqualizer_iff _ _ _).mp heq
    refine ⟨z, ?_⟩
    change fst (ofAffine G) X ((fixedPointIncidence A).inclusion z) = _
    exact (congrArg (fst (ofAffine G) X) hz).trans (fst_prodPoint _ _)

/-- Completeness of the acted-on variety makes the incidence projection image closed. -/
public theorem incidenceProjection_isClosed_range {X : Variety.Geometric k}
    (A : MorphicAction G X) (hX : IsComplete X) :
    IsClosed (Set.range (incidenceProjection A).hom) := by
  have hproj := (isComplete_iff_projection_isClosedMap X).mp hX
    (ofAffine G).toScheme (ofAffine G).structureMap
  have h := hproj (Set.range (fixedPointIncidence A).inclusion.hom)
    (fixedPointIncidence A).inclusion.hom.isClosedEmbedding.isClosed_range
  change IsClosed (Set.range ((fixedPointIncidence A).inclusion.hom ≫
    (fst (ofAffine G) X).hom))
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact h

/-- For an action on a complete variety, the elements having a fixed point form a Zariski closed set. -/
public theorem isZariskiClosed_has_fixedPoint {X : Variety.Geometric k}
    (A : MorphicAction G X) (hX : IsComplete X) :
    IsZariskiClosed G {g : Variety.Point G | ∃ x : Point X, A.toMulAction.smul g x = x} := by
  have h := isZariskiClosed_ofAffine_closedPoint_preimage
    (G := G) (Set.range (incidenceProjection A).hom)
    (incidenceProjection_isClosed_range A hX)
  convert h using 1
  ext g
  exact (mem_incidenceProjection_range_iff A g).symm.trans
    ((incidenceProjection A).point_mem_range_iff_closedPoint_mem_range _)

end Theory.AlgebraicGroup.BorelElementCoverage
