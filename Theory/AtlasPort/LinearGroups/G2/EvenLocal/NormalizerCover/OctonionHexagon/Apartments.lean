module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CoordinateFrame
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.CycleExtraction
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.CoordinateCalculations
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.PathNormalization
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.PrefixCompletion

/-!
# Normalization of intrinsic octonion twelve-cycles

Cycle extraction gives six distinct singular points and zero-product planes.
The conjugating automorphism can then be constructed in two steps: normalize
the first four points to basis lines 0, 1, 5, 7, then normalize the remaining
two using a root element fixing those four lines. The actual cyclic order of
the coordinate points is 0, 1, 5, 7, 6, 2.

The geometric normalization proofs establish all nonzero denominators from
point and line distinctness. Inverting the composite automorphism places all
six coordinate points on the original cycle. This proves the containment
over every field, in particular for the finite fields of characteristic two
used in the quasithin application.

Source context: Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4, repeated
as Theorem 0.1.1 on pp.481--482. The imported licensed ATLAS port defines the
actual split-octonion automorphism model throughout.
-/

public section

open Atlas.G2

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]
open Apartments

/-- Conditional assembly of the two coordinate calculations with cycle extraction.
The two normalization premises must be proved in the actual automorphism model. -/
theorem cycle_contains_coordinatePoints_of_prefix_normalization
    (hprefix : ∀ H : PointHexagon F, ∃ g : Model F, HasCoordinatePrefix (H.map g))
    (hcompletion : ∀ H : PointHexagon F, HasCoordinatePrefix H →
      ∃ g : Model F, ∀ i : Fin 6, ∃ j : Fin 6, g • H.point j = coordinatePoint i)
    {x : GeometryVertex F} (w : geometryGraph.Walk x x)
    (hw : w.IsCycle) (hl : w.length = 12) :
    ∃ g : Model F, ∀ i : Fin 6,
      g • (Sum.inr (coordinatePoint i) : GeometryVertex F) ∈ w.support := by
  obtain ⟨H,hpoints,_⟩ := exists_pointHexagon_of_cycle w hw hl
  obtain ⟨a,ha⟩ := hprefix H
  obtain ⟨b,hb⟩ := hcompletion (H.map a) ha
  refine ⟨(b * a)⁻¹, ?_⟩
  intro i
  obtain ⟨j,hj⟩ := hb i
  have he : (b * a)⁻¹ • coordinatePoint (F := F) i = H.point j := by
    rw [← hj, PointHexagon.map_point, ← SemigroupAction.mul_smul b a, inv_smul_smul]
  change (Sum.inr ((b * a)⁻¹ • coordinatePoint i) : GeometryVertex F) ∈ w.support
  rw [he]
  exact hpoints j

/-- Every twelve-cycle in the intrinsic octonion incidence graph contains a
translate of the six singular coordinate points under an actual split-octonion
automorphism. The coordinate normalization works over every field. -/
theorem cycle_contains_coordinatePoints
    {x : GeometryVertex F} (w : geometryGraph.Walk x x)
    (hw : w.IsCycle) (hl : w.length = 12) :
    ∃ g : Model F, ∀ i : Fin 6,
      g • (Sum.inr (coordinatePoint i) : GeometryVertex F) ∈ w.support :=
  cycle_contains_coordinatePoints_of_prefix_normalization
    normalize_prefix complete_coordinate_prefix w hw hl

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
