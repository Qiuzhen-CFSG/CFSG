module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.BinaryCover.PrefixNormalization
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Diameter
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.LineLayers
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.PointPredecessor
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

/-!
# The hexagon of the actual binary parabolic pair

The coordinate strata give diameter six and girth twelve. Normalizing the
first four points of a twelve-cycle and completing the remaining two puts
an actual coordinate apartment on every twelve-cycle. Its pointwise
stabilizer is the binary split torus, of odd order. The equivariant coset
identification transfers these facts to the two actual parabolic coset spaces.

This verifies all geometric inputs of the normalizer fixed-point theorem;
no group recognition or local-cover assumption is used.
Source: the defining-characteristic geometry for Aschbacher–Smith,
Theorem 0.1.2(1), printed pp.3–4 and pp.481–482, with the binary pair
discussed in Lemma 14.2.21, printed p.988.
-/

public section

namespace Atlas.G2.BinaryParabolicPair.BinaryCoverGeometry
open EvenLocal.NormalizerCover EvenLocal.NormalizerCover.OctonionHexagon

/-- The full binary octonion model acts on its actual generalized hexagon. -/
theorem hexagonData : HexagonData (G := Model (ZMod 2))
    (incidenceGraph (F := ZMod 2)) vertexColor := by
  obtain ⟨e,he,hlong,_⟩ := exists_equivariant_cosetGeometryIso (F := ZMod 2)
  apply hexagonData_of_intrinsic_geometry e he hlong
  · exact geometryGraph_diameter_bound
  · exact metric_girth_of_predecessors metric_line_step metric_line_unique_preceding_point
      metric_point_level_four_predecessor_unique
  · intro x
    exact cycle_contains_coordinatePoints_of_prefix_normalization coordinate_prefix
      Apartments.complete_coordinate_prefix

end Atlas.G2.BinaryParabolicPair.BinaryCoverGeometry
