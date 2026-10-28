module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Diameter
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Levels
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.LineLayers
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.PointPredecessor

/-!
# Metric of the intrinsic split-octonion geometry

`geometryGraph_diameter_bound` and `geometryGraph_girth_bound` prove diameter
at most six and girth at least twelve for the actual incidence graph of
singular points and zero-product planes, over every field. In particular,
they apply to the required finite fields of characteristic two.

Explicit coordinate walks and point transitivity give the diameter bound.
For girth, incident vertices have consecutive algebraic levels, and each
vertex at positive level below six has at most one preceding neighbor. A cycle
shorter than twelve would have a maximum level below six and two distinct
preceding neighbors. The line-layer and point-predecessor coordinate proofs
discharge all premises of `metric_girth_of_predecessors`; point transitivity
and cycle rotation cover every base vertex.

Source context: the split G₂ case in Aschbacher--Smith, Theorem 0.1.2(1),
printed pp.3--4, and Theorem 0.1.1, printed pp.481--482.
The split-octonion coordinates and action APIs are from the licensed ATLAS
port; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

variable {F : Type*} [Field F]

/-- Every cycle in the intrinsic octonion incidence graph has length at least
twelve. All coordinate predecessor premises are discharged over every field. -/
theorem geometryGraph_girth_bound (x : GeometryVertex F)
    (w : geometryGraph.Walk x x) (hw : w.IsCycle) : 12 ≤ w.length :=
  metric_girth_of_predecessors metric_line_step metric_line_unique_preceding_point
    metric_point_level_four_predecessor_unique x w hw

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
