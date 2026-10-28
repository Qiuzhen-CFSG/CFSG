module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CoordinateFrame
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments

/-!
# Assembly of the concrete octonion hexagon

The actual root-parabolic coset graph is equivariantly identified with the
incidence graph of singular octonion points and zero-product planes. Coordinate
walks and predecessor calculations prove diameter at most six and girth at
least twelve. Normalizing a twelve-cycle places a translate of the six singular
coordinate points on it, so its pointwise stabilizer is conjugate to a subgroup
of the split torus and has odd order in characteristic two.

`hexagonData` assembles all these proved inputs over every finite field of
characteristic two, in particular for fields of order `2^f` with `f ≥ 2`.
The conditional transfer lemmas remain available for reuse.

Source context: Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4, repeated
as Theorem 0.1.1 on pp.481--482, and the rank-two Borel--Tits argument.
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Conditional assembly with a concrete apartment-normalization premise.
The three geometric premises must be proved for the actual octonion model. -/
theorem hexagonData_of_coordinate_apartments
    (hdiam : ∀ x y : Vertex F,
      ∃ w : incidenceGraph.Walk x y, w.length ≤ 6)
    (hgirth : ∀ (x : Vertex F) (w : incidenceGraph.Walk x x),
      w.IsCycle → 12 ≤ w.length)
    (hapartment : ∀ (x : Vertex F) (w : incidenceGraph.Walk x x),
      w.IsCycle → w.length = 12 → ∃ g : Model F,
        ∀ i : Fin 6, g • coordinateLongVertex (F := F) i ∈ w.support) :
    HexagonData (G := Model F) (incidenceGraph (F := F)) vertexColor where
  adjacent_color := incident_vertices_different_colors
  smul_adj := smul_incident
  smul_color := vertexColor_smul
  diameter_bound := hdiam
  cycle_bound := hgirth
  apartment_stabilizer_odd x w hw hl := by
    obtain ⟨g,hg⟩ := hapartment x w hw hl
    exact fixing_odd_of_contains_coordinateLongVertices {v | v ∈ w.support} g hg

/-- Transporting the intrinsic octonion geometry requires an equivariant
isomorphism with the actual parabolic coset graph and its long-point marking. -/
theorem hexagonData_of_intrinsic_geometry
    (e : incidenceGraph (F := F) ≃g geometryGraph (F := F))
    (he : ∀ (g : Model F) (v : Vertex F), e (g • v) = g • e v)
    (hlong : ∀ v : Model F ⧸ LieParabolicSetup.parabolic₂,
      e (Sum.inr v) = Sum.inr (longCosetEquivSingularPoints v))
    (hdiam : ∀ x y : GeometryVertex F,
      ∃ w : geometryGraph.Walk x y, w.length ≤ 6)
    (hgirth : ∀ (x : GeometryVertex F) (w : geometryGraph.Walk x x),
      w.IsCycle → 12 ≤ w.length)
    (hapartment : ∀ (x : GeometryVertex F) (w : geometryGraph.Walk x x),
      w.IsCycle → w.length = 12 → ∃ g : Model F,
        ∀ i : Fin 6, g • (Sum.inr (coordinatePoint i) : GeometryVertex F) ∈ w.support) :
    HexagonData (G := Model F) (incidenceGraph (F := F)) vertexColor := by
  apply hexagonData_of_coordinate_apartments
  · intro x y
    obtain ⟨w,hw⟩ := hdiam (e x) (e y)
    refine ⟨(w.map e.symm.toHom).copy (e.symm_apply_apply x) (e.symm_apply_apply y), ?_⟩
    simpa using hw
  · intro x w hw
    have h := hgirth (e x) (w.map e.toHom) (hw.map e.injective)
    simpa using h
  · intro x w hw hl
    obtain ⟨g,hg⟩ := hapartment (e x) (w.map e.toHom) (hw.map e.injective)
      (by simpa using hl)
    refine ⟨g, ?_⟩
    intro i
    have hc : e (coordinateLongVertex (F := F) i) =
        Sum.inr (coordinatePoint i) := by
      rw [coordinateLongVertex, hlong, Equiv.apply_symm_apply]
    have hi := hg i
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hi
    obtain ⟨v,hv,heq⟩ := hi
    have heq' : v = g • coordinateLongVertex (F := F) i := by
      apply e.injective
      rw [he, hc]
      change e v = g • (Sum.inr (coordinatePoint i) : GeometryVertex F) at heq
      exact heq
    simpa only [heq'] using hv

/-- The actual two-parabolic incidence graph satisfies all geometric and
odd-stabilizer clauses of `HexagonData` over a finite field of characteristic
two. The equivariant identification, metric bounds, and apartment normalization
are all supplied by the concrete octonion proofs. -/
theorem hexagonData :
    HexagonData (G := Model F) (incidenceGraph (F := F)) vertexColor :=
  hexagonData_of_intrinsic_geometry cosetGeometryIso
    cosetGeometryIso_smul cosetGeometryIso_long
    geometryGraph_diameter_bound geometryGraph_girth_bound
    (fun _ w hw hl => cycle_contains_coordinatePoints w hw hl)

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
