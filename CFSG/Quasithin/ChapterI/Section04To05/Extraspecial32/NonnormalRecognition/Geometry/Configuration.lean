module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Interfaces

/-!
# Construction of the source configuration: endpoint and assembly stage

`Configuration.Endpoints` proves endpoint fusion, constructs the actual
second intersection, and proves its overlap with the first. The theorem
below applies the local splitting producer at both endpoints and the
middle-normalizer producer to this constructed pair.

The two producer premises remain explicit proof obligations. This is a
conditional assembly, not the completed existence assertion of source 3.1.
The original configuration task retains their discharge.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemmas 2.8 and 3.1, printed pp.36–37.
-/

public section

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z g : G}

/-- Apply the two outstanding local producers to the endpoints constructed here.
The source theorem is complete only after both producer premises are discharged. -/
theorem exists_configuration_of_local_producers (h : Hypotheses z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hs : ¬ FusionSaturated z g)
    (splitting : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      ∃ K : Subgroup (normalizer (coreIntersection z y : Set G)),
        IsComplement' ((coreIntersection z y).subgroupOf
          (normalizer (coreIntersection z y : Set G))) K)
    (middle : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      coreIntersection z g ⊓ coreIntersection z y = zpowers z →
      (∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
        IsComplement' ((coreIntersection z g).subgroupOf
          (normalizer (coreIntersection z g : Set G))) K) →
      Nonempty (MiddleData z g y)) : Nonempty (A3Configuration z g) := by
  obtain ⟨y, hyQ, hy, hinter⟩ := exists_endpoint_pair h local_intersections hgQ hg hs
  have point_split := splitting g hgQ hg
  have plane_split := splitting y hyQ hy
  obtain ⟨m⟩ := middle y hyQ hy hinter point_split
  exact ⟨{
    y := y
    conjugate_mem := hyQ
    conjugate_ne := hy
    endpoint_intersection := hinter
    fusion_union := m.fusion_union
    A := m.A
    elementary := m.elementary
    card := m.card
    self_centralizing := m.self_centralizing
    normalizer_quotient := m.normalizer_quotient
    S := m.S
    A_le_sylow := m.A_le_sylow
    normalizer_intersection := m.normalizer_intersection
    point_split := point_split
    plane_split := plane_split }⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
