module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Splitting

/-!
# Discharging both endpoint splitting premises in the configuration

Apply local normalizer splitting to the original intersection and the actual
second endpoint constructed by `exists_configuration_of_local_producers`.
This discharges its entire splitting premise using the same local-intersection
family. The independent middle-normalizer and fusion conclusions remain an
explicit premise for the configuration's assembly owner.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemma 3.1, printed pp.36–37.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z g : G}

/-- Apply splitting at both actual endpoints. Only the independent middle
normalizer and fusion producer remains to complete the source configuration. -/
public theorem exists_configuration_of_middle (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hs : ¬ FusionSaturated z g)
    (middle : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      coreIntersection z g ⊓ coreIntersection z y = zpowers z →
      (∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
        IsComplement' ((coreIntersection z g).subgroupOf
          (normalizer (coreIntersection z g : Set G))) K) →
      Nonempty (MiddleData z g y)) : Nonempty (A3Configuration z g) := by
  exact exists_configuration_of_local_producers h local_intersections hgQ hg hs
    (fun y hyQ hy => intersection_normalizer_complement h hn (local_intersections y hyQ hy))
    middle

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
