module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition

/-!
# The proved intersection input to nonnormal quaternion recognition

The local intersection theorem supplies the complete `local_intersections`
input of `recognition_of_source_steps`, uniformly in the literal conjugator.
The recognition argument therefore retains only the saturated-fusion,
A₃-geometry, A₃-recognition and overgroup-index inputs. Those later source
arguments remain explicit; this module completes their local intersection
input, not the full recognition theorem.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Sections 2–3; Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Apply the complete local-intersection theorem to the existing recognition
consumer, retaining precisely its four later source inputs. -/
public theorem recognition_of_nonnormal_source_steps (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (saturated : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g → FusionSaturated z g →
      normalizer (coreIntersection z g : Set G) = ⊤)
    (geometry : (∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g) →
      ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      ¬ FusionSaturated z g →
      Nat.card (CoreFusion z) = 13 ∧
        ∃ L : Subgroup G, Centralizer z ≤ L ∧ Nonempty (Quasithin.I5.DSystem .A3 L))
    (a3 : ∀ L : Subgroup G, Quasithin.I5.DSystem .A3 L →
      Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)))
    (overgroup : (∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g) → Nat.card (CoreFusion z) = 13 →
      ∀ L : Subgroup G, Nonempty (L ≃* alternatingGroup (Fin 8)) →
        Centralizer z ≤ L → L = ⊤ ∨ L.index = 9) :
    ElementaryEightAlternative G ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) :=
  recognition_of_source_steps h (intersectionData h hn) saturated geometry a3 overgroup

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
