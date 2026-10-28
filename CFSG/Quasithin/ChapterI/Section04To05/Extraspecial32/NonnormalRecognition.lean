module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Overgroup
public import CFSG.Quasithin.ChapterI.Section04To05.DSystem
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Assembly of the nonnormal quaternion branch of I.4.6

The fusion intersection separates the normal elementary-eight alternative from
the A₃-system argument. Recognition of that system gives PSL₄(2); the existing
exceptional isomorphism gives a genuine A₈ subgroup. The overgroup calculation
leaves index one or nine, and the proved coset-action endpoint recognizes A₉.

`recognition_of_source_steps` is conditional: the local intersection facts, saturated-fusion theorem,
construction of the A₃-system, recognition of A₃-systems, and the overgroup
index calculation remain explicit inputs. It is not the unconditional I.4.6
recognition theorem. The assembly owner must discharge all five inputs.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemma 2.8, Lemma 3.2 and Proposition 3.3, pp.35–38;
Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Assemble the source branches from their precise remaining mathematical steps.
The elementary-eight conclusion is retained, and no ambient simplicity is assumed. -/
public theorem recognition_of_source_steps (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
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
      Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  classical
  obtain ⟨g, hgQ, hg⟩ := h.fused
  by_cases hs : FusionSaturated z g
  · have d := local_intersections g hgQ hg
    exact Or.inl (d.elementaryEight_of_normalizer_eq_top (saturated g hgQ hg d hs))
  · obtain ⟨h13, L, hCL, ⟨system⟩⟩ := geometry local_intersections g hgQ hg hs
    obtain ⟨e⟩ := a3 L system
    let eA : L ≃* alternatingGroup (Fin 8) :=
      e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    exact Or.inr (alternating_eight_or_nine L eA hCL
      (overgroup local_intersections h13 L ⟨eA⟩ hCL))

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
