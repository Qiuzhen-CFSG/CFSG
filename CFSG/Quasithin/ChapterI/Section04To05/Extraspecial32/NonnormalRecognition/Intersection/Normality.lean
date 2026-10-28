module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.ActorConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.SwapGeometry

/-!
# Normality and self-centralization of the nonnormal-branch fusion eight

Ambient self-centralization of the literal fusion intersection is proved
without a quaternion-nonnormality hypothesis. In the nonnormal branch, the
constructed arranged inverter swaps the intrinsic quaternion factors and
inverts the original chosen Sylow three-subgroup. The quaternion argument
makes the arranged intersection invariant under that subgroup, and transport
back by the arranging element of H proves normality for the original g.

The final assembly below discharges both the normality and centralizer fields
of IntersectionData. Only the normalizer quotient and involution fusion remain
explicit inputs for the full local-intersection assembly owner.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.2–2.6; Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Source 2.6(1) for the original fusion witness: E is normal in H when
the intrinsic quaternion subgroups are not normal in H. -/
public theorem coreIntersection_normal_in_centralizer (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    ((coreIntersection z g).subgroupOf (Centralizer z)).Normal := by
  obtain ⟨w⟩ := nonempty_arrangedSwapWitness h hn g hgQ hg
  exact coreIntersection_normal_in_centralizer_of_arrangedSwap h g hgQ hg w

/-- Apply source 2.5(1) to the exact IntersectionData centralizer field.
The remaining source steps are explicit and must be discharged by assembly. -/
public theorem intersectionData_of_normality_and_normalizer_steps (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hNormal : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal)
    (hQuotient : Nonempty
      ((normalizer (coreIntersection z g : Set G) ⧸
        (coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hFusion : ∀ t : G, t ∈ Centralizer z → orderOf t = 2 →
      ∃ m : normalizer (coreIntersection z g : Set G),
        (m : G) * t * (m : G)⁻¹ ∈ coreInG z) :
    IntersectionData z g where
  elementary := coreIntersection_elementary h g hg
  card := coreIntersection_card h g hgQ hg
  normal_in_centralizer := hNormal
  self_centralizing := coreIntersection_self_centralizing h g hgQ hg
  normalizer_quotient := hQuotient
  involution_fusion := hFusion
  centralizer_odd_index := centralizer_odd_index h

/-- Apply sources 2.5(1) and 2.6(1) to their exact IntersectionData fields.
The local-intersection assembly owner retains the independent quotient and
involution-fusion steps of sources 2.5(2) and 2.6(2). -/
public theorem intersectionData_of_nonnormal_and_normalizer_steps (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hQuotient : Nonempty
      ((normalizer (coreIntersection z g : Set G) ⧸
        (coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hFusion : ∀ t : G, t ∈ Centralizer z → orderOf t = 2 →
      ∃ m : normalizer (coreIntersection z g : Set G),
        (m : G) * t * (m : G)⁻¹ ∈ coreInG z) :
    IntersectionData z g :=
  intersectionData_of_normality_and_normalizer_steps h g hgQ hg
    (coreIntersection_normal_in_centralizer h hn g hgQ hg) hQuotient hFusion

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
