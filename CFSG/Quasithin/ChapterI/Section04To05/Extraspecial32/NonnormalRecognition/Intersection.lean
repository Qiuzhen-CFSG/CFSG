module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Automizer

/-!
# Assembly of the nonnormal quaternion intersection data

For every fusion witness g, the literal intersection E = Q ∩ Qᵍ is elementary
abelian of order eight, normal in H, and self-centralizing in G. Conjugation
identifies its actual normalizer quotient with PSL₃(2), and every involution
of H is fused into Q under that normalizer. H also has odd ambient index.

The arranged quaternion argument proves H-normality for the original g;
ambient self-centralization makes the normalizer action faithful, and its
order-24 subgroup and a mover from Qᵍ give the full automorphism group of E.
The theorem `intersectionData` assembles all seven fields from the original
local hypotheses and quaternion nonnormality, with no further premises.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.4–2.6 and the opening of Section 3, pp.34–36;
Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The conditional assembly interface for the intersection and Sylow facts.
The theorem `intersectionData` below discharges its local-action premises. -/
public theorem intersectionData_of_normalizer_steps (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hNormal : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal)
    (hCentral : centralizer (coreIntersection z g : Set G) = coreIntersection z g)
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
  self_centralizing := hCentral
  normalizer_quotient := hQuotient
  involution_fusion := hFusion
  centralizer_odd_index := centralizer_odd_index h

/-- Sources 2.4–2.6 and the opening Sylow argument of Section 3, for the
literal intersection belonging to any given fusion witness. All local-action
premises are discharged from the source hypotheses in the nonnormal branch. -/
public theorem intersectionData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    IntersectionData z g := by
  have hNormal := coreIntersection_normal_in_centralizer h hn g hgQ hg
  have hCentral := coreIntersection_self_centralizing h g hgQ hg
  exact intersectionData_of_normalizer_steps h g hgQ hg hNormal hCentral
    (coreIntersection_normalizer_quotient h g hgQ hg hNormal hCentral)
    (coreIntersection_involution_fusion h g hgQ hg hNormal hCentral)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
