module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Automizer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.FourGroup


/-!
# Saturation and global normality of the fusion eight

If the selected intersection equals the fusion eight, the fusion data supply
its normality in H and its ambient self-centralization. The actual automizer
and involution-fusion theorems then give all the intersection data required
by the source strong-closure and TI argument.

This module applies that global argument and derives the needed distinction
E ≠ F under nonnormality of F. The sole remaining premise is the independent
local calculation for involutions acting on the elementary eight: four fixed
points and a two-group centralizer. No quaternion-nonnormality assumption
is needed by any theorem used here.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.5 and 2.8, pp.34–36.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- In the saturated case every local intersection premise follows from the supplied fusion data. -/
public theorem intersectionData_of_eq_fusion (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (he : coreIntersection z g = fusionCore z) :
    NonnormalRecognition.IntersectionData z g := by
  have he' : NonnormalRecognition.coreIntersection z g = fusionCore z := he
  have hn : ((NonnormalRecognition.coreIntersection z g).subgroupOf (Centralizer z)).Normal := by
    rw [he']
    exact h.fusionCore_normal_in_centralizer
  have hc : centralizer (NonnormalRecognition.coreIntersection z g : Set G) =
      NonnormalRecognition.coreIntersection z g := by
    rw [he']
    exact d.centralizer_eq
  exact {
    elementary := NonnormalRecognition.coreIntersection_elementary h g hg
    card := NonnormalRecognition.coreIntersection_card h g hgQ hg
    normal_in_centralizer := hn
    self_centralizing := hc
    normalizer_quotient :=
      NonnormalRecognition.coreIntersection_normalizer_quotient h g hgQ hg hn hc
    involution_fusion :=
      NonnormalRecognition.coreIntersection_involution_fusion h g hgQ hg hn hc
    centralizer_odd_index := NonnormalRecognition.centralizer_odd_index h }

/-- Apply the source global-normality argument, retaining its independent local-action calculation. -/
public theorem fusionCore_normal_of_eq_intersection_of_local_action
    (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (he : coreIntersection z g = fusionCore z)
    (local_action : ∀ j : G, j ∈ normalizer (fusionCore z : Set G) →
      orderOf j = 2 → j ∉ fusionCore z →
      Nat.card ((fusionCore z).subgroupOf (Centralizer j)) = 4 ∧
        IsPGroup 2 ((normalizer (fusionCore z : Set G)).subgroupOf (Centralizer j))) :
    (fusionCore z).Normal := by
  have b := intersectionData_of_eq_fusion h d g hgQ hg he
  have hs := (fusionSaturated_iff h d g).mpr he
  have he' : NonnormalRecognition.coreIntersection z g = fusionCore z := he
  have hn := NonnormalRecognition.normalizer_eq_top_of_local_action h b hs (by
    change ∀ j : G, j ∈ normalizer (NonnormalRecognition.coreIntersection z g : Set G) →
      orderOf j = 2 → j ∉ NonnormalRecognition.coreIntersection z g →
      Nat.card ((NonnormalRecognition.coreIntersection z g).subgroupOf (Centralizer j)) = 4 ∧
        IsPGroup 2 ((normalizer (NonnormalRecognition.coreIntersection z g : Set G)).subgroupOf
          (Centralizer j))
    rw [he']
    exact local_action)
  rw [he'] at hn
  exact normalizer_eq_top_iff.mp hn

/-- Nonnormality excludes saturation through the full global-normality argument. -/
public theorem intersection_ne_fusion_of_local_action
    (h : Hypotheses z) (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal)
    (local_action : ∀ (g : G) (_b : NonnormalRecognition.IntersectionData z g) (j : G),
      j ∈ normalizer (NonnormalRecognition.coreIntersection z g : Set G) →
      orderOf j = 2 → j ∉ NonnormalRecognition.coreIntersection z g →
      Nat.card (NonnormalRecognition.centralizerIntersection z g j) = 4 ∧
        IsPGroup 2 ((normalizer (NonnormalRecognition.coreIntersection z g : Set G)).subgroupOf
          (Centralizer j)))
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    coreIntersection z g ≠ fusionCore z := by
  intro he
  apply hnon
  apply fusionCore_normal_of_eq_intersection_of_local_action h d g hgQ hg he
  have b := intersectionData_of_eq_fusion h d g hgQ hg he
  have he' : NonnormalRecognition.coreIntersection z g = fusionCore z := he
  have hl := local_action g b
  change (∀ j : G, j ∈ normalizer (NonnormalRecognition.coreIntersection z g : Set G) →
    orderOf j = 2 → j ∉ NonnormalRecognition.coreIntersection z g →
    Nat.card ((NonnormalRecognition.coreIntersection z g).subgroupOf (Centralizer j)) = 4 ∧
      IsPGroup 2 ((normalizer (NonnormalRecognition.coreIntersection z g : Set G)).subgroupOf
        (Centralizer j))) at hl
  rw [he'] at hl
  exact hl

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
