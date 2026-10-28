module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerEndpointRecognition
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PlaneStabilizer
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlane

/-!
# Complete original-source normalizer facts

The original source hypotheses now produce all of F.5.4, including both
normalizer quotients, the exact elementary family and intersections, and
the endpoint joins EᵢR ≃ D₈ × S₄. The only choice is the source Sylow R
containing Tf. Every earlier fusion and local-model premise is discharged.

The product identifications have the exact unmarked meaning in NormalizerFacts;
they assert no additional identification of a literal S₄ complement.
Source: Aschbacher--Smith F.5.4, printed p.301.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

/-- All original F.5.4 conclusions, using the literal marked short involution. -/
theorem source_normalizerFacts (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) :
    NormalizerFacts c i z (sourceMarkedShort c i) R := by
  let t := sourceMarkedShort c i
  have hf := source_fusionFacts c i z h
  have ht := source_normalizer_root_transitive c i z h
  have hp := normalizer_point_stabilizer_card c i z h t hf
  have hl := source_normalizer_local_plane c i z h
  exact {
    self_centralizer := source_A_self_centralizer c i z h
    R_iso := normalizer_R_iso c i z t hf R
    R_normalizes_E := normalizer_R_normalizes_E c i z t hf h R hR ht hp hl
    ER_iso := normalizer_ER_iso c i z t hf h R hR ht hp hl
    point_quotient := source_normalizer_point_quotient c i z h
    plane_quotient := source_normalizer_plane_quotient c i z h
    Q_quotient := normalizer_Q_quotient c i z h
    elementary_bound := normalizer_elementary_bound c i z h
    elementary_list := source_normalizer_elementary_list c i z h
    plane_intersection := source_normalizer_plane_intersection c i z h
    joint_centralizer := source_normalizer_joint_centralizer c i z h
    local_plane_normalizer := hl
    transvection := source_normalizer_transvection c i z h }

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
