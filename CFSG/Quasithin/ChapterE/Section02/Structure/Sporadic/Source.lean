module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.InvariantRows
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.MathieuRows
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.JankoRows
public import CFSG.Quasithin.ClassificationModels.Families
/-!
# The full normal sporadic exclusion in E.2.2

The original normal C-component has simple nonabelian image in H/J.
Its quotient is core-free and remains minimal parabolic. Consequently the
image is self-centralizing and equals the generalized Fitting subgroup.
All eleven C(5) sporadic rows are excluded by their concrete generating
Sylow overgroups, including every permitted outer two-extension.

No module hypothesis, model geometry witness or classification conclusion
is assumed by the original-quotient consumer.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.Sporadic
open ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- No C(5) sporadic group occurs as the normal simple supplement of a
core-free minimal parabolic. -/
theorem no_model (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hm : IsTheoremCSporadicModel L) : False := by
  obtain ⟨hF,hc⟩ := faithful_normal_structure T hP hcore L ha hgen
  have htwo : pCore 2 G = ⊥ := le_bot_iff.mp
    ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hcore.le)
  rcases hm with hs | hj1
  · rcases hs with ⟨name, hn, ⟨e⟩⟩
    cases name with
    | m11 => exact no_m11 T L ha hc e hP
    | m12 => exact no_m12 T L ha hc e hP
    | m22 => exact no_m22 T L hc htwo e hP
    | m23 => exact no_m23 T L hc e hP
    | m24 => exact no_m24 T L ha hgen e hP
    | j2 => exact no_jankoTwo T L hF e hP
    | j3 => exact hn rfl
    | j4 => exact no_jankoFour T L hF e hP
    | hs => exact no_higmanSims T L ha hgen e hP
    | he => exact no_held T L ha hgen e hP
    | ru => exact no_rudvalis T L hgen e hP
  · obtain ⟨e⟩ := hj1
    exact no_jankoOne T L ha hF e hP

end CFSG.Quasithin.ChapterE.Structure.Sporadic

namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]
/-- The literal normal-component image in the original H/J has no sporadic row. -/
theorem source_normal_component_not_sporadic (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ¬ ChapterA.Section02.IsTheoremCSporadicModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) := by
  intro hm
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hi := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  let : (K.map q).Normal := hi.2.2.1
  have hc := source_star_minimal_core_free T hP
  exact Sporadic.no_model (T.mapSurjective (QuotientGroup.mk'_surjective J))
    hc.1 hc.2 (K.map q) hi.2.1 hi.2.2.2 hm
end CFSG.Quasithin.ChapterE.Structure
