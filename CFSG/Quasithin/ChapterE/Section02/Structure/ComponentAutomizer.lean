module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer.Source
/-!
# The literal component automizer in the E.2.2 reduction

The selected component generates H together with its original Sylow
subgroup, so its Sylow orbit is the two-residual. Its even order follows
from perfectness and the odd-order theorem. The genuine automizer theorem
therefore applies to N_H(K)/C_H(K). Its unique maximal subgroup is exactly
the image of the original N_M(K), as required by the paired witness proof.

Source: Aschbacher–Smith B.6.8(3), E.2.2 and E.2.7, pp.114,215–218.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The selected original component has a genuine marked minimal-parabolic automizer. -/
theorem source_component_automizer (hH : IsStronglyQuasithin H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ∃ S : Sylow 2 (NormalizerAction.Star K),
      (S : Subgroup (NormalizerAction.Star K)) =
        ((T : Subgroup H).subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K) ∧
      ∃ hPs : ChapterB.IsMinimalParabolicOver S ⊤,
        ChapterB.minimalParabolicMax S hPs =
          ((ChapterB.minimalParabolicMax T hP).subgroupOf (normalizer (K : Set H))).map
            (NormalizerAction.quotient K) := by
  have ho := generating_component_orbit_eq_residual hH T hK hgen
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  obtain ⟨S,hS,hPs⟩ := ChapterB.component_automizer_minimalParabolic T hP hK heven ho
  have hb := ChapterB.component_automizer_maximal_image_ne_top T hP hK heven ho
  have hsB : (S : Subgroup (NormalizerAction.Star K)) ≤
      ((ChapterB.minimalParabolicMax T hP).subgroupOf (normalizer (K : Set H))).map
        (NormalizerAction.quotient K) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (ChapterB.minimalParabolicMax_spec T hP).2)
  refine ⟨S,hS,hPs,le_antisymm ?_ ?_⟩
  · exact ChapterB.component_automizer_overgroup_le T hP hK heven ho
      (ChapterB.minimalParabolicMax S hPs) (ChapterB.minimalParabolicMax_spec S hPs).1.ne_top
      (hS ▸ (ChapterB.minimalParabolicMax_spec S hPs).2)
  · exact hPs.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec S hPs).2,(ChapterB.minimalParabolicMax_spec S hPs).1.covBy_top⟩
      hsB (lt_top_iff_ne_top.mpr hb)
end CFSG.Quasithin.ChapterE.Structure
