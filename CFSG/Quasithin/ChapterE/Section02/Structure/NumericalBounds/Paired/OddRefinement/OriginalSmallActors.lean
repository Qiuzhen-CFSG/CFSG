module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.OddRefinement.SmallActors
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Attainment
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Small swapping actors through the full original maximal core

The actual image of A in H/J has order at most four and moves the simple
component image. Its genuine rank-one E-member escapes the marked maximal.
E.1.10(7) lifts this member with the same embedded two-residual image and
all of the original A. A hypothetical containment upstairs would put the
quotient residual and its prescribed Sylow into the quotient maximal,
contradicting the original escape. No equality of whole member images is used.

This is a source-correct branch of the odd paired refinement, not generation
at one for arbitrary elementary families. Source: Aschbacher–Smith E.1.10(7),
E.1.11 and E.2.2, printed pp.211–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.OddRefinement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem original_small_moving_member_escape
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup H))
    (hcard : Nat.card (A.map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 4)
    (hmove : ¬ A.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≤
      normalizer ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) :
        Set (H ⧸ ChapterB.minimalParabolicCore T hP))) :
    ∃ X : Subgroup H, IsEMemberAt 1 (T : Subgroup H) A X ∧
      ¬ X ≤ ChapterB.minimalParabolicMax T hP := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  let W := A.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := source_component_simple_image T hP hs K hK hgen
  have hLn : ¬ L.Normal := fun hd => hn (cComponent_normal_of_quotient_normal hK J hd)
  obtain ⟨hPs,hJs⟩ := source_star_minimal_core_free T hP
  have hM : ChapterB.minimalParabolicMax S hPs = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hcardW : Nat.card W ≤ 4 := hcard
  obtain ⟨P,hPm,hPM⟩ := exists_small_moving_member_escape
    (source_star_sqtk hA hH T hP hs).stronglyQuasithin S hPs hsX hJs hi.2.1
    hi.2.2.2 hLn (map_mono hAT) hmove hcardW
  obtain ⟨X,hX,hres⟩ := hPm.exists_quotient_lift T A J hAT
  refine ⟨X,hX,?_⟩
  intro hXM
  apply hPM
  have hR : (pResidual 2 P).map P.subtype ≤ ChapterB.minimalParabolicMax S hPs := by
    rw [hM,←hres]
    exact map_mono ((map_subtype_le (pResidual 2 X)).trans hXM)
  obtain ⟨R,hRP⟩ := hPm.1.2.2.2.2.1
  have he := congrArg (Subgroup.map P.subtype) (pResidual_sup_sylow_eq_top R)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at he
  rw [←he]
  refine sup_le hR ?_
  rw [hRP,subgroupOf_map_subtype]
  exact inf_le_left.trans (ChapterB.minimalParabolicMax_spec S hPs).2

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.OddRefinement
