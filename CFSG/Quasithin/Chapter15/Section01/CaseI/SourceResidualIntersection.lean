module
public import CFSG.Quasithin.Chapter15.Section01.ChosenCentralizerPlacement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineResidual

/-!
# The source residual intersection in the elementary-nine row

The chosen central-seed span puts C_G(V) in M_c. The unique centralizer
partner contains T and differs from the selected maximal local M. These
source facts discharge the three remaining placement inputs of the marked
Nine residual calculation, proving the literal 15.1.18(2) intersection.

Source: Aschbacher--Smith 15.1.5(2), 15.1.16(b) and 15.1.18(2),
printed pp.1087 and1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.source_nine_residual_intersection
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) :
    letI := h.elementary
    SourceCases.Nine (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) →
    ∃ Z1 : Subgroup G, Z1 ≤ thompsonFixed T V ∧ Z1 ≠ ⊥ ∧
      M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G) ∧
      (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
          (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
        (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
          (M ⊓ centralizer (V : Set G)).subtype := by
  let := h.elementary
  intro h9
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMnot : ¬ M ≤ Mc := fun hle => hne (hM.1.1.eq_of_le hMc.1.1 hle)
  exact chosen_nine_residual_intersection T hM.1.2 h.normalized h9
    (inf_le_right.trans (h.centralizer_le_partner T hu)) hTMc hMnot

end CFSG.Quasithin.Chapter15.Section01
