module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.Alternating
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.Parameters
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.BorelMarks

/-!
# The complete original alternating branch of E.6.7

Every alternating marking on a selected chi-zero block has degree three or
five. The original characteristic-normalizer control supplies its full
Borel, and the actual inner action gives corank one and global parameter
one. All earlier source premises are discharged on the original H and V.

Source: Aschbacher–Smith E.6.7(2), printed p.246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The full alternating clause, uniformly over every alternating marking
of the selected block. No Borel or action bound is retained as a premise. -/
theorem source_alternating {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M)
    (hm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆)
    (hchi : ChapterC.IsChiZeroBlock L) (hType : ChapterC.IsAlternatingBlock L n) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) = 1 ∧
      (L ⊓ M).relIndex L = n ∧ globalR V = 1 := by
  have hs : IsStronglyQuasithin L :=
    (IsStronglyQuasithin.equiv (subgroupOfEquivOfLe hLH)).mp
      ((h.obstructionIntermediate_sqtk hW hHC).stronglyQuasithin.subgroup (L.subgroupOf H))
  have hn := alternating_parameter_of_chiZero hs hchi hType
  exact source_alternating_of_borel h hW hQH hHC hc hLH hL hout hm hType hn
    (source_alternating_borel h hW hQH hHC hc hLH hL hout hType hn)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
