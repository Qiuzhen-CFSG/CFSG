module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

/-!
# The original E.6.7 producer in the block-selection consumer

Discharge the full E67Input in the low-three-rank branch of the actual
centralizer selection theorem. The supplied source V, W and centralizer
are retained; no abstract block family is supplied by the caller.

Source: Aschbacher–Smith E.6.7 and the low-three-rank branch of E.6.14,
printed pp.246 and 251.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The existing literal centralizer consumer with its E.6.7 premise discharged. -/
theorem exists_single_of_rank_knownSimple
    {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hW : W ∈ obstructionFamily M V)
    (hc : HasCharacteristicTwo (centralizer (W : Set G)))
    (hrank : primeRank 3 (centralizer (W : Set G)) ≤ 1) :
    ∃ L : Subgroup G, L ≤ centralizer (W : Set G) ∧
      centralizer (W : Set G) = (centralizer (W : Set G) ⊓ M) ⊔ L ∧
      ChapterC.IsChiZeroBlock L ∧
      (L.subgroupOf (centralizer (W : Set G))).IsSubnormal ∧ ¬ L ≤ M :=
  exists_single_of_rank h (e67Input_knownSimple h) hW hc hrank

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
