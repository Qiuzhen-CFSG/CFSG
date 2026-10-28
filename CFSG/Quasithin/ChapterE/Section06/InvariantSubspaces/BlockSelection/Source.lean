module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.Family
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.AlternatingSource
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.RankOneSource

/-!
# E.6.7 from the original hypotheses

The original known-simple C.1.29 product selects at most two commuting
chi-zero factors, moved by the original Thompson subgroup. Its proved full
Borel markings and the literal central Sylow action give the alternating
and binary rank-one conclusions. All maps retain the original intermediate
subgroup H, centralizer Q, and elementary subgroup V.

The theorem produces the unchanged complete E67Input contract used by
E.6.11, E.6.14 and the minimum-generation arguments. Its separate rank-one
source theorem also retains regularity on the actual [V,X].

Source: Aschbacher–Smith E.6.7, printed p.246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The original full E.6.7 theorem for the complete known-simple catalogue. -/
theorem e67Input_knownSimple {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) : E67Input T M V := by
  intro W hW H hQH hHC hc
  obtain ⟨f⟩ := sourceFamily_knownSimple h hW hQH hHC hc
  have hb (i) : ChapterC.IsBlock ((f.block i).subgroupOf H) := {
    finite := inferInstance
    short := ChapterC.RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe (f.le i)).symm (f.type i).chi.short
    subnormal := f.subnormal i }
  refine ⟨{ f.toBlockFamily with
    product := f.product
    thompson := f.thompson
    alternating := ?_
    rankOne := ?_ }⟩
  · intro i n ht
    exact source_alternating h hW hQH hHC hc (f.le i) (hb i) (f.outside i)
      (f.thompson i) (f.type i) ht
  · intro i n ht
    obtain ⟨_, X, hX, hcyc, hcard, hgen, hdis, hmove, hprod, hB, hbound, _⟩ :=
      source_rankOne h hW hQH hHC hc (f.le i) (hb i) (f.outside i) (f.thompson i) ht
    exact ⟨X, hX, hcyc, hcard, hgen, hdis, hmove, hprod, hB, hbound⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
