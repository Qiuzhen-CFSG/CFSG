module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Displacement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.MarkedAction

/-!
# The PSL₃ branches of the E.6.8 component sieve

`ordinary_borelAlternative` proves E.6.8(1) for PSL₃(2ⁿ), including n = 1.
`cover_borelAlternative` proves it for every permitted central two-cover of
PSL₃(4), including the trivial center.

`BorelPlacement` constructs the marked Sylow subgroup and identifies L ∩ M
with its normalizer, using the full E.6.7 input for containment and the
O^{2′} residual condition to exclude larger parabolics. `MarkedAction`
identifies the actual cyclic induced action, its exact corank, and its
fixed subgroup for n > 1. The coprime splitting from `Reduction` then gives
the source direct decomposition and displacement dimension, and containment
of U in C_V(L) gives the upper bound.

The known-simple class is the full catalogue. Only the earlier local facts
and the universally quantified E.6.7 source statement remain explicit inputs;
Borel placement and all model action calculations are discharged here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The ordinary PSL₃ branch of E.6.8(1), with all seven clauses and the
binary endpoint retained. The full E.6.7 statement is the earlier source input. -/
theorem ordinary_borelAlternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    BorelAlternative M V U L n := by
  obtain ⟨hz, S, hS, hplace⟩ :=
    BorelPlacement.ordinary_placement h earlier h67 hU hL hn iso
  obtain ⟨haction, hdimension, hfixed⟩ :=
    MarkedAction.ordinary_calculations h earlier hU hL hn iso S hS hplace
  exact borelAlternative_of_calculations h hU hL (.linear_three hn iso)
    S hz hplace haction hdimension hfixed

/-- The PSL₃(4) central-cover branch of E.6.8(1). Every two-group center is
allowed, including the trivial center; the source parameter is n = 2. -/
theorem cover_borelAlternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : n = 2) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    BorelAlternative M V U L n := by
  subst n
  obtain ⟨S, hS, hplace⟩ := BorelPlacement.cover_placement h earlier h67 hU hL hz iso
  obtain ⟨haction, hdimension, hfixed⟩ :=
    MarkedAction.four_cover_calculations h earlier hU hL iso S hz hS hplace
  exact borelAlternative_of_calculations h hU hL (.linear_three_cover rfl hz iso)
    S hz hplace haction hdimension (fun _ => hfixed)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
