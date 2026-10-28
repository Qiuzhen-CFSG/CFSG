module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegularConsumers

/-!
# The original Chapter 12 strict path application

The chosen-module input supplies the original left PSL₂ marking, and the
selected perfect residual makes both original parabolics nonsolvable.
Applying the strict path construction gives `r = 6`, `s = 7`, seven-path
transitivity and odd seven-path fixers on the literal universal tree.

This discharges the path premises of the Chapter 14 apartment construction
for the strict noncommuting branch of the same prepared configuration.
The critical pair, its original base edge and the branch `b = 2` are retained;
no additional field, residual-separation or path-regularity premise is added.
The compatible marked amalgam comparison remains the recognition obligation.

Source: DGS (1985), (10.10)(a)--(c), p.164, and (14.1), pp.210--211;
Aschbacher--Smith, F.1.11--F.1.12 and 12.2.2, pp.263--264,795--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "F" => Reduction.reducedFamily ![L,R] (Global.sourceS L H)
local notation "α" => base F false
local notation "β" => base F true
local notation "M" => G₀ ![L,R] (Global.sourceS L H)
local notation "𝒜" => reducedAmalgam ![L,R] (Global.sourceS L H)

/-- The original preparation supplies the complete strict path profile.
The original left quotient and the constructed right quotient discharge both
field markings, and the continuations of the critical path are constructed. -/
theorem strict_path_profile_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    HasSourcePathParameters
      (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf M) 6 7 ∧
    BasedPathTransitive (X := (𝒜).Universal) (sourceGraph 𝒜) 7 ∧
    ∀ {a b} (p : (sourceGraph 𝒜).Walk a b), p.IsPath → p.length = 7 →
      Odd (Nat.card (pathFixer (X := (𝒜).Universal) p)) :=
  Assembly.BTwoSource.original_bTwo_strict_tree_path_profile_of_linear_left
    (d.hypothesisF11 h hTH) hc hne hb hβu (d.parabolics_not_solvable h hp 0) h.linear

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
open Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH
local notation "F" => Reduction.reducedFamily ![L,R] (Global.sourceS L H)
local notation "α" => base F false
local notation "β" => base F true
local notation "M" => G₀ ![L,R] (Global.sourceS L H)
local notation "𝒜" => reducedAmalgam ![L,R] (Global.sourceS L H)

/-- Literal Chapter 12 application of DGS (10.10)(a)--(c): the original
selected perfect residual gives `(r,s)=(6,7)` and the path hypotheses used
in the apartment construction, without an additional field or path premise. -/
theorem rankOne_strict_path_profile_of_critical_bTwo_source
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    HasSourcePathParameters
      (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf M) 6 7 ∧
    BasedPathTransitive (X := (𝒜).Universal) (sourceGraph 𝒜) 7 ∧
    ∀ {a b} (p : (sourceGraph 𝒜).Walk a b), p.IsPath → p.length = 7 →
      Odd (Nat.card (pathFixer (X := (𝒜).Universal) p)) :=
  d.strict_path_profile_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hβu

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
