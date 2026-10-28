module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanDistinctSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualConsumers

/-!
# Chapter 6 and Chapter 12 adapters for distinct Cartan tori

The source-level distinctness theorem is applied to the selected original
component and its reduced completion.  These adapters preserve the full
Cartan complement, the original endpoint cores and the literal inclusion;
they add no model-selection premise.
Source: DGS85, (10.8), pp.160--161.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "F" => Reduction.reducedFamily ![L,R] (Global.sourceS L H)
local notation "α" => base F false
local notation "β" => base F true

/-- The prepared source supplies distinct alpha tori and their nontrivial beta
intersection on the literal original completion. -/
theorem path_cartan_distinct_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ ![L,R] (Global.sourceS L H)),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      ∃ g ∈ graphLocalGroup F α,
        g ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β,
        a ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ a • α = u ∧
      K ⊓ graphLocalGroup F α ≠ K ⊓ graphLocalGroup F u ∧
      ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
        (K ⊓ graphLocalGroup F β) ≠ ⊥ := by
  exact BTwoSource.original_bTwo_path_cartan_distinct
    (d.hypothesisF11 h hTH) hc hne hb hβu ht htne hy hyne
    (d.parabolics_not_solvable h hp 0)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
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

/-- Chapter 12 application of the distinct-tori source package for the
selected perfect component. -/
theorem rankOne_path_cartan_distinct_of_critical_bTwo_source
    (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ ![L,R] (Global.sourceS L H)),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      ∃ g ∈ graphLocalGroup F α,
        g ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β,
        a ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ a • α = u ∧
      K ⊓ graphLocalGroup F α ≠ K ⊓ graphLocalGroup F u ∧
      ((K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F u)) ⊓
        (K ⊓ graphLocalGroup F β) ≠ ⊥ := by
  exact d.path_cartan_distinct_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hne hb hβu ht htne hy hyne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
