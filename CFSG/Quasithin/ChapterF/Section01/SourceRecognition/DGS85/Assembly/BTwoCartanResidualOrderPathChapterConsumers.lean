module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrderPathConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegularConsumers

/-!
# Chapter 6 and Chapter 12 adapters for the terminal residual order

These wrappers retain the selected original component and its actual
reduced-to-original inclusion while forwarding the source path-card result.
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

/-- Chapter 6 adapter for the concrete terminal residual order. -/
theorem path_cartan_residual_order_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      ∃ g : G₀ ![L,R] (Global.sourceS L H),
        g ∈ graphLocalGroup F α ∧ g • β = t ∧
          Nat.card (bTwoResidual F β t u (g • u)) = Nat.card k := by
  exact BTwoSource.original_bTwo_path_cartan_residual_order
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

/-- Chapter 12 adapter for the selected perfect component and terminal path. -/
theorem rankOne_path_cartan_residual_order_of_critical_bTwo_source
    (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      ∃ g : G₀ ![L,R] (Global.sourceS L H),
        g ∈ graphLocalGroup F α ∧ g • β = t ∧
          Nat.card (bTwoResidual F β t u (g • u)) = Nat.card k := by
  exact d.path_cartan_residual_order_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hβu
    ht htne hy hyne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

