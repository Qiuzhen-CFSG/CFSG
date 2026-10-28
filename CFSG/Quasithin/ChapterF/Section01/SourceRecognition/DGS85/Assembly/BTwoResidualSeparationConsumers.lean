module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualConsumers

/-!
# Chapter 6/12 application of original residual separation

This adapter supplies the exact F.1.11 hypothesis produced by the prepared
rank-one input and forwards the separation package to the literal selected
parabolic.  It keeps the original `L`, `R`, endpoint two-cores, Borel and
reduced-to-original inclusion visible in the conclusion, so later Chapter 12
arguments do not silently replace them with intrinsic graph groups.
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
local notation "ι" => Subgroup.subtype (G₀ ![L,R] (Global.sourceS L H))

/-- The prepared original source supplies the opening residual-separation
control in the strict `b = 2` branch. -/
theorem residual_separation_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (_hp : Group.IsPerfect R)
    {u t y : Vertex F}
    (hc : IsCriticalPair F α u)
    (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    ∃ g : graphLocalGroup F α, (g : G₀ ![L,R] (Global.sourceS L H)) • β = t ∧
      let D₀ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓
        (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔
        (Z F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
        (graphLocalGroup F u).subtype).map ι
      let Z' := (Z F u).map ι
      J₀ ≤ (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓
          (Q F y).map ι ∧
        Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
        J₀ ≤ centralizer
          ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  exact BTwoSource.original_bTwo_residual_separation
    (d.hypothesisF11 h hTH) hc hne hb hβu ht htne hy hyne

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- Literal Chapter 12 application of the original residual-separation opening. -/
theorem rankOne_residual_separation_of_critical_bTwo_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (_hp : Group.IsPerfect R)
    {u t y : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) u)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) u⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2)
    (hβu : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) u)
    (ht : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) t)
    (htne : t ≠ base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)
    (hy : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj u y)
    (hyne : y ≠ base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) :
    let F := Reduction.reducedFamily ![L,R] (Global.sourceS L H)
    let ι := (G₀ ![L,R] (Global.sourceS L H)).subtype
    ∃ g : graphLocalGroup F (base F false),
      (g : G₀ ![L,R] (Global.sourceS L H)) • base F true = t ∧
      let D₀ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓
        (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔
        (Z F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
        (graphLocalGroup F u).subtype).map ι
      let Z' := (Z F u).map ι
      J₀ ≤ (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓
          (Q F y).map ι ∧
        Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
        J₀ ≤ centralizer
          ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  exact d.residual_separation_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 _hp hc hne hb hβu
    ht htne hy hyne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
