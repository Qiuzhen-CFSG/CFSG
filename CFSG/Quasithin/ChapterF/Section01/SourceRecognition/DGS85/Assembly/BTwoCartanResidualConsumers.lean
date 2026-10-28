module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualConsumers

/-!
# Original Chapter 12 path-compatible residual control

The prepared source supplies the full Cartan, both corrected local transporters,
and the residual associated with a prescribed five-vertex path. The same
witnesses give both-torus centralization and the source three-subgroup
calculation through the literal inclusion into the original completion.

These applications discharge the local action and Cartan inputs to the first
part of DGS85 (10.8), printed pp.159--161. They do not assert terminal-core
separation or identify this chosen-path witness with a witness chosen uniformly
for all terminal continuations.
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

/-- The prepared original source supplies the full path-compatible Cartan
and the literal original-completion residual centralization. -/
theorem path_cartan_residual_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
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
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ a • α = u ∧
      let D₀ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let Kα := (K ⊓ graphLocalGroup F α).map ι
      let Kβ := (K ⊓ graphLocalGroup F β).map ι
      let Ku := (K ⊓ graphLocalGroup F u).map ι
      W₀ ⊔ (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2 = enlargedEndpoint ![L,R] (Global.sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      D₀ = (Z F α).map ι ⊔ R₀ ∧ Disjoint ((Z F α).map ι) R₀ ∧
      Disjoint R₀ ((Z F u).map ι) ∧
      K.map ι ≤ normalizer (W₀ : Set G) ⊓ normalizer (R₀ : Set G) ⊓
        normalizer (J₀ : Set G) ∧
      R₀ ≤ centralizer (Kα : Set G) ∧
      J₀ ≤ centralizer ((Kα ⊔ Ku : Subgroup G) : Set G) ∧
      ⁅(V F β 1 ⊓ Q F α).map ι,(Kα ⊔ Ku) ⊓ Kβ⁆ ≤ centralizer (J₀ : Set G) ∧
      Kα.conjBy (a : G) = Ku := by
  exact BTwoSource.original_bTwo_path_cartan_control
    (d.hypothesisF11 h hTH) hc hne hb hβu ht htne hy hyne

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
local notation "ι" => Subgroup.subtype (G₀ ![L,R] (Global.sourceS L H))

/-- The actual Chapter 12 source supplies the chosen-path residual and
three-subgroup calculation without additional model or Cartan premises. -/
theorem rankOne_path_cartan_residual_of_critical_bTwo_source
    (d : Global.Preparation T L H A B R)
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
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ g • β = t ∧
      ∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ ![L,R] (Global.sourceS L H))) ∧ a • α = u ∧
      let D₀ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let Kα := (K ⊓ graphLocalGroup F α).map ι
      let Kβ := (K ⊓ graphLocalGroup F β).map ι
      let Ku := (K ⊓ graphLocalGroup F u).map ι
      W₀ ⊔ (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2 = enlargedEndpoint ![L,R] (Global.sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      D₀ = (Z F α).map ι ⊔ R₀ ∧ Disjoint ((Z F α).map ι) R₀ ∧
      Disjoint R₀ ((Z F u).map ι) ∧
      K.map ι ≤ normalizer (W₀ : Set G) ⊓ normalizer (R₀ : Set G) ⊓
        normalizer (J₀ : Set G) ∧
      R₀ ≤ centralizer (Kα : Set G) ∧
      J₀ ≤ centralizer ((Kα ⊔ Ku : Subgroup G) : Set G) ∧
      ⁅(DGS85.V F β 1 ⊓ Q F α).map ι,(Kα ⊔ Ku) ⊓ Kβ⁆ ≤ centralizer (J₀ : Set G) ∧
      Kα.conjBy (a : G) = Ku := by
  exact d.path_cartan_residual_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    hc hne hb hβu ht htne hy hyne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
