module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualPairing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidualConsumers

/-!
# Original Chapter 12 endpoint-core detection

The original prepared source constructs a single residual with its four-core
intersection, whole-core centralizer and direct-product decomposition. The
endpoint-core pairing detects every element of that same residual: its
intersection with the centralizer of the intersection of the two full endpoint
cores is trivial.
The source construction supplies the linear beta marking and elementary core;
the selected perfect residual supplies original parabolic nonsolvability.
The same residual also supplies terminal separation control for every
continuation of the critical path. All maps and full Borel normalizers remain
in the original completion.

This supplies the detection input to DGS (10.8), printed pp.159--162. The
terminal-core separation, residual order and marked recognition remain open.
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

/-- The original prepared configuration supplies endpoint-core detection for
the same nontrivial residual and opposite-center conjugator. -/
theorem residual_detection_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α, Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    ∃ g : graphLocalGroup F α, (g : G₀ ![L,R] (Global.sourceS L H)) • β = t ∧
      let Q₀ := (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2
      let Q₁ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map ι
      let Z₀ := (Z F α).map ι
      let W₀ := (Z F u).map ι ⊔
        (Z F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint ![L,R] (Global.sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓
        (Q F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      R₀ ⊓ centralizer ((Q₀ ⊓ Q₁ : Subgroup G) : Set G) = ⊥ ∧
      P₀ ![L,R] (Global.sourceS L H) 0 ≤
        normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (Global.sourceS L H) ≤
        normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y ≠ β →
        let J₀ := R₀ ⊓ (Q F y).map ι
        let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
          (graphLocalGroup F u).subtype).map ι
        let Z' := (Z F u).map ι
        J₀ ≤ Q₁ ⊓ (Q F y).map ι ∧
          Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
          J₀ ≤ centralizer
            ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  exact BTwoSource.original_strict_residual_detection
    (d.hypothesisF11 h hTH) hc hne hb hβu ht htne
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
local notation "ι" => Subgroup.subtype (G₀ ![L,R] (Global.sourceS L H))

/-- The literal Chapter 12 selected-perfect-R application, with original full
cores, Borel and reduced-to-original inclusion retained. -/
theorem rankOne_residual_detection_of_critical_bTwo_source
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α, Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    ∃ g : graphLocalGroup F α, (g : G₀ ![L,R] (Global.sourceS L H)) • β = t ∧
      let Q₀ := (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2
      let Q₁ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map ι
      let Z₀ := (Z F α).map ι
      let W₀ := (Z F u).map ι ⊔
        (Z F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint ![L,R] (Global.sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓
        (Q F ((g : G₀ ![L,R] (Global.sourceS L H)) • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      R₀ ⊓ centralizer ((Q₀ ⊓ Q₁ : Subgroup G) : Set G) = ⊥ ∧
      P₀ ![L,R] (Global.sourceS L H) 0 ≤
        normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (Global.sourceS L H) ≤
        normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y ≠ β →
        let J₀ := R₀ ⊓ (Q F y).map ι
        let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
          (graphLocalGroup F u).subtype).map ι
        let Z' := (Z F u).map ι
        J₀ ≤ Q₁ ⊓ (Q F y).map ι ∧
          Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
          J₀ ≤ centralizer
            ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  exact d.residual_detection_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hβu ht htne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
