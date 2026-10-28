module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalConsumers

/-!
# Marked geometric completion for the original Chapter 12 pair

Apply the constructed full-Cartan profiles and r=3 geometric completion to
the selected original pair. The original left marking and perfect right
factor supply nonsolvability at both endpoints. The resulting alternative
has the same universal quotient, both endpoint inclusions and whole Borel,
or retains the actual r=4 source parameters. All natural-coordinate, root,
reflection, exchange and geometric-completion inputs are constructed.

The Chapter 12 application retains KnownSimple and the original proper-K
scope. This is an earlier finite-completion conclusion: the Borel-image
root-sign bridge, the marked split system and the remaining regular and
exceptional branches still require proof for the final classification.

Source: DGS, Groups and Graphs (1985), (10.5) and (14.13), pp.156--157,217--218;
Aschbacher--Smith, The Classification of Quasithin Groups, 5.2.6 and 12.2.2,
pp.650--651,795.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

public noncomputable section
universe u
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The original selected pair supplies the full-Cartan profiles and, in
the r=3 branch, the marked finite geometric quotient. No matrix, reflection,
root, apartment, exchange or finite-completion input is added. -/
theorem marked_geometry_of_critical_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} (d.hypothesisF11 h hTH)
        (chosenCartans (d.hypothesisF11 h hTH)) j,
      (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 3 4 ∧
        BOneSource.HasMarkedGeometricQuotient ds) ∨
      HasSourcePathParameters
        (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 4 5 := by
  obtain ⟨ds,he⟩ := BOneSource.marked_geometry_of_critical_bOne
    (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb
    (chosenCartans (d.hypothesisF11 h hTH))
  exact ⟨ds,he.imp (fun he => ⟨he.1,he.2.1⟩) id⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)

include hp in
/-- Chapter 12 obtains the actual marked finite completion in the r=3
branch, with the full original KnownSimple and proper-K hypotheses retained.
The central r=4 branch and the further BN-pair recognition remain open. -/
theorem rankOne_marked_geometry_of_critical_bOne
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} hf (chosenCartans hf) j,
      (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf
            (G₀ ![L,R] (Global.sourceS L H))) 3 4 ∧
        BOneSource.HasMarkedGeometricQuotient ds) ∨
      HasSourcePathParameters
        (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf
          (G₀ ![L,R] (Global.sourceS L H))) 4 5 :=
  d.marked_geometry_of_critical_bOne (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp hc hne hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
