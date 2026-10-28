module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalConsumers

/-!
# Original Chapter 12 application of natural apartment exchange

The unchanged selected-pair hypotheses supply both full-Cartan profiles.
Both source path alternatives now have exact root-reflection fusion,
apartment exchange and the same faithful finite geometric completion,
with both endpoint squares and the whole middle of the reduced amalgam. The r=4
alternative retains its nontrivial center and literal Q/Z coordinates.

The quotient Borel-image root signs and exhaustive marked classification
remain source obligations. KnownSimple, proper-K and the original selected
pair are unchanged.
Source: DGS, Groups and Graphs (1985), (10.5), (14.12)--(14.15),
pp.156--157,217--220; Aschbacher--Smith, 12.2.2, pp.795--796.
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

/-- The original selected pair supplies exact natural exchange and its marked
finite geometric completion in both the r=3 and r=4 source alternatives. -/
theorem exchange_geometry_of_critical_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} (d.hypothesisF11 h hTH) (chosenCartans (d.hypothesisF11 h hTH)) j,
      (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 3 4 ∨
        (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 4 5 ∧
          BOneSource.HasCentralRootGeometry ds)) ∧
      BOneSource.HasMarkedGeometricQuotient ds ∧
      ChosenApartmentExchange (X := (reducedAmalgam ![L,R] (sourceS L H)).Universal)
        (sourceGraph (reducedAmalgam ![L,R] (sourceS L H)))
        (cartanApartment (reducedAmalgam ![L,R] (sourceS L H)) (apartmentGroup (chosenCartans (d.hypothesisF11 h hTH)) (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) ∧
      ∀ j, ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
        ∃ g∈universalBOneActor (d.hypothesisF11 h hTH) j (ds j).data, g*x*g⁻¹=fullCartanReflections ds j :=
  BOneSource.exchange_geometry_of_critical_bOne (d.hypothesisF11 h hTH)
    (d.parabolics_not_solvable h hp) hc hne hb (chosenCartans (d.hypothesisF11 h hTH))

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
/-- The Chapter 12 consumer obtains the original marked geometric quotient,
exact fusion and exchange, preserving the central r=4 data and full scope. -/
theorem rankOne_exchange_geometry_of_critical_bOne
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} hf (chosenCartans hf) j,
      (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf (G₀ ![L,R] (Global.sourceS L H))) 3 4 ∨
        (HasSourcePathParameters
          (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf (G₀ ![L,R] (Global.sourceS L H))) 4 5 ∧
          BOneSource.HasCentralRootGeometry ds)) ∧
      BOneSource.HasMarkedGeometricQuotient ds ∧
      ChosenApartmentExchange (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
        (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H)))
        (cartanApartment (reducedAmalgam ![L,R] (Global.sourceS L H)) (apartmentGroup (chosenCartans hf) (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) ∧
      ∀ j, ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
        ∃ g∈universalBOneActor hf j (ds j).data, g*x*g⁻¹=fullCartanReflections ds j :=
  d.exchange_geometry_of_critical_bOne (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp hc hne hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
