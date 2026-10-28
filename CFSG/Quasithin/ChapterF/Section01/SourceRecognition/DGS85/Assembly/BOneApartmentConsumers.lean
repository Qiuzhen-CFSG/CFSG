module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneApartmentGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalConsumers

/-!
# The constructed natural apartment on the original Chapter 12 pair

The selected perfect right factor and the original left marking make both
source parabolics nonsolvable. In the distance-one noncommuting critical
branch, construct the two natural actors, nonbinary fields, compatible
Cartan, moving reflections and actual path roots. The same apartment has
uniqueness and a finite geometric quotient, with all the literal original
pair and universal-completion conventions retained.

The chosen-module application keeps the original KnownSimple and proper-K
hypotheses. It has no extra natural-action, field-size, reflection, root or
Cartan premise. Fusion, exchange and the Borel-image bridge are still needed
for the marked split quotient and regular comparison. The other critical
and source branches remain necessary for exhaustive classification.

Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157,
(14.1)--(14.10), pp.210--216; AS 5.2.6 and 12.2.2, pp.650--651,795.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The literal selected pair supplies every natural and nonbinary input
for the constructed Cartan apartment in its noncommuting distance-one branch. -/
theorem apartment_of_critical_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1) :
    ∃ a : BOneSource.NaturalApartment ![L,R] (sourceS L H)
        (chosenCartans (d.hypothesisF11 h hTH)),
      ApartmentsUnique (X := (reducedAmalgam ![L,R] (sourceS L H)).Universal)
        (sourceGraph (reducedAmalgam ![L,R] (sourceS L H)))
        (cartanApartment (reducedAmalgam ![L,R] (sourceS L H))
          (apartmentGroup (chosenCartans (d.hypothesisF11 h hTH)) a.roots)) (a.length+1) ∧
      Finite (QuotientGroup (reducedAmalgam ![L,R] (sourceS L H))
        (cartanApartment (reducedAmalgam ![L,R] (sourceS L H))
          (apartmentGroup (chosenCartans (d.hypothesisF11 h hTH)) a.roots)) a.length) := by
  obtain ⟨a⟩ := BOneSource.apartment_of_critical_bOne (d.hypothesisF11 h hTH)
    (d.parabolics_not_solvable h hp) hc hne hb
  exact ⟨a,a.unique (d.hypothesisF11 h hTH),a.quotient_finite (d.hypothesisF11 h hTH)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)

include hp in
/-- Chapter 12 obtains actual roots, whole-Cartan reflections and their
source path parameters with no extra profile or field-size premise. -/
theorem rankOne_apartment_of_critical_bOne
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    ∃ a : BOneSource.NaturalApartment ![L,R] (Global.sourceS L H) (chosenCartans hf),
      ApartmentsUnique (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
        (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H)))
        (cartanApartment (reducedAmalgam ![L,R] (Global.sourceS L H))
          (apartmentGroup (chosenCartans hf) a.roots)) (a.length+1) ∧
      Finite (QuotientGroup (reducedAmalgam ![L,R] (Global.sourceS L H))
        (cartanApartment (reducedAmalgam ![L,R] (Global.sourceS L H))
          (apartmentGroup (chosenCartans hf) a.roots)) a.length) :=
  d.apartment_of_critical_bOne (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
