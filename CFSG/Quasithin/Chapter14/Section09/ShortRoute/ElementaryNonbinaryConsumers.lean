module
public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.ElementaryNonbinary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.UnitaryFourConsumers

/-!
# The elementary nonbinary DGS branch at the selected Chapter 12 factor

The original critical pair, commuting centers and elementary beta Sylow
quotient construct a marked reduced U₄ comparison. Original restoration
retains its whole Borel and the possible degree-two outer extension. Feed
this constructed comparison into the existing prepared-pair catalogue and,
when the selected factor is the whole residual, into the ambient recognizer.

The proper-K, full KnownSimple, original many-overgroups and perfect residual
hypotheses are unchanged. This proves this particular source branch; no
exhaustive profile selection is asserted. Source: DGS (1985), (11.7),
Theorem D and (15.2); Aschbacher--Smith F.1.12 and the application on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
variable
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
  (hb : DGS85.b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),Z (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆=⊥)
  (helem : ∃ hN : (((Q (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
      (twoCore (commonBorel ![L,R] (sourceS L H)))).Normal,
    letI := hN
    IsElementaryAbelian 2 (twoCore (commonBorel ![L,R] (sourceS L H)) ⧸
      ((Q (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
        (twoCore (commonBorel ![L,R] (sourceS L H)))))
  (hnb : ¬ ClassicalGroup.IsPSL
    ((graphLocalGroup (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map (Reduction.G₀ ![L,R] (sourceS L H)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily ![L,R] (sourceS L H)) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map (Reduction.G₀ ![L,R] (sourceS L H)).subtype)) 2 2)
include d h hTH hp hc hb hcomm helem hnb

/-- The selected source pair has an original concrete comparison on this
branch, with no supplied model, finite quotient, exchange or root signs. -/
theorem comparison_of_elementary_nonbinary :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨m,hm,_,e,_,_⟩ := ShortRoute.elementary_nonbinary_original_comparison
    (G := G) (L := ![L,R]) (S := sourceS L H)
    (d.hypothesisF11 h hTH) hc hb hcomm helem hnb
  exact d.concreteComparison_of_reduced_alternatives h hTH hp
    (.unitaryFour m hm false ⟨e⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
variable
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) false) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true))
  (hb : DGS85.b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) false),Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true)⁆=⊥)
  (helem : ∃ hN : (((Q (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true)).map (Reduction.G₀ ![L,residual H] (Global.sourceS L H)).subtype).subgroupOf
      (twoCore (commonBorel ![L,residual H] (Global.sourceS L H)))).Normal,
    letI := hN
    IsElementaryAbelian 2 (twoCore (commonBorel ![L,residual H] (Global.sourceS L H)) ⧸
      ((Q (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true)).map (Reduction.G₀ ![L,residual H] (Global.sourceS L H)).subtype).subgroupOf
        (twoCore (commonBorel ![L,residual H] (Global.sourceS L H)))))
  (hnb : ¬ ClassicalGroup.IsPSL
    ((graphLocalGroup (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true)).map (Reduction.G₀ ![L,residual H] (Global.sourceS L H)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) (base (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) true)).map (Reduction.G₀ ![L,residual H] (Global.sourceS L H)).subtype)) 2 2)
include D h hmany hn hpsl hH d hp hc hb hcomm helem hnb

/-- The actual whole-residual consumer closes the elementary nonbinary
branch, retaining the original guarded source hypotheses and full catalogue. -/
theorem rankOne_globalExit_of_elementary_nonbinary : RankOneModule.GlobalExit G := by
  exact D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (d.comparison_of_elementary_nonbinary
      (G := G) (T := T) (L := L) (H := H) (R := residual H)
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hb hcomm helem hnb)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
