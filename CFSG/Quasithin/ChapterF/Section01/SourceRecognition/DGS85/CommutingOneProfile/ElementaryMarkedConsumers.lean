module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.UnitaryFourConsumers

/-!
# Original-pair consumers of the elementary commuting-edge theorem

The actual prepared pair has nonsolvable parabolics, so the elementary
commuting-edge calculation constructs its local markings and entire U₄
profile. Apply the native reduced comparison and the existing Chapter 15
restoration to obtain a comparison of the ORIGINAL pair, keeping its full
Borel and both endpoint inclusions. No equality S=O₂(B) is assumed.

The Chapter 12 application retains full KnownSimple and the same arbitrary
selected perfect factor. A marked split quotient with rotation order four
is still an explicit Chapter 14 input. This proves the conditional elementary
source branch, not exhaustive source-profile or quotient selection.
Source: DGS (1985), (11.7), pp.174--175, Theorem D and (15.2), pp.224,226--228;
Aschbacher--Smith F.1.12, pp.263--264, and 12.2.2, p.795.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Restore the original pair from its literal elementary commuting-edge
branch. The prepared nonsolvable parabolics discharge the local catalogues;
the Chapter 11 calculation constructs the entire recognition profile. -/
theorem comparison_of_commuting_one_elementary
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥)
    (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
      IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H))))
    (quot : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨m,hm,⟨f⟩⟩ := original_nonsolvable_elementary_reduced_comparison
    (d.hypothesisF11 h hTH) hc hb hcomm helem (d.parabolics_not_solvable h hp) quot e split hrot
  exact d.concreteComparison_of_reduced_alternatives h hTH hp (.unitaryFour m hm false ⟨f⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)
  (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (Global.sourceS L H)) 1
    IsElementaryAbelian 2 (reducedSylow ![L,R] (Global.sourceS L H) ⧸
      ((parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1).pCoreIn 2).subgroupOf
        (reducedSylow ![L,R] (Global.sourceS L H))))
  {P : Fin 2 → Subgroup X} (quot : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) quot.standardAmalgam)
  (split : SplitData quot.tits) (hrot : rotationOrder quot = 4)

include D h hmany hn hpsl hH d hp hc hb hcomm helem e split hrot in
/-- The full KnownSimple chosen-module consumer on the same selected perfect
factor. No source profile or local actor marking remains as an extra input. -/
theorem rankOne_comparison_of_commuting_one_elementary :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_elementary
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm helem quot e split hrot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
