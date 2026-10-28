module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BinaryQuotients
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreGeometry
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Chapter 13 exclusions on the original quasithin consumers

The generic prepared pair has nonsolvable endpoints; the selected cubic
or prime pair has a nonsolvable right endpoint even when its left endpoint
is solvable. These facts follow from their existing source hypotheses and
exclude Chapter 13's both-SL₂(2) conclusion. The actual eight-field pair is
excluded by its prescribed residual quotient marking, transported through
the original starred inclusion into G₀.

These applications require no M₁₂ or Aut(M₁₂) reconstruction. They do not
prove the earlier Chapter 9 binary conclusion or the exhaustive source
case split; those inputs retain their producers. The selected right factor,
original Sylow, full parabolic cores and original KnownSimple scope remain.

Source: DGS, Groups and Graphs (1985), (13.1), p.191; Aschbacher--Smith
F.1.9--12, pp.261--264, 5.2.2 and 5.2.6, pp.647--651, 12.2.2, p.795,
and 14.2.14--27, pp.984--992.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Chapter 13's both-binary conclusion is impossible for every original
prepared perfect R. Its nonsolvability is supplied by the preparation. -/
theorem no_chapter_thirteen_binary
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (e : ∀ i, (ReducedLayer.star ![L,R] (sourceS L H) i ⧸
      pCore 2 (ReducedLayer.star ![L,R] (sourceS L H) i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_source_binary_of_nonsolvable_parabolic (d.hypothesisF11 h hTH) 0
    (d.parabolics_not_solvable h hp 0) e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.Source ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

/-- The selected cubic/prime pair already has a nonsolvable right endpoint.
This excludes Chapter 13 using its original source hypotheses, even when
the left endpoint itself is cubic and solvable. -/
theorem LocalData.zeroCore_no_chapter_thirteen_binary
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : ∀ i, (ReducedLayer.star ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) i ⧸
      pCore 2 (ReducedLayer.star ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_source_binary_of_nonsolvable_parabolic (d.hypothesisF11 h hH c hd hz) 1
    (d.right_parabolic_not_solvable hz) e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterF.Source
open ChapterF.Source.DGS85.Assembly.BinaryQuotients
open ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-field residual marking excludes Chapter 13 at the
original first factor. No nonbinary condition is appended to 14.2.27. -/
theorem source_no_chapter_thirteen_binary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
    (eb : (ReducedLayer.star (locals T M Mc H) (T : Subgroup G) false ⧸
      pCore 2 (ReducedLayer.star (locals T M Mc H) (T : Subgroup G) false)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  have hf := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  apply no_source_binary_of_nonbinary_linear hf false (n := 3) (by decide) _ eb
  exact ⟨GaloisField 2 3, inferInstance, inferInstance,
    GaloisField.card 2 3 (by decide), ⟨residualQuotientEquiv H eR⟩⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

/-- Exclude Chapter 13 at the SAME selected perfect R used by the original
chosen-module consumer, deriving nonsolvability from its existing hypotheses. -/
theorem rankOne_no_chapter_thirteen_binary
    {T : Sylow 2 G} {L V H A B R : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (e : ∀ i, (ReducedLayer.star ![L,R] (Global.sourceS L H) i ⧸
      pCore 2 (ReducedLayer.star ![L,R] (Global.sourceS L H) i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  d.no_chapter_thirteen_binary (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
