module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Maximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Right maximality for the original G₂ pair above field order four

The actual compatible comparison fixes the model field order as 2^n and
identifies both original local factors. For n > 2 the short core dichotomy
and local characteristic two identify every overcomponent's core with that
of O²(H). Binary embedding selection then gives right maximality. The
normalizer application removes the separate maximality, common-Sylow and
enlarged-core premises from the local conditions of 5.3.

The G₂(4), unitary and Ree maximality rows, exhaustive comparison, original
uniqueness and actual ambient completion remain source obligations.
The original S and full overlap are retained throughout.
Source: Aschbacher–Smith 5.2.8, pp.652–653, and Chapter12, p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both actual factors and the original exponent are determined by the
compatible G₂ comparison; the source S lies in both factors. -/
theorem rankOne_global_g2_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Nat.card F = 2^n ∧ Nonempty (L ≃* Atlas.G2.LieParabolicSetup.local₂ (F := F)) ∧
      Nonempty (residual H ≃* Atlas.G2.LieParabolicSetup.local₁ (F := F)) ∧
      ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^n) ∧
      (∀ i : Fin 2, Global.sourceS L H ≤ ![L,residual H] i) :=
  d.g2_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F he

/-- Every actual local overcomponent has the same special core when n > 2. -/
theorem rankOne_global_g2_overcomponent_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) : J.pCoreIn 2 = (residual H).pCoreIn 2 :=
  d.g2_overcomponent_core
    (D.rankOne_generic_input_of_many h hmany (by omega) hpsl) hH.1.1.2 hp hn F he hJ hKJ

/-- Right maximality in the original G₂ row for n > 2. -/
theorem rankOne_global_g2_right_maximal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) :=
  d.g2_right_maximal
    (D.rankOne_generic_input_of_many h hmany (by omega) hpsl) hH hp hn F he

/-- The original normalizer pair satisfies the local conditions of 5.3,
with maximality, the common Sylow and both enlarged cores discharged. -/
theorem rankOne_global_g2_normalizer_local_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) :=
  d.g2_normalizer_local_conditions
    (D.rankOne_generic_input_of_many h hmany (by omega) hpsl) hH hp hn F he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
