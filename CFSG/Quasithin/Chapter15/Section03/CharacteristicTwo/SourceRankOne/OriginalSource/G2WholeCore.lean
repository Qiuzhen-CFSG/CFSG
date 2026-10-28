module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Intrinsic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ShortCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2Irreducibility

/-!
# The original G₂ branch from core reconstruction

The original source supplies perfectness, the generalized Fitting condition
and the quasisimple quotient. A natural G₂ model gives module irreducibility.
When the actual component module exhausts [O₂(L),L], its elementary and central
properties therefore establish shortness and feed the existing original-source
contradiction with the original parabolic marking.

The core equality and equivariant model are still explicit MS93 reconstruction
inputs. This module does not infer them from a natural constituent.
Source: Aschbacher–Smith C.1.7, C.1.30–32 and 15.3.31, pp.123,135–136,1132;
Meierfrankenfeld–Stellmacher (1993), Main Theorem (10).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open CentralCover.BlockModels
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual natural model discharges irreducibility; source data discharges the group clauses. -/
theorem source_g2_short_of_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (he : IsElementaryAbelian 2 (ChapterC.blockU c.L))
    (hc : ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) :
    ChapterC.IsShort c.L := by
  have hact : multiplicativeAction G2.action = ChapterC.g2TwoNaturalAction := by ext a v; rfl
  have hm : ChapterC.BlockModuleModel c.L ChapterC.g2TwoNaturalAction := hact ▸ model
  exact s.short_of_core he hc hm.g2_irreducible

/-- The exact structural output of MS93 suffices, without identifying its seed
with the separately constructed source component module. -/
theorem source_g2_false_of_elementary_central_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L G2.Actor
      Parabolics.g2DerivedParabolic)
    (he : IsElementaryAbelian 2 (ChapterC.blockU c.L))
    (hc : ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) : False :=
  source_g2_false_of_natural_core s m (source_g2_short_of_core s he hc model) model

/-- Core exhaustion and literal natural coordinates eliminate the original G₂ branch. -/
theorem source_g2_false_of_core_reconstruction
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L G2.Actor
      Parabolics.g2DerivedParabolic)
    (hQ : extensionCore c.L = d.componentModule I c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) : False := by
  exact source_g2_false_of_elementary_central_core s m
    (s.core_elementary_of_eq_componentModule hQ)
    (s.core_central_of_eq_componentModule hQ) model
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
