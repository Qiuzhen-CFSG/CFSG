module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Basic
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M11
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoOneRudvalis
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoFourLyons

/-!
# Four complete sporadic exclusions on the original B.4 source domain

The faithful-normalizer exclusions for M11, J1, J4 and Ru apply to the
original FF action via its component normalizer. Their concrete generation,
automorphism rank and representation-degree inputs are all discharged.
No small-module recognition is assumed. The stronger FF hypothesis of
B.4.2 avoids the separate larger degree windows for cubic ratio two.

Source: Aschbacher--Smith B.4.2, p.86; K.4, p.457.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem not_ff_m11 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m11.Carrier)) :
    ¬ IsFFModule ρ :=
  not_ff_of_faithfulExclusion .m11 faithfulExclusion_m11 h he

theorem not_ff_j1 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j1.Carrier)) :
    ¬ IsFFModule ρ :=
  not_ff_of_faithfulExclusion .j1 (j1_exclusion_of_geometry geometry_j1) h he

theorem not_ff_j4 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j4.Carrier)) :
    ¬ IsFFModule ρ :=
  not_ff_of_faithfulExclusion .j4 (j4_exclusion_of_geometry geometry_j4) h he

theorem not_ff_ru (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.ru.Carrier)) :
    ¬ IsFFModule ρ :=
  not_ff_of_faithfulExclusion .ru (ru_exclusion_of_geometry geometry_ru) h he

end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
