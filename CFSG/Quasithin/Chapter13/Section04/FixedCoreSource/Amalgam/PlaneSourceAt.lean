module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondShortExclusionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneNonsolvableSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SourceAmalgam

/-!
# The restricted plane theorem from guarded earlier structure

Commuting residual actions give the source two-core containment. Otherwise
the actual second Goldschmidt triple and its doubled natural module exclude
the solvable branch. The nonsolvable plane selection then gives the linear
component and full overgroup formula. This constructs the exact preserved
PlaneAmalgamSource1347 interface at the original G,T, with no extra local
amalgam, model, movement or chief-factor callback.

Earlier module, 13.3.2, 13.3.16 and natural large-distance inputs remain explicit.
The original escaping-point application is in OriginalPlaneSourceAt.
Source: Aschbacher--Smith 13.4.7(1--4), printed pp.899--904.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- Construct the restricted source consequence for every applicable original
plane pair, discharging model selection and both excluded alternatives. -/
theorem planeAmalgamSource1347_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    Solvable.PlaneAmalgamSource1347 D m := by
  intro W hW hTW A
  dsimp only
  intro hA hB eA eB hne _hres _hchief hiA hiB hcentral
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hlocal := original_pair_local D m hA.2 hB.2 eA.some eB.some hne hiA hiB
  refine ⟨hlocal,?_⟩
  by_cases hc : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)
  · exact Or.inl ((original_pair_commuting_action h₀ D m hA.2 hB.2 eA.some eB.some
      hne hiA hiB hcentral hc).2.2.2.1.trans inf_le_left)
  have hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G) := by
    intro hs
    exact original_plane_solvable_noncommuting_impossible_of_largeDistance_at h₀ h structural
      D m hA.2 hB.2 eA.some eB.some hne hindexL hiA hiB hcentral hs hc
      W hW hTW rfl hM h1332 modules fixed covered h13316 hl
  exact Or.inr (original_plane_nonsolvable_source_at h₀ D m h1332 fixed covered
    hA.2 hB.2 eA.some eB.some hne hiA hiB hcentral h13316 h structural hindexL hnonsolv
    hl W hW hTW rfl).2.2.1

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
