module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondShortExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ApplicableNonsolvable
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalSource

/-!
# The original restricted plane amalgam theorem

For every applicable original plane pair, commuting residual actions
lift to the required residual two-core bound. Otherwise the completed
second-amalgam argument excludes solvability. Actual component selection
then excludes the alternating-six row and supplies the linear-three
component, ordinary Thompson normality and the full overgroup product.
Thus the exact PlaneAmalgamSource1347 interface is constructed without a
local amalgam, model, movement, chief-budget or Baumann callback.

The final application discharges that interface in the original solvable
recognition theorem. Genuine preceding structural, module, 13.3.2,
13.3.16 and natural large-distance inputs remain explicit; recognition
also retains the earlier fusion and local-structure hypotheses. This is
not yet the final assembly of 13.4.1 at every reciprocal core.
Source: Aschbacher--Smith 13.4.7(1--4), printed pp.899--904, and its
original 13.4.8--9 application, printed pp.904--907.
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
theorem planeAmalgamSource1347
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    exact original_plane_solvable_noncommuting_impossible_of_largeDistance h₀ h structural
      D m hA.2 hB.2 eA.some eB.some hne hindexL hiA hiB hcentral hs hc
      W hW hTW rfl hM h1332 modules fixed covered h13316 hl
  exact Or.inr (original_plane_nonsolvable_source h₀ D m h1332 fixed covered
    hA.2 hB.2 eA.some eB.some hne hiA hiB hcentral h13316 h structural hindexL hnonsolv
    hl W hW hTW rfl).2.2.1

/-- Apply the constructed plane theorem to the original solvable recognition
consumer; its earlier fusion and local source hypotheses remain explicit. -/
theorem original_R1_recognition_of_plane_source
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  exact Solvable.isPSp_of_original_R1_source_amalgam h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342
    (planeAmalgamSource1347 hl h₀ h structural modules D m h1332 fixed covered h13316 hindex hM)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
