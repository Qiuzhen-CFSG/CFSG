module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.OriginalSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationSolvableAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneSourceAt

/-!
# Original solvable recognition with structural inputs at G,T

A solvable escaping centralizer excludes the covered initial quotient.
The escaping centralizer and N_G(L) lie in distinct maximal two-local
overgroups of T. This verifies the guard for the completed 12.2.13 theorem,
using just the earlier structural and module clauses at G,T. In the ordinary
row the augmentation calculation supplies the Baumann alternative on the
literal R₁; the resulting recognition alternatives give fusion and the omega
index. The point-residual theorem supplies 13.3.9. The actual local product then proves N_G(L)=LT, so the constructed
plane theorem applies and selects the linear amalgam. Its marked C₃
geometry, Thompson fusion and product centralizers recognize G as Sp₆(2).

The final statement starts with the original nonzero fixed chosen module.
It constructs applicability and the five-dimensional marking, and assumes
no ordinary quotient, normalizer supplement, fusion, amalgam or recognition
callback, nor a separate 12.2.13 premise. Genuine earlier Chapter12/13.3
and natural large-distance inputs remain explicit for final source assembly.
Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem recognition_from_escaping_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    Theorem12213At KnownSimple.IsKnownSimple T := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hH := isTwoLocal_involution_centralizer
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1)
  obtain ⟨N,hHN,hN⟩ := Finite.exists_le_maximal hH
  have hM := (h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  apply Chapter12.Section02.RecognitionSource.theorem12213_of_modules_of_many_at structural modules
  apply (Set.one_lt_ncard (Set.toFinite _)).mpr
  refine ⟨normalizer (L : Set G),⟨hM,D.sylow_normalizes_component⟩,
    N,⟨hN,(original_sylow_le_centralizer hz).trans hHN⟩,?_⟩
  intro he
  exact hout (hHN.trans he.ge)

/-- Discharge every local solvable-recognition premise on the marked original
module, with earlier structure used only at the same G,T. -/
theorem augmentation_solvable_recognition_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ClassicalGroup.IsPSp G 3 2 := by
  have earlier := recognition_from_escaping_point h structural modules D z hz hzL hout
  obtain ⟨eL⟩ := augmentation_solvable_initial_quotient_at h₀ h structural D m z hz hzL hout hsolv
  have hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L := by
    rw [firstFlagCore_eq_firstParabolicCore_at h structural D m eL z hz hzL]
    exact ordinary_augmentation_baumann_alternative_of_largeDistance_at hl h structural D m eL z hz hzL
  have hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w :=
    fun v _ => ordinary_core_normalizer_fusion_at hl h₀ h structural D m earlier eL v
  have h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3) :=
    fun _ => augmentation_point_residual_at h structural D m z hz hzL hout
  have h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype = L :=
    fun _ => normalizer_primeToThree_residual_at h structural eL
  have hi := original_omega_fixed_index_at h₀ h structural D m earlier
  have hVJ := module_le_original_R1_thompson_of_ordinary_at h structural D m eL z hz hzL
  obtain ⟨_,_,_,_,_,hinter,_⟩ := centralizer_pair_quotient_of_original_R1_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hi h1342
  have hM := normalizer_eq_component_sylow_of_centralizer_intersection
    (normalizer_component_centralizer_supplement_at h structural D m z) hinter
  exact isPSp_of_original_R1_source_amalgam_at h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hi h1342
    (Amalgam.planeAmalgamSource1347_at hl h₀ h structural modules D m h1332 fixed covered
      h13316 hi hM)

/-- The original solvable-centralizer implication in both initial quotient
rows. Its faithful applicability and augmentation marking are constructed. -/
theorem original_solvable_recognition_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ClassicalGroup.IsPSp G 3 2 := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  exact augmentation_solvable_recognition_at hl h₀ h structural modules D m
    h1332 fixed covered h13316 z hz hzL hout hsolv

/-- Apply the solvable implication separately at every escaping omega point.
This supplies universal nonsolvability, including both nonconstant weights. -/
theorem original_universal_escaping_nonsolvable_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hnot : ¬ ClassicalGroup.IsPSp G 3 2) :
    ∀ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      z.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) := by
  intro z hz hzL hout hs
  exact hnot (original_solvable_recognition_at hl h₀ D hfixed structural modules
    h1332 fixed covered h13316 z hz hzL hout hs)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
