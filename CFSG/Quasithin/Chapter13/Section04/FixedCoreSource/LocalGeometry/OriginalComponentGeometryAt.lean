module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentCoveredNaturalAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixGeometryAt

/-!
# Geometry at every original nonsolvable escaping point

Construct the original augmentation marking and Chapter 12 guard, then
choose the relatively normal escaping component from 13.3.2. The guarded
exclusions leave linear-three or ordinary A₆. Their complete moved-module
arguments supply the actual chosen module, the ordinary original quotient,
L₁ containment, the central four-group, and both reciprocal residuals.
The original fixed line and the escaping involution generate the full seed.

This is the original-module application of both selected component rows;
no selected component, module marking, fixed-space case or exhaustive-list
callback is supplied. The earlier source/module clauses and natural
LargeDistanceInput remain explicit. OriginalComponentPairAt constructs the actual 13.4.7 pair. The guarded
amalgam and final 13.4.1 recognition remain to be assembled.
Source: Aschbacher--Smith 13.4.10(1--6), printed pp.907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the source geometry on the original fixed module, separately
at every nonsolvable escaping point. Both surviving component rows are handled. -/
theorem original_escaping_component_geometry_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ m : CoreMarking D, ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) ∧
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let H := K ⊔ (T : Subgroup G)
      let U := ⁅conjugateSpanBy Z K,K⁆
      ∃ DK : ChosenModule T K U,
        Nonempty (ComponentModuleAt DK z.val) ∧
        U = ⁅(ReducedModule H).map H.subtype,K⁆ ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        Solvable.firstCentralizerResidual L z.val ≤ K ∧
        primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
        Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
        Solvable.firstCentralizerResidual K m.constant.val =
          Solvable.firstCentralizerResidual L z.val ∧
        (pResidual 2 (K ⊓ centralizer (Z : Set G) : Subgroup G)).map
            (K ⊓ centralizer (Z : Set G)).subtype =
          (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
            (L ⊓ centralizer ({z.val} : Set G)).subtype ∧
        Z ⊓ centralizer (K : Set G) = zpowers z.val ∧
        conjugateSpanBy Z K = U ⊔ zpowers z.val := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨K,hK,hfK,hstarK,hKN,hTK,hKM,hLK⟩ :=
    augmentation_exists_escaping_component_at h₀ h structural m h1332 hzT hz1 hout hnonsolv
  have hrows := selected_component_rows_at hl h₀ h structural D m h1332 fixed five covered
    h13316 hindex z hzT hzL hK hKN hKM hfK
  refine ⟨m,K,hK,hfK,hstarK,hKN,hTK,hKM,hLK,hrows,?_⟩
  have hfix := component_full_fixed_line_at h structural z.val hz1 hzT hindex K hK.1 hKM
  have hsplit := component_seed_split h₀ hzT hz1 hK.1 hTK
  rw [hfix] at hsplit
  rcases hrows with h3 | h6
  · obtain ⟨eK⟩ := h3
    obtain ⟨DK,mark,hL,hres,hrank,hrec,htwo,hwhole,_,hZ,hcard,_⟩ :=
      linear_component_geometry_at hl h₀ h structural modules D m h1332 fixed hindex
        z hzT hzL hK.1 hKN hKM hfK eK
    exact ⟨DK,mark,hwhole,hL,hres,hrank,hZ,hcard,hrec,htwo,hfix,hsplit⟩
  · obtain ⟨eK⟩ := h6
    obtain ⟨DK,mark,hwhole,hL,hres,hrank,hZ,hcard,hrec,htwo⟩ :=
      ordinary_six_component_geometry_at h₀ h structural modules D m h1332 fixed hindex
        z hzT hzL hK hKN hKM hfK eK
    exact ⟨DK,mark,hwhole,hL,hres,hrank,hZ,hcard,hrec,htwo,hfix,hsplit⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
