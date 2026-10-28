module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenter
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterAction

/-!
# The original nontrivial orbit action under Hypothesis13.3.1

Construct the actual H* in the escaping Baumann normalizer, retaining its
reduced Sylow-center span W. The original orbit intersection T∩L₀ acts
nontrivially on W by the Frattini argument and the common-normal bound.
This strengthens the fixed-center setup by discharging the nontrivial
orbit-action input before the transvection step of10.2.1.
Source: Aschbacher–Smith,10.2.1 and13.3.2(2),pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_orbit_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G)
        (normalizer (localOrbit T L : Set G)) ∧
      H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
       W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
       IsPReduced 2 (W.subgroupOf H) ∧
       H ⊓ centralizer (W : Set G) ≤ normalizer (localOrbit T L : Set G) ∧
       ¬ (T : Subgroup G) ⊓ localOrbit T L ≤ centralizer (W : Set G)) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  obtain ⟨H,hH,hHN,hWE,hred,hcent,_⟩ :=
    Chapter10.source_baumann_HStar_fixed_center_setup D hne hout
  exact ⟨H,hH,hHN,hWE,hred,hcent,
    Chapter10.source_a5_fixed_center_orbit_action D e hn hne H hH⟩
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
