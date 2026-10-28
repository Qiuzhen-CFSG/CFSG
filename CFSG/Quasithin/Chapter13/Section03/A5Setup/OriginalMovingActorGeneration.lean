module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterTransvection
public import CFSG.Quasithin.Chapter10.SourceA5MovingActorGeneration
/-!
# Residual generation for the original fixed-center transvection

The actual Hypothesis 13.3.1 setup supplies a transvection on the reduced
HStar orbit module whose normal closure contains O²(H). Its normal closure
therefore generates all displacement on the orbit module. This is the
residual input for restricting the faithful action to the moved module.
Source: Aschbacher--Smith 10.2.1 and 13.3.2(2), printed pp.743,884--885.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_transvection_with_residual_generation
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
       ∃ g : H, (g : G) ∈ (T : Subgroup G) ⊓ localOrbit T L ∧
         ∃ v ∈ W, v ≠ 1 ∧
         (∀ x ∈ W, ⁅(g:G),x⁆ = 1 ∨ ⁅(g:G),x⁆ = v) ∧
         (∃ x ∈ W, ⁅(g:G),x⁆ = v) ∧
         pResidual 2 H ≤ normalClosure ({g} : Set H) ∧
         ⁅W,H⁆ = ⁅W,(normalClosure ({g} : Set H)).map H.subtype⁆) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_exists_fixed_center_transvection_with_residual_generation
    D e hn hne hout
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
