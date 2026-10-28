module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterAction
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterTransvection
/-!
# The original Hypothesis 13.3.1 fixed-center transvection

The genuine original setup supplies the reduced HStar orbit module and an
actual residual Sylow actor whose nonzero displacement is a single line.
This consumes the paired displacement and Sylow-product actor selection
without an action marking or chosen-factor alignment premise.
Source: Aschbacher--Smith 10.2.1 and 13.3.2(2), printed pp.743,884--885.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_transvection
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
       ∃ g ∈ (T : Subgroup G) ⊓ localOrbit T L, ∃ v ∈ W, v ≠ 1 ∧
         (∀ x ∈ W, ⁅g,x⁆ = 1 ∨ ⁅g,x⁆ = v) ∧ ∃ x ∈ W, ⁅g,x⁆ = v) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_exists_fixed_center_transvection D e hn hne hout
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
