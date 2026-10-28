module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceBaumannFixedCenter

/-!
# The original fixed-center auxiliary group in the A₅ branch

Hypothesis 13.3.1 supplies the Fundamental Setup on the original component.
The fixed-center argument then selects H* inside the escaping Baumann
normalizer and constructs its actual reduced Sylow-center span. Its full
centralizer lies in the original maximal normalizer M, so H acts nontrivially.
No auxiliary quotient, module marking or overgroup is postulated.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal 13.3.1 input constructs the original nonzero fixed-center
configuration of 10.2.1. -/
theorem exists_original_fixed_center_setup
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
       ¬ H ≤ centralizer (W : Set G)) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_baumann_HStar_fixed_center_setup D hne hout

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
