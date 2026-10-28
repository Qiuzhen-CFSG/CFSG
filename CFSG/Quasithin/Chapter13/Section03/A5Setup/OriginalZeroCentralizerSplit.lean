module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerSplit

/-!
# Original 13.3.1 consumer of the zero-center A₅ extension splitting

The original hypothesis constructs its Fundamental Setup and discharges the
natural-kernel and complement premises. The resulting homomorphic section
retains the literal quotient L/O₂(L). This is the alternating group-extension
input to 10.2.1 used by 13.3.2, not the remaining odd-transposition lift.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2, printed pp.742–743 and884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original zero-center source supplies an actual section of L→L/O₂(L). -/
theorem zero_centralizer_quotient_section
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ s : (L ⧸ pCore 2 L) →* L,
      (QuotientGroup.mk' (pCore 2 L)).comp s = MonoidHom.id _ := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_zero_centralizer_quotient_section D e hn hout hz

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
