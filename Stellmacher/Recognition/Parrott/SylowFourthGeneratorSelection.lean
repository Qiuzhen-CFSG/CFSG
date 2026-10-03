module

public import Stellmacher.Recognition.Parrott.SylowCoreSelectionData
public import Stellmacher.Recognition.Parrott.SylowFourthCommutatorRow
public import Stellmacher.Recognition.Parrott.SylowFourthGeneration

/-!
# Completing the initial Sylow frame

Starting with the supplied three-generator frame, select an element `c` in
the original core whose central commutator row detects only `v`. The four
dual rows then generate the core by the central pairing and Frattini
argument. Applying `toInitial` retains every supplied coordinate and adds
only `c`, completing equations (9)–(10) and the core generation equality.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.673–674 and p.679, equations (9)–(10).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Complete the supplied three-generator frame by choosing only its fourth
core generator. -/
public theorem ParrottSylowThreeGeneratorData.exists_initial
    (f : ParrottSylowThreeGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSylowInitialData n) := by
  obtain ⟨c, hc, hcu, hcw, hct, hcv⟩ := f.exists_fourth_commutator_row h
  exact ⟨f.toInitial c hcu hcw hct hcv
    (f.fourth_generates h c hc hcu hcw hct hcv)⟩

end Stellmacher.Recognition
