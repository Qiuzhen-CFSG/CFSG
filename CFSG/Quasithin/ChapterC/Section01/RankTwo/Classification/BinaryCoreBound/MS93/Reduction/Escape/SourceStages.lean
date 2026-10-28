module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.SourceProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation

/-!
# Complete source stages preceding the final MS93 (4.3) contradiction

All initial, local-control, general edge-transfer and propagation producers
are instantiated using only the original source, geometry, distance bound,
module facts and normalization transfer. The propagation package retains
the source's relative-normalizer bound as well as the original interface.

The final contradiction at the bottom of printed p.889 and on p.890 is
not asserted here: it still needs the third orbit neighbor and radius-six
argument. This checked package is the complete earlier input to that proof.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.SourceStages

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- All source stages through (4.3.8), with every earlier producer applied
and no assumed initial, local-control, edge-transfer or propagation premise. -/
theorem sourceStages (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) :
    (∀ p : Counterexample geometry, Nonempty (InitialFacts p)) ∧
      (∀ p : Counterexample geometry, LocalControl p) ∧
      Escape.EdgeTransfer geometry ∧ PropagationFacts geometry ∧
      Propagation.Backward.Products.Selection.RelativeBoundFacts geometry := by
  have initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p) :=
    Initial.initialFacts source geometry hb modules
  have control : ∀ p : Counterexample geometry, LocalControl p :=
    PairingControl.SourceProof.localControl_of_source source hb modules transfer initial
  have edge : Escape.EdgeTransfer geometry := EdgeTransfer.edgeTransfer hb modules
  obtain ⟨propagation, relative⟩ :=
    Propagation.sourcePropagationFacts source hb modules transfer initial control edge
  exact ⟨initial, control, edge, propagation, relative⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.SourceStages
