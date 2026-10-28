module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.SourceProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial

/-!
# Source boundary for binary MS93 (4.3.2)

The initial assertions (4.3.1) supply the earlier input to the complete
selected-path pairing argument. This yields both clauses of (4.3.2):
the full-radius commutator lies in the fixed core, and H equals the two
specified edge commutators for every moving neighbor on the first edge.

`localControl` supplies the uniform local-control input used by the parent
escape and propagation arguments. It requires only their local source,
geometry, distance, module and normalization inputs. The original conditional
assembly and the more general `SourceProof.localControl_of_source` remain
available through this extension. The final (4.3) contradiction belongs to
the parent escape proof.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)--(4.3.2),
printed pp.882--886.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

/-- Both clauses of binary MS93 (4.3.2), with the earlier (4.3.1) input
constructed from the source hypotheses. -/
theorem localControl (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) :
    ∀ p : Counterexample geometry, LocalControl p :=
  SourceProof.localControl_of_source source hb modules transfer
    (Initial.initialFacts source geometry hb modules)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
