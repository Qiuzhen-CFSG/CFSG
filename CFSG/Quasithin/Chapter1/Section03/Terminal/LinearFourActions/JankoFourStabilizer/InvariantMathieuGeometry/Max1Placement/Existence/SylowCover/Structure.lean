module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.Reduction

/-!
# Constructing the normal elementary witness from two-core and order inputs

The normal closure in M of the center of its restricted ambient Sylow is
nontrivial. Nontriviality of O₂(M) makes it elementary abelian by the
center-intersection argument in `Structure.Reduction`. The independent
order spectrum then gives the exact relative-normal witness required by
`NormalElementaryStructure`.

This assembly is conditional: neither `MaximalTwoCoreNontrivial` nor
`CentralClosureOrderSpectrum` is discharged here. In particular, the
unconditional `normalElementaryStructure` remains open. Final assembly
belongs to this module once both inputs have been proved.

Source: Aschbacher–Smith A.3.12 and its sporadic Sylow-overgroup argument,
printed pp.47–48, citing Aschbacher (1986); Kleidman–Wilson (1988),
pp.484–510. The quotient list in A.3.12 does not prove these inputs.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

/-- Actual application of the canonical closure construction to the exact
existence contract. Both independent J₄ inputs remain explicit. -/
theorem normalElementaryStructure_of_core_and_centralClosure_order
    (hcore : MaximalTwoCoreNontrivial) (horder : CentralClosureOrderSpectrum) :
    NormalElementaryStructure := by
  intro S M hM hSM
  have he := centralClosure_elementary_of_twoCore_ne_bot S M hSM (hcore S M hM hSM)
  exact ⟨centralClosure S M hSM, inferInstance, he, horder S M hM hSM he⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
