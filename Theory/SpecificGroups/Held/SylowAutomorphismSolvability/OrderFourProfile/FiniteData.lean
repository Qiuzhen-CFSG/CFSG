module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action

/-!
# Finite data for the Held order-four profile

The bit code is the image of the original reverse-PC normal form in the
Frattini coordinates. The proposed order-four flags are checked in blocks
against the actual four-point action; the count table is then evaluated using
only these flags. No equality of arbitrary permutations is inferred from a
four-point test. The bridge to actual powers is in `OrderFourProfile`.

Source: ATLAS HeG1-p2058B0, the existing `TwoGroup.Tables`, and the original
`IntrinsicEnumeration.Words` normal form. The local `Source/generate.py`
reproduces the proposed flags; the Lean kernel checks every finite assertion.
-/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

/-- The original word's quotient code, with masks `[1,2,4,4,8,8,8,8,8,0]`. -/
@[expose] public def indexCode (n : Fin 1024) : Nat :=
  n.val % 2 + 2 * (n.val / 2 % 2) +
    4 * ((n.val / 4 + n.val / 8) % 2) +
    8 * ((n.val / 16 + n.val / 32 + n.val / 64 + n.val / 128 + n.val / 256) % 2)

@[expose] public def hasOrderFour (n : Fin 1024) : Bool :=
  sameAction (normalFormAction n ^ 4) 1 && !sameAction (normalFormAction n ^ 2) 1

/-- Proposed flags, each certified against the literal action in `Checks`. -/
@[expose] public def orderFourTable (n : Fin 1024) : Bool :=
  (173798855762674718042566294314874042503223103110411777654692467753795387510097247662968849849036463812255423381496420592576329387513426968912561933593216411996270893117150979245066743075679055178924804056454041017210753099570599143631672019468434715015257773043034072513460084022911611052553070567372674199202 : Nat).testBit n.val

@[expose] public def countTable (n : Nat) : Nat :=
  #[16,64,48,32,32,64,48,64,48,48,48,64,64,64,64,0].getD n 0

@[expose] public def blockIndex (b : Fin 16) (k : Fin 64) : Fin 1024 :=
  ⟨64 * b.val + k.val, by omega⟩

end Held.SylowAutomorphismSolvability.OrderFourProfile
