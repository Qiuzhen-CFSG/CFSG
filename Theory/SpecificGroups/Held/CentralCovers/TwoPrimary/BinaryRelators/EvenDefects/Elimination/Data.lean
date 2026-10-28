module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Data.Block005

/-!
# The checked comparison prefix and additional literal facts

Source: John Bray, ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The producer supplies data only. All equality and tail checks run in the kernel.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Data
open Comparison Comparison.Replay

noncomputable def db (n : Nat) : Fact :=
  if n < 17223 then Comparison.Data.db n else (if n < 23367 then (if n < 19271 then Block000.db n else (if n < 21319 then Block001.db n else Block002.db n)) else (if n < 25415 then Block003.db n else (if n < 27463 then Block004.db n else Block005.db n)))

def initialCount : Nat := 17448
def factCount : Nat := 29040

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Data
