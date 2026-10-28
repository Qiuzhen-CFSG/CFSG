module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Data.Block008

/-!
# Balanced lookup of literal central-tail equations

Source: John Bray, ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The producer supplies data only. All equality and tail checks run in the kernel.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Data
open Replay

noncomputable def db (n : Nat) : Fact :=
  (if n < 8192 then (if n < 4096 then (if n < 2048 then Block000.db n else Block001.db n) else (if n < 6144 then Block002.db n else Block003.db n)) else (if n < 12288 then (if n < 10240 then Block004.db n else Block005.db n) else (if n < 14336 then Block006.db n else (if n < 16384 then Block007.db n else Block008.db n))))

def initialCount : Nat := 3098
def factCount : Nat := 17223

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Data
