module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.opCode
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.scanHeader
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.scanLeft
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.scanRight
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def refs : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, c => if c == 0 then [] else (c % 131072 - 1) :: refs n (c >>> 17)

def instructions (n : Nat) : Scan.Op Bool :=
  let c := opCode n
  let a := c / 8 % 131072
  let b := c / 1048576
  match c % 8 with
  | 0 => .basic (.refl a)
  | 1 => .basic (.defining a)
  | 2 => .basic (.subgroup (decode a))
  | 3 => .basic (.relator a b)
  | 4 => .basic (.reverse a)
  | 5 => .basic (.compose a b)
  | _ => .scan (scanHeader a / 4096) (scanHeader a % 4096)
      (refs 72 (scanLeft a)) (refs 72 (scanRight a))

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
