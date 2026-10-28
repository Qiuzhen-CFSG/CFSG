module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.opCode
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.scanHeader
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.scanLeft
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.scanRight
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Scan

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def refs : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, c => if c == 0 then [] else (c % 524288 - 1) :: refs n (c >>> 19)

def instructions (n : Nat) : Scan.Op (Fin 3) :=
  let c := opCode n
  let a := c / 8 % 1048576
  let b := c / 8388608
  match c % 8 with
  | 0 => .basic (.refl a)
  | 1 => .basic (.defining a)
  | 2 => .basic (.subgroup (decode a))
  | 3 => .basic (.relator a b)
  | 4 => .basic (.reverse a)
  | 5 => .basic (.compose a b)
  | _ => .scan (scanHeader a / 2048) (scanHeader a % 2048)
      (refs 56 (scanLeft a)) (refs 56 (scanRight a))

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
