module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.opCode
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.scanHeader
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.scanLeft
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.scanRight

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def refs : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, c => if c == 0 then [] else (c % 65536 - 1) :: refs n (c >>> 16)

def instructions (n : Nat) : Scan.Op (Fin 2) :=
  let c := opCode n
  let a := c / 8 % 65536
  let b := c / 524288
  match c % 8 with
  | 0 => .basic (.refl a)
  | 1 => .basic (.defining a)
  | 2 => .basic (.subgroup (decode a))
  | 3 => .basic (.relator a b)
  | 4 => .basic (.reverse a)
  | 5 => .basic (.compose a b)
  | _ => .scan (scanHeader a / 128) (scanHeader a % 128)
      (refs 13 (scanLeft a)) (refs 13 (scanRight a))

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
