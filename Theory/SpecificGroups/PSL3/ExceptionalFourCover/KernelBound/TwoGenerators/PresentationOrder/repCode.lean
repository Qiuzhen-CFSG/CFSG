module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.repCodeData00

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def repCode (i : Nat) : Nat :=
  unpack (branch 32 repCodePage0 repCodePage32) 15 i

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
