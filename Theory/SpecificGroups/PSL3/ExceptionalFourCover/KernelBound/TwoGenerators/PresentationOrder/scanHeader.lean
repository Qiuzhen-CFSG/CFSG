module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.scanHeaderData00

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def scanHeader (i : Nat) : Nat :=
  unpack (branch 32 scanHeaderPage0 (branch 64 scanHeaderPage32 scanHeaderPage64)) 22 i

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
