module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.defCodeData00

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def defCode (i : Nat) : Nat :=
  unpack (branch 128 (branch 64 (branch 32 defCodePage0 defCodePage32) (branch 96 defCodePage64 defCodePage96)) (branch 192 (branch 160 defCodePage128 defCodePage160) (branch 224 defCodePage192 (branch 256 defCodePage224 defCodePage256)))) 17 i

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
