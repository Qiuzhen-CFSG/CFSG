module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.opCodeData00

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def opCode (i : Nat) : Nat :=
  unpack (branch 384 (branch 192 (branch 96 (branch 32 opCodePage0 (branch 64 opCodePage32 opCodePage64)) (branch 128 opCodePage96 (branch 160 opCodePage128 opCodePage160))) (branch 288 (branch 224 opCodePage192 (branch 256 opCodePage224 opCodePage256)) (branch 320 opCodePage288 (branch 352 opCodePage320 opCodePage352)))) (branch 576 (branch 480 (branch 416 opCodePage384 (branch 448 opCodePage416 opCodePage448)) (branch 512 opCodePage480 (branch 544 opCodePage512 opCodePage544))) (branch 672 (branch 608 opCodePage576 (branch 640 opCodePage608 opCodePage640)) (branch 736 (branch 704 opCodePage672 opCodePage704) (branch 768 opCodePage736 opCodePage768))))) 35 i

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
