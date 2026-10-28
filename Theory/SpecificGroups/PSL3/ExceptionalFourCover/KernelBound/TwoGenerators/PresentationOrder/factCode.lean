module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.factCodeData00

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def factCode (i : Nat) : Nat :=
  unpack (branch 384 (branch 192 (branch 96 (branch 32 factCodePage0 (branch 64 factCodePage32 factCodePage64)) (branch 128 factCodePage96 (branch 160 factCodePage128 factCodePage160))) (branch 288 (branch 224 factCodePage192 (branch 256 factCodePage224 factCodePage256)) (branch 320 factCodePage288 (branch 352 factCodePage320 factCodePage352)))) (branch 576 (branch 480 (branch 416 factCodePage384 (branch 448 factCodePage416 factCodePage448)) (branch 512 factCodePage480 (branch 544 factCodePage512 factCodePage544))) (branch 672 (branch 608 factCodePage576 (branch 640 factCodePage608 factCodePage640)) (branch 736 (branch 704 factCodePage672 factCodePage704) (branch 768 factCodePage736 factCodePage768))))) 33 i

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
