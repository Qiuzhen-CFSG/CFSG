module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.factCode

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def facts (n : Nat) : FactData (Fin 2) :=
  let c := factCode n
  let a := c / 32768 % 8
  ⟨c % 32768, if a == 0 then [] else [decode (a-1)], c / 262144⟩

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
