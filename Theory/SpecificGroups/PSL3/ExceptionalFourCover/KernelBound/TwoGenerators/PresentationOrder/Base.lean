module

public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 64) >>> (bits * (i % 64))) % (2 ^ bits)

def decode (a : Nat) : Letter (Fin 2) :=
  (⟨(a / 2) % 2, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
