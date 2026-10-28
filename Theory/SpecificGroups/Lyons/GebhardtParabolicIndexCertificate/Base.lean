module

public import Theory.SpecificGroups.Lyons.GebhardtLocalTowerSetup
public import Theory.GroupTheory.CosetWordCertificate

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

/-- Balanced lookup of packed pages; no proof history is reconstructed. -/
def lookupBranch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

/-- Fixed-width entries packed in pages of 128. -/
def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 128) >>> (bits * (i % 128))) % (2 ^ bits)

end Lyons.Gebhardt.ParabolicIndexCertificate
