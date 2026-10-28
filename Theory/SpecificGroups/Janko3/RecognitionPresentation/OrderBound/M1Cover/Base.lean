module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.EnumerationSetup

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 128) >>> (bits * (i % 128))) % (2 ^ bits)

def decode (a : Nat) : Letter (Fin 3) :=
  (⟨(a / 2) % 3, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
