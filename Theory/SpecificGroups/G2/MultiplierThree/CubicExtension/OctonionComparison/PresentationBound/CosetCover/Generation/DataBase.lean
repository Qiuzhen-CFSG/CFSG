module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.Replay

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def lookup {α : Type*} (cut : Nat) (l r : Nat → α) (i : Nat) : α :=
  if i < cut then l i else r i

def decodeWord (w : List Nat) : Word Label :=
  w.map fun a => (⟨a / 2 % 367, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

def singleWord (code : Nat) : Word Label :=
  if code = 0 then [] else
    [(⟨((code - 1) / 2) % 367, Nat.mod_lt _ (by decide)⟩, code % 2 == 1)]

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
