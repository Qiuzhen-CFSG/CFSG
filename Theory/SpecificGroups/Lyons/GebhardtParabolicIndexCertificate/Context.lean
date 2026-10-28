module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.defCodeTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.LiteralRelators

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def decode (a : Nat) : Letter (Fin 3) := (⟨(a / 2) % 3, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

def definitions : Definitions (Fin 3) where
  parent n := min (defCode n / 8) (n - 1)
  letter n := decode (defCode n % 8)
  parent_lt n := by
    have := Nat.min_le_right (defCode (n + 1) / 8) (n + 1 - 1)
    omega

def context : Context (Fin 3) :=
  ⟨definitions.parent, definitions.letter, relatorWords,
    fun a => decide (a = (0, true) ∨ a = (1, true))⟩

end Lyons.Gebhardt.ParabolicIndexCertificate
