module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphSeparation.Recovery
import Mathlib.Tactic.FinCases

/-!
# Kernel-checked recovery of all Fi22 points

Each 64-point block checks the literal graph signatures and packed point map.
These linear-size checks prove the recovery specification for all 3510 points;
the extra indices in the final block simply repeat initial points modulo 3510.
No native decision procedure or mathematical assumption certifies the table.

Source: ATLAS F22G1-p3510B0; GLS3 Table 5.3t. Generated reproducibly by
`GraphSeparation/source/generate.py` from the existing Lean data.
-/

public section
namespace Sporadic.Fischer.Fi22.KernelCertificate.GraphSeparation

private theorem block0 :
    ∀ i : Fin 64, CorrectAt (64 * 0 + i.val) := by decide +kernel

private theorem block1 :
    ∀ i : Fin 64, CorrectAt (64 * 1 + i.val) := by decide +kernel

private theorem block2 :
    ∀ i : Fin 64, CorrectAt (64 * 2 + i.val) := by decide +kernel

private theorem block3 :
    ∀ i : Fin 64, CorrectAt (64 * 3 + i.val) := by decide +kernel

private theorem block4 :
    ∀ i : Fin 64, CorrectAt (64 * 4 + i.val) := by decide +kernel

private theorem block5 :
    ∀ i : Fin 64, CorrectAt (64 * 5 + i.val) := by decide +kernel

private theorem block6 :
    ∀ i : Fin 64, CorrectAt (64 * 6 + i.val) := by decide +kernel

private theorem block7 :
    ∀ i : Fin 64, CorrectAt (64 * 7 + i.val) := by decide +kernel

private theorem block8 :
    ∀ i : Fin 64, CorrectAt (64 * 8 + i.val) := by decide +kernel

private theorem block9 :
    ∀ i : Fin 64, CorrectAt (64 * 9 + i.val) := by decide +kernel

private theorem block10 :
    ∀ i : Fin 64, CorrectAt (64 * 10 + i.val) := by decide +kernel

private theorem block11 :
    ∀ i : Fin 64, CorrectAt (64 * 11 + i.val) := by decide +kernel

private theorem block12 :
    ∀ i : Fin 64, CorrectAt (64 * 12 + i.val) := by decide +kernel

private theorem block13 :
    ∀ i : Fin 64, CorrectAt (64 * 13 + i.val) := by decide +kernel

private theorem block14 :
    ∀ i : Fin 64, CorrectAt (64 * 14 + i.val) := by decide +kernel

private theorem block15 :
    ∀ i : Fin 64, CorrectAt (64 * 15 + i.val) := by decide +kernel

private theorem block16 :
    ∀ i : Fin 64, CorrectAt (64 * 16 + i.val) := by decide +kernel

private theorem block17 :
    ∀ i : Fin 64, CorrectAt (64 * 17 + i.val) := by decide +kernel

private theorem block18 :
    ∀ i : Fin 64, CorrectAt (64 * 18 + i.val) := by decide +kernel

private theorem block19 :
    ∀ i : Fin 64, CorrectAt (64 * 19 + i.val) := by decide +kernel

private theorem block20 :
    ∀ i : Fin 64, CorrectAt (64 * 20 + i.val) := by decide +kernel

private theorem block21 :
    ∀ i : Fin 64, CorrectAt (64 * 21 + i.val) := by decide +kernel

private theorem block22 :
    ∀ i : Fin 64, CorrectAt (64 * 22 + i.val) := by decide +kernel

private theorem block23 :
    ∀ i : Fin 64, CorrectAt (64 * 23 + i.val) := by decide +kernel

private theorem block24 :
    ∀ i : Fin 64, CorrectAt (64 * 24 + i.val) := by decide +kernel

private theorem block25 :
    ∀ i : Fin 64, CorrectAt (64 * 25 + i.val) := by decide +kernel

private theorem block26 :
    ∀ i : Fin 64, CorrectAt (64 * 26 + i.val) := by decide +kernel

private theorem block27 :
    ∀ i : Fin 64, CorrectAt (64 * 27 + i.val) := by decide +kernel

private theorem block28 :
    ∀ i : Fin 64, CorrectAt (64 * 28 + i.val) := by decide +kernel

private theorem block29 :
    ∀ i : Fin 64, CorrectAt (64 * 29 + i.val) := by decide +kernel

private theorem block30 :
    ∀ i : Fin 64, CorrectAt (64 * 30 + i.val) := by decide +kernel

private theorem block31 :
    ∀ i : Fin 64, CorrectAt (64 * 31 + i.val) := by decide +kernel

private theorem block32 :
    ∀ i : Fin 64, CorrectAt (64 * 32 + i.val) := by decide +kernel

private theorem block33 :
    ∀ i : Fin 64, CorrectAt (64 * 33 + i.val) := by decide +kernel

private theorem block34 :
    ∀ i : Fin 64, CorrectAt (64 * 34 + i.val) := by decide +kernel

private theorem block35 :
    ∀ i : Fin 64, CorrectAt (64 * 35 + i.val) := by decide +kernel

private theorem block36 :
    ∀ i : Fin 64, CorrectAt (64 * 36 + i.val) := by decide +kernel

private theorem block37 :
    ∀ i : Fin 64, CorrectAt (64 * 37 + i.val) := by decide +kernel

private theorem block38 :
    ∀ i : Fin 64, CorrectAt (64 * 38 + i.val) := by decide +kernel

private theorem block39 :
    ∀ i : Fin 64, CorrectAt (64 * 39 + i.val) := by decide +kernel

private theorem block40 :
    ∀ i : Fin 64, CorrectAt (64 * 40 + i.val) := by decide +kernel

private theorem block41 :
    ∀ i : Fin 64, CorrectAt (64 * 41 + i.val) := by decide +kernel

private theorem block42 :
    ∀ i : Fin 64, CorrectAt (64 * 42 + i.val) := by decide +kernel

private theorem block43 :
    ∀ i : Fin 64, CorrectAt (64 * 43 + i.val) := by decide +kernel

private theorem block44 :
    ∀ i : Fin 64, CorrectAt (64 * 44 + i.val) := by decide +kernel

private theorem block45 :
    ∀ i : Fin 64, CorrectAt (64 * 45 + i.val) := by decide +kernel

private theorem block46 :
    ∀ i : Fin 64, CorrectAt (64 * 46 + i.val) := by decide +kernel

private theorem block47 :
    ∀ i : Fin 64, CorrectAt (64 * 47 + i.val) := by decide +kernel

private theorem block48 :
    ∀ i : Fin 64, CorrectAt (64 * 48 + i.val) := by decide +kernel

private theorem block49 :
    ∀ i : Fin 64, CorrectAt (64 * 49 + i.val) := by decide +kernel

private theorem block50 :
    ∀ i : Fin 64, CorrectAt (64 * 50 + i.val) := by decide +kernel

private theorem block51 :
    ∀ i : Fin 64, CorrectAt (64 * 51 + i.val) := by decide +kernel

private theorem block52 :
    ∀ i : Fin 64, CorrectAt (64 * 52 + i.val) := by decide +kernel

private theorem block53 :
    ∀ i : Fin 64, CorrectAt (64 * 53 + i.val) := by decide +kernel

private theorem block54 :
    ∀ i : Fin 64, CorrectAt (64 * 54 + i.val) := by decide +kernel

private theorem all_blocks (b : Fin 55) :
    ∀ i : Fin 64, CorrectAt (64 * b.val + i.val) := by
  fin_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54

/-- Every graph signature recovers exactly the point and its `fastA` image. -/
theorem recoveryCorrect (x : Fin 3510) : RecoveryCorrect x := by
  have h := all_blocks ⟨x.val / 64, by omega⟩ ⟨x.val % 64, by omega⟩
  have hn : 64 * (x.val / 64) + x.val % 64 = x.val := by omega
  simpa only [CorrectAt, hn, Nat.mod_eq_of_lt x.isLt] using h

end Sporadic.Fischer.Fi22.KernelCertificate.GraphSeparation
