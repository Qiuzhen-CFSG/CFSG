module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData

/-!
# Difference operators at active roots of binary SL₄

An upper-root difference kills the highest vector. At an active root it
recovers that vector from its coordinate-exchange translate. These direct
rank-one consequences feed the independent-vector dimension bounds.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

private theorem upper_mul_swap (i : Fin 3) :
    simpleUpper i * simpleSwap i = simpleLower i * simpleUpper i := by
  revert i
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_add_self (x : V) : x + x = 0 := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh

/-- The difference between an upper simple transvection and the identity. -/
def upperDifference (ρ : Representation (ZMod 2) Group V) (i : Fin 3) : V →ₗ[ZMod 2] V :=
  ρ (simpleUpper i) - LinearMap.id

/-- Every upper simple-root difference kills the highest vector. -/
theorem LocalHighestVector.upperDifference_self
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (i : Fin 3) : upperDifference ρ i v = 0 := by
  have hu := h.upper_fixed i.castSucc i.succ (by simp)
  change ρ (simpleUpper i) v = v at hu
  change ρ (simpleUpper i) v - v = 0
  rw [hu, sub_self]

/-- At an active root, the difference recovers the highest vector from its exchange translate. -/
theorem LocalHighestVector.upperDifference_swap
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) {i : Fin 3} (hi : i ∈ J) :
    upperDifference ρ i (ρ (simpleSwap i) v) = v := by
  have hu := h.upper_fixed i.castSucc i.succ (by simp)
  change ρ (simpleUpper i) v = v at hu
  have ha := h.active_relation i hi
  have hl : ρ (simpleLower i) v = v + ρ (simpleSwap i) v := by
    have ht := congrArg (fun x => x + ρ (simpleLower i) v) ha
    simpa only [add_assoc, binary_add_self, add_zero, zero_add] using ht.symm
  have he : ρ (simpleUpper i) (ρ (simpleSwap i) v) = v + ρ (simpleSwap i) v := by
    calc
      _ = ρ (simpleUpper i * simpleSwap i) v := by rw [map_mul]; rfl
      _ = ρ (simpleLower i * simpleUpper i) v := by rw [upper_mul_swap]
      _ = ρ (simpleLower i) v := by
        rw [map_mul]
        change ρ (simpleLower i) (ρ (simpleUpper i) v) = _
        rw [hu]
      _ = _ := hl
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) - ρ (simpleSwap i) v = v
  rw [he, add_sub_cancel_right]

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
