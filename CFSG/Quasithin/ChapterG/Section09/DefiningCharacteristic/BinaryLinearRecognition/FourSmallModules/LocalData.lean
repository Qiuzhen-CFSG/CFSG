module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Rank-one relations for binary SL₄ modules

A local highest vector is fixed by the six positive root transvections.
Each of the three simple roots either fixes it under coordinate exchange or
satisfies the binary three-term relation. For a nonzero vector these
alternatives are disjoint, so support is determined by the actual action.
No existence or classification statement is included in this definition.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

abbrev Group := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)

/-- The adjacent lower transvection, adding coordinate `i` to coordinate `i+1`. -/
def simpleLower (i : Fin 3) : Group :=
  Matrix.SpecialLinearGroup.transvection
    (i := i.succ) (j := i.castSucc) (by intro h; have := congrArg Fin.val h; simp at this)
    (1 : ZMod 2)

/-- The adjacent upper transvection. -/
def simpleUpper (i : Fin 3) : Group :=
  Matrix.SpecialLinearGroup.transvection
    (i := i.castSucc) (j := i.succ) (by intro h; have := congrArg Fin.val h; simp at this)
    (1 : ZMod 2)

/-- Exchange the adjacent coordinates `i` and `i+1`. -/
def simpleSwap (i : Fin 3) : Group :=
  simpleLower i * simpleUpper i * simpleLower i

/-- Conjugating the upper transvection by the exchange gives the lower one. -/
theorem simpleLower_eq_swap_upper_swap (i : Fin 3) :
    simpleLower i = simpleSwap i * simpleUpper i * simpleSwap i := by
  revert i
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixedness under the positive root groups, stated on their generators. -/
def UpperFixed (ρ : Representation (ZMod 2) Group V) (v : V) : Prop :=
  ∀ (i j : Fin 4) (hij : i < j),
    ρ (Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) (1 : ZMod 2)) v = v

/-- Explicit rank-one alternatives for an upper-fixed vector. The support is
the set of roots with the three-term alternative. Nonzeroness is kept separate. -/
structure LocalHighestVector (ρ : Representation (ZMod 2) Group V)
    (J : Finset (Fin 3)) (v : V) : Prop where
  upper_fixed : UpperFixed ρ v
  inactive_fixed : ∀ i, i ∉ J → ρ (simpleSwap i) v = v
  active_relation : ∀ i, i ∈ J → v + ρ (simpleSwap i) v + ρ (simpleLower i) v = 0

private theorem binary_add_self (v : V) : v + v = 0 := by
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [htwo, zero_smul]

/-- An active root necessarily moves a nonzero local highest vector. -/
theorem LocalHighestVector.swap_ne_self
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i : Fin 3} (hi : i ∈ J) :
    ρ (simpleSwap i) v ≠ v := by
  intro hswap
  have hu : ρ (simpleUpper i) v = v :=
    h.upper_fixed i.castSucc i.succ (by simp)
  have hl : ρ (simpleLower i) v = v := by
    rw [simpleLower_eq_swap_upper_swap, map_mul, map_mul]
    change ρ (simpleSwap i) (ρ (simpleUpper i) (ρ (simpleSwap i) v)) = v
    rw [hswap, hu, hswap]
  have hr := h.active_relation i hi
  rw [hswap, hl, binary_add_self, zero_add] at hr
  exact hv hr

/-- The support can be recovered from the action on any nonzero local highest
vector; it is not an arbitrary choice of labels. -/
theorem LocalHighestVector.mem_iff_swap_ne_self
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) (i : Fin 3) :
    i ∈ J ↔ ρ (simpleSwap i) v ≠ v := by
  constructor
  · exact h.swap_ne_self hv
  · intro hi
    by_contra hnot
    exact hi (h.inactive_fixed i hnot)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
