module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
import Mathlib.Tactic.FinCases

/-!
# A concrete Sylow-two candidate in the local star action

Four permutations are certified as words in the two ATLAS local star generators.
Their generated subgroup is the common input for two independent obligations:
its order is 1024, and its involutions fuse to `starFirst` or
`(starFirst * starSecond)^7` inside `StarGroup`. Neither obligation is assumed
or asserted here. The quotient-to-star bridge and Sylow transfer consume them.

Source: the literal ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup`; `source/sylow.g` discovers the witnesses and
`source/generate.py` reflects them. GAP multiplication is opposite to Lean's
permutation composition, so the saved words are reversed before evaluation.
All reflected equalities below are checked by the kernel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality.QuotientCount.Image Theory.GroupTheory

/-- The first local generator in the concrete star group. -/
def starFirst : StarGroup := ⟨starX, Subgroup.subset_closure (by simp)⟩

/-- The second local generator in the concrete star group. -/
def starSecond : StarGroup := ⟨starY, Subgroup.subset_closure (by simp)⟩

def starAlphabet : Fin 4 → Equiv.Perm (Fin 24) :=
  ![starX, starY, starX⁻¹, starY⁻¹]

theorem starAlphabet_mem (i : Fin 4) : starAlphabet i ∈ StarGroup := by
  fin_cases i
  · exact starFirst.property
  · exact starSecond.property
  · exact StarGroup.inv_mem starFirst.property
  · exact StarGroup.inv_mem starSecond.property

def sylowPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 14, 2, 3, 6, 7, 4, 5, 8, 9, 22, 16, 23, 17, 1, 15, 11, 13, 20, 19, 18, 21, 10, 12]
  invFun := ![0, 14, 2, 3, 6, 7, 4, 5, 8, 9, 22, 16, 23, 17, 1, 15, 11, 13, 20, 19, 18, 21, 10, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sylowWord0 : List (Fin 4) :=
  [2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1]

theorem sylowPerm0_word : sylowPerm0 = evalWord starAlphabet sylowWord0 := by
  decide +kernel

theorem sylowPerm0_mem : sylowPerm0 ∈ StarGroup := by
  rw [sylowPerm0_word]
  exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _

def sylowPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![23, 11, 22, 20, 17, 8, 13, 15, 5, 18, 19, 1, 21, 6, 16, 7, 14, 4, 9, 10, 3, 12, 2, 0]
  invFun := ![23, 11, 22, 20, 17, 8, 13, 15, 5, 18, 19, 1, 21, 6, 16, 7, 14, 4, 9, 10, 3, 12, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sylowWord1 : List (Fin 4) :=
  [3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1]

theorem sylowPerm1_word : sylowPerm1 = evalWord starAlphabet sylowWord1 := by
  decide +kernel

theorem sylowPerm1_mem : sylowPerm1 ∈ StarGroup := by
  rw [sylowPerm1_word]
  exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _

def sylowPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 17, 2, 7, 13, 9, 16, 3, 20, 5, 10, 14, 12, 4, 11, 18, 6, 1, 15, 19, 8, 21, 22, 23]
  invFun := ![0, 17, 2, 7, 13, 9, 16, 3, 20, 5, 10, 14, 12, 4, 11, 18, 6, 1, 15, 19, 8, 21, 22, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sylowWord2 : List (Fin 4) :=
  [2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1]

theorem sylowPerm2_word : sylowPerm2 = evalWord starAlphabet sylowWord2 := by
  decide +kernel

theorem sylowPerm2_mem : sylowPerm2 ∈ StarGroup := by
  rw [sylowPerm2_word]
  exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _

def sylowPerm3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 5, 23, 4, 2, 16, 19, 15, 12, 22, 11, 9, 14, 13, 8, 6, 17, 18, 7, 20, 21, 10, 3]
  invFun := ![0, 1, 5, 23, 4, 2, 16, 19, 15, 12, 22, 11, 9, 14, 13, 8, 6, 17, 18, 7, 20, 21, 10, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sylowWord3 : List (Fin 4) :=
  [2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1]

theorem sylowPerm3_word : sylowPerm3 = evalWord starAlphabet sylowWord3 := by
  decide +kernel

theorem sylowPerm3_mem : sylowPerm3 ∈ StarGroup := by
  rw [sylowPerm3_word]
  exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _

/-- Generators with membership in the actual star group proved by words. -/
def sylowGenerator : Fin 4 → StarGroup :=
  ![⟨sylowPerm0, sylowPerm0_mem⟩, ⟨sylowPerm1, sylowPerm1_mem⟩,
    ⟨sylowPerm2, sylowPerm2_mem⟩, ⟨sylowPerm3, sylowPerm3_mem⟩]

/-- This fixed candidate is not declared Sylow until its order is certified. -/
def sylowCandidate : Subgroup StarGroup := Subgroup.closure (Set.range sylowGenerator)

end Janko4.Simplicity.Max1Fusion.QuotientInvolutions
