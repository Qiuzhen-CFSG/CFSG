module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData
import Mathlib.Tactic.FinCases
/-!
# Checked ambient conjugators for star involution fusion

These 25 permutation tables are certified as words in `starAlphabet`, so the
conjugators belong to the actual `StarGroup`. GAP words are reversed to account
for Lean's permutation multiplication. The target flag selects `starFirst`
or `(starFirst * starSecond)^7`; `Checks` verifies the conjugacy equations.

Source: the exploratory witnesses in `../source/fusion.json` and conventions
in `../source/README.md`. All word identities are checked by kernel reduction;
no GAP class enumeration or class-size assertion is assumed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
open Cardinality.QuotientCount.Image Theory.GroupTheory

def repPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![4, 22, 15, 13, 12, 3, 5, 23, 18, 14, 0, 9, 7, 16, 6, 11, 2, 10, 17, 8, 21, 20, 1, 19]
  invFun := ![10, 22, 16, 5, 0, 6, 14, 12, 19, 11, 17, 15, 4, 3, 9, 2, 13, 18, 8, 23, 21, 20, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord0 : List (Fin 4) := [1, 2, 3, 2, 3, 3, 0, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0]

theorem repPerm0_word : repPerm0 = evalWord starAlphabet repWord0 := by
  decide +kernel

def repConjugator0 : StarGroup :=
  ⟨repPerm0, by
    rw [repPerm0_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 4, 18, 8, 7, 3, 21, 23, 22, 15, 16, 19, 0, 14, 13, 9, 17, 20, 12, 11, 10, 6, 5, 1]
  invFun := ![12, 23, 0, 5, 1, 22, 21, 4, 3, 15, 20, 19, 18, 14, 13, 9, 10, 16, 2, 11, 17, 6, 8, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord1 : List (Fin 4) := [2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3]

theorem repPerm1_word : repPerm1 = evalWord starAlphabet repWord1 := by
  decide +kernel

def repConjugator1 : StarGroup :=
  ⟨repPerm1, by
    rw [repPerm1_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![4, 9, 15, 11, 12, 3, 5, 18, 14, 23, 20, 2, 0, 6, 10, 21, 22, 16, 17, 1, 13, 7, 19, 8]
  invFun := ![12, 19, 11, 5, 0, 6, 13, 21, 23, 1, 14, 3, 4, 20, 8, 2, 17, 18, 7, 22, 10, 15, 16, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord2 : List (Fin 4) := [1, 0, 1, 0, 3, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1]

theorem repPerm2_word : repPerm2 = evalWord starAlphabet repWord2 := by
  decide +kernel

def repConjugator2 : StarGroup :=
  ⟨repPerm2, by
    rw [repPerm2_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm3 : Equiv.Perm (Fin 24) where
  toFun := ![13, 8, 17, 18, 14, 19, 4, 20, 7, 21, 11, 15, 23, 1, 3, 0, 6, 9, 2, 22, 5, 12, 10, 16]
  invFun := ![15, 13, 18, 14, 6, 20, 16, 8, 1, 17, 22, 10, 21, 0, 4, 11, 23, 2, 3, 5, 7, 9, 19, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord3 : List (Fin 4) := [3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0]

theorem repPerm3_word : repPerm3 = evalWord starAlphabet repWord3 := by
  decide +kernel

def repConjugator3 : StarGroup :=
  ⟨repPerm3, by
    rw [repPerm3_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm4 : Equiv.Perm (Fin 24) where
  toFun := ![5, 4, 12, 18, 8, 3, 20, 23, 13, 11, 16, 0, 10, 1, 15, 14, 7, 19, 17, 6, 21, 22, 9, 2]
  invFun := ![11, 13, 23, 5, 1, 0, 19, 16, 4, 22, 12, 9, 2, 8, 15, 14, 10, 18, 3, 17, 6, 20, 21, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord4 : List (Fin 4) := [2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]

theorem repPerm4_word : repPerm4 = evalWord starAlphabet repWord4 := by
  decide +kernel

def repConjugator4 : StarGroup :=
  ⟨repPerm4, by
    rw [repPerm4_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm5 : Equiv.Perm (Fin 24) where
  toFun := ![19, 13, 14, 9, 22, 8, 11, 4, 7, 6, 18, 17, 1, 23, 16, 0, 10, 12, 5, 3, 2, 20, 21, 15]
  invFun := ![15, 12, 20, 19, 7, 18, 9, 8, 5, 3, 16, 6, 17, 1, 2, 23, 14, 11, 10, 0, 21, 22, 4, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord5 : List (Fin 4) := [2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2]

theorem repPerm5_word : repPerm5 = evalWord starAlphabet repWord5 := by
  decide +kernel

def repConjugator5 : StarGroup :=
  ⟨repPerm5, by
    rw [repPerm5_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm6 : Equiv.Perm (Fin 24) where
  toFun := ![4, 9, 18, 15, 16, 3, 12, 11, 13, 0, 14, 22, 1, 2, 10, 21, 6, 5, 7, 23, 20, 19, 17, 8]
  invFun := ![9, 12, 13, 5, 0, 17, 16, 18, 23, 1, 14, 7, 6, 8, 10, 3, 4, 22, 2, 21, 20, 15, 11, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord6 : List (Fin 4) := [3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0]

theorem repPerm6_word : repPerm6 = evalWord starAlphabet repWord6 := by
  decide +kernel

def repConjugator6 : StarGroup :=
  ⟨repPerm6, by
    rw [repPerm6_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm7 : Equiv.Perm (Fin 24) where
  toFun := ![10, 4, 21, 14, 9, 20, 5, 18, 16, 1, 22, 8, 15, 0, 2, 23, 7, 6, 11, 19, 12, 13, 17, 3]
  invFun := ![13, 9, 14, 23, 1, 6, 17, 16, 11, 4, 0, 18, 20, 21, 3, 12, 8, 22, 7, 19, 5, 2, 10, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord7 : List (Fin 4) := [3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0]

theorem repPerm7_word : repPerm7 = evalWord starAlphabet repWord7 := by
  decide +kernel

def repConjugator7 : StarGroup :=
  ⟨repPerm7, by
    rw [repPerm7_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm8 : Equiv.Perm (Fin 24) where
  toFun := ![2, 6, 15, 17, 7, 3, 22, 21, 18, 23, 9, 19, 8, 0, 1, 11, 12, 5, 14, 4, 13, 16, 10, 20]
  invFun := ![13, 14, 0, 5, 19, 17, 1, 4, 12, 10, 22, 15, 16, 20, 18, 2, 21, 3, 8, 11, 23, 7, 6, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord8 : List (Fin 4) := [3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0]

theorem repPerm8_word : repPerm8 = evalWord starAlphabet repWord8 := by
  decide +kernel

def repConjugator8 : StarGroup :=
  ⟨repPerm8, by
    rw [repPerm8_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm9 : Equiv.Perm (Fin 24) where
  toFun := ![2, 4, 14, 18, 15, 11, 20, 3, 9, 23, 6, 0, 13, 8, 1, 22, 7, 19, 16, 17, 5, 12, 10, 21]
  invFun := ![11, 14, 0, 7, 1, 20, 10, 16, 13, 8, 22, 5, 21, 12, 2, 4, 18, 19, 3, 17, 6, 23, 15, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord9 : List (Fin 4) := [2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0]

theorem repPerm9_word : repPerm9 = evalWord starAlphabet repWord9 := by
  decide +kernel

def repConjugator9 : StarGroup :=
  ⟨repPerm9, by
    rw [repPerm9_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm10 : Equiv.Perm (Fin 24) where
  toFun := ![12, 21, 5, 9, 15, 4, 20, 8, 22, 6, 11, 1, 0, 14, 3, 16, 19, 18, 23, 2, 17, 10, 13, 7]
  invFun := ![12, 11, 19, 14, 5, 2, 9, 23, 7, 3, 21, 10, 0, 22, 13, 4, 15, 20, 17, 16, 6, 1, 8, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord10 : List (Fin 4) := [2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3]

theorem repPerm10_word : repPerm10 = evalWord starAlphabet repWord10 := by
  decide +kernel

def repConjugator10 : StarGroup :=
  ⟨repPerm10, by
    rw [repPerm10_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm11 : Equiv.Perm (Fin 24) where
  toFun := ![17, 20, 13, 11, 18, 10, 21, 4, 16, 8, 1, 0, 12, 19, 2, 3, 5, 7, 23, 9, 14, 15, 22, 6]
  invFun := ![11, 10, 14, 15, 7, 16, 23, 17, 9, 19, 5, 3, 12, 2, 20, 21, 8, 0, 4, 13, 1, 6, 22, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord11 : List (Fin 4) := [2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1]

theorem repPerm11_word : repPerm11 = evalWord starAlphabet repWord11 := by
  decide +kernel

def repConjugator11 : StarGroup :=
  ⟨repPerm11, by
    rw [repPerm11_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm12 : Equiv.Perm (Fin 24) where
  toFun := ![19, 23, 5, 15, 10, 4, 16, 8, 6, 1, 0, 17, 21, 22, 11, 9, 13, 12, 3, 2, 14, 20, 7, 18]
  invFun := ![10, 9, 19, 18, 5, 2, 8, 22, 7, 15, 4, 14, 17, 16, 20, 3, 6, 11, 23, 0, 21, 12, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord12 : List (Fin 4) := [2, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 1, 0]

theorem repPerm12_word : repPerm12 = evalWord starAlphabet repWord12 := by
  decide +kernel

def repConjugator12 : StarGroup :=
  ⟨repPerm12, by
    rw [repPerm12_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm13 : Equiv.Perm (Fin 24) where
  toFun := ![22, 14, 9, 2, 21, 4, 17, 20, 10, 12, 3, 0, 11, 8, 13, 6, 1, 15, 7, 5, 19, 16, 23, 18]
  invFun := ![11, 16, 3, 10, 5, 19, 15, 18, 13, 2, 8, 12, 9, 14, 1, 17, 21, 6, 23, 20, 7, 4, 0, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord13 : List (Fin 4) := [3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0]

theorem repPerm13_word : repPerm13 = evalWord starAlphabet repWord13 := by
  decide +kernel

def repConjugator13 : StarGroup :=
  ⟨repPerm13, by
    rw [repPerm13_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm14 : Equiv.Perm (Fin 24) where
  toFun := ![13, 5, 18, 19, 15, 8, 14, 4, 11, 20, 22, 1, 6, 0, 7, 12, 3, 2, 16, 21, 17, 10, 23, 9]
  invFun := ![13, 11, 17, 16, 7, 1, 12, 14, 5, 23, 21, 8, 15, 0, 6, 4, 18, 20, 2, 3, 9, 19, 10, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord14 : List (Fin 4) := [2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3]

theorem repPerm14_word : repPerm14 = evalWord starAlphabet repWord14 := by
  decide +kernel

def repConjugator14 : StarGroup :=
  ⟨repPerm14, by
    rw [repPerm14_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm15 : Equiv.Perm (Fin 24) where
  toFun := ![11, 7, 15, 20, 23, 4, 5, 9, 8, 19, 1, 0, 13, 2, 17, 6, 22, 16, 18, 3, 21, 10, 14, 12]
  invFun := ![11, 10, 13, 19, 5, 6, 15, 1, 8, 7, 21, 0, 23, 12, 22, 2, 17, 14, 18, 9, 3, 20, 16, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord15 : List (Fin 4) := [1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 0]

theorem repPerm15_word : repPerm15 = evalWord starAlphabet repWord15 := by
  decide +kernel

def repConjugator15 : StarGroup :=
  ⟨repPerm15, by
    rw [repPerm15_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm16 : Equiv.Perm (Fin 24) where
  toFun := ![14, 9, 11, 8, 6, 4, 12, 21, 20, 3, 0, 22, 13, 10, 2, 17, 16, 5, 15, 1, 23, 7, 18, 19]
  invFun := ![10, 19, 14, 9, 5, 17, 4, 21, 3, 1, 13, 2, 6, 12, 0, 18, 16, 15, 22, 23, 8, 7, 11, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord16 : List (Fin 4) := [3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1]

theorem repPerm16_word : repPerm16 = evalWord starAlphabet repWord16 := by
  decide +kernel

def repConjugator16 : StarGroup :=
  ⟨repPerm16, by
    rw [repPerm16_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm17 : Equiv.Perm (Fin 24) where
  toFun := ![2, 6, 14, 8, 4, 15, 9, 7, 18, 19, 5, 0, 3, 1, 20, 21, 16, 12, 17, 13, 11, 22, 10, 23]
  invFun := ![11, 13, 0, 12, 4, 10, 1, 7, 3, 6, 22, 20, 17, 19, 2, 5, 16, 18, 8, 9, 14, 15, 21, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord17 : List (Fin 4) := [2, 3, 3, 0, 3, 0, 3, 0, 3, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1]

theorem repPerm17_word : repPerm17 = evalWord starAlphabet repWord17 := by
  decide +kernel

def repConjugator17 : StarGroup :=
  ⟨repPerm17, by
    rw [repPerm17_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm18 : Equiv.Perm (Fin 24) where
  toFun := ![10, 4, 5, 21, 7, 3, 15, 17, 11, 23, 2, 0, 6, 19, 1, 14, 8, 20, 13, 12, 18, 9, 16, 22]
  invFun := ![11, 14, 10, 5, 1, 2, 12, 4, 16, 21, 0, 8, 19, 18, 15, 6, 22, 7, 20, 13, 17, 3, 23, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord18 : List (Fin 4) := [2, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0]

theorem repPerm18_word : repPerm18 = evalWord starAlphabet repWord18 := by
  decide +kernel

def repConjugator18 : StarGroup :=
  ⟨repPerm18, by
    rw [repPerm18_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm19 : Equiv.Perm (Fin 24) where
  toFun := ![14, 9, 18, 17, 7, 23, 4, 22, 13, 16, 1, 0, 21, 5, 2, 12, 6, 8, 11, 19, 10, 15, 3, 20]
  invFun := ![11, 10, 14, 22, 6, 13, 16, 4, 17, 1, 20, 18, 15, 8, 0, 21, 9, 3, 2, 19, 23, 12, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord19 : List (Fin 4) := [0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 2, 3, 2, 3]

theorem repPerm19_word : repPerm19 = evalWord starAlphabet repWord19 := by
  decide +kernel

def repConjugator19 : StarGroup :=
  ⟨repPerm19, by
    rw [repPerm19_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm20 : Equiv.Perm (Fin 24) where
  toFun := ![11, 23, 5, 8, 16, 4, 20, 15, 1, 3, 7, 22, 0, 18, 19, 9, 17, 21, 14, 10, 6, 2, 12, 13]
  invFun := ![12, 8, 21, 9, 5, 2, 20, 10, 3, 15, 19, 0, 22, 23, 18, 7, 4, 16, 13, 14, 6, 17, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord20 : List (Fin 4) := [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]

theorem repPerm20_word : repPerm20 = evalWord starAlphabet repWord20 := by
  decide +kernel

def repConjugator20 : StarGroup :=
  ⟨repPerm20, by
    rw [repPerm20_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm21 : Equiv.Perm (Fin 24) where
  toFun := ![9, 6, 14, 8, 5, 13, 4, 7, 11, 3, 0, 2, 23, 21, 17, 18, 20, 16, 22, 19, 10, 12, 1, 15]
  invFun := ![10, 22, 11, 9, 6, 4, 1, 7, 3, 0, 20, 8, 21, 5, 2, 23, 17, 14, 15, 19, 16, 13, 18, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord21 : List (Fin 4) := [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3]

theorem repPerm21_word : repPerm21 = evalWord starAlphabet repWord21 := by
  decide +kernel

def repConjugator21 : StarGroup :=
  ⟨repPerm21, by
    rw [repPerm21_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm22 : Equiv.Perm (Fin 24) where
  toFun := ![9, 4, 14, 11, 20, 13, 8, 3, 10, 21, 22, 0, 18, 15, 7, 5, 19, 1, 16, 23, 6, 12, 2, 17]
  invFun := ![11, 17, 22, 7, 1, 15, 20, 14, 6, 0, 8, 3, 21, 5, 2, 13, 18, 23, 12, 16, 4, 9, 10, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord22 : List (Fin 4) := [3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0]

theorem repPerm22_word : repPerm22 = evalWord starAlphabet repWord22 := by
  decide +kernel

def repConjugator22 : StarGroup :=
  ⟨repPerm22, by
    rw [repPerm22_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm23 : Equiv.Perm (Fin 24) where
  toFun := ![21, 7, 11, 16, 5, 12, 4, 13, 15, 17, 1, 0, 23, 6, 8, 14, 9, 2, 19, 10, 18, 20, 3, 22]
  invFun := ![11, 10, 17, 22, 6, 4, 13, 1, 14, 16, 19, 2, 5, 7, 15, 8, 3, 9, 20, 18, 21, 0, 23, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord23 : List (Fin 4) := [2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1]

theorem repPerm23_word : repPerm23 = evalWord starAlphabet repWord23 := by
  decide +kernel

def repConjugator23 : StarGroup :=
  ⟨repPerm23, by
    rw [repPerm23_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repPerm24 : Equiv.Perm (Fin 24) where
  toFun := ![16, 7, 18, 10, 5, 21, 14, 11, 4, 19, 22, 1, 13, 15, 0, 23, 2, 3, 17, 12, 6, 9, 8, 20]
  invFun := ![14, 11, 16, 17, 8, 4, 20, 1, 22, 21, 3, 7, 19, 12, 6, 13, 0, 18, 2, 9, 23, 5, 10, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repWord24 : List (Fin 4) := [2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0]

theorem repPerm24_word : repPerm24 = evalWord starAlphabet repWord24 := by
  decide +kernel

def repConjugator24 : StarGroup :=
  ⟨repPerm24, by
    rw [repPerm24_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

def repConjugator : Fin 25 → StarGroup :=
  ![repConjugator0, repConjugator1, repConjugator2, repConjugator3, repConjugator4, repConjugator5, repConjugator6, repConjugator7, repConjugator8, repConjugator9, repConjugator10, repConjugator11, repConjugator12, repConjugator13, repConjugator14, repConjugator15, repConjugator16, repConjugator17, repConjugator18, repConjugator19, repConjugator20, repConjugator21, repConjugator22, repConjugator23, repConjugator24]

def targetFlag : Fin 25 → Bool :=
  ![false, false, false, true, false, true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true]

def target (c : Fin 25) : StarGroup := if targetFlag c then starFirst else (starFirst * starSecond)^7

end Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
