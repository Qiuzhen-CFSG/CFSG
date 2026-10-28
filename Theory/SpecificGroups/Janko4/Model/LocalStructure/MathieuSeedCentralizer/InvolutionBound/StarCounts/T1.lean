module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.T0

/-!
# Centralizer true, stabilizer level 1

These stabilizer transversals give only lower bounds. Every permutation,
word identity, fixed point and distinct image is checked by the Lean kernel.
GAP is used solely to discover the witnesses; its right-composition words
are reversed for Lean. See `source/generate.py` and `source/centralizers.g`.
The input generators are the certified ATLAS J4 max1 star action in `StarDefs`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions Theory.GroupTheory

def t1g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 22, 4, 3, 9, 10, 7, 21, 5, 6, 11, 16, 13, 14, 17, 12, 15, 18, 19, 23, 8, 2, 20]
  invFun := ![0, 1, 22, 4, 3, 9, 10, 7, 21, 5, 6, 11, 16, 13, 14, 17, 12, 15, 18, 19, 23, 8, 2, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t1g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 10, 21, 8, 12, 22, 7, 4, 16, 2, 11, 5, 13, 14, 20, 9, 23, 18, 19, 15, 3, 6, 17]
  invFun := ![0, 1, 10, 21, 8, 12, 22, 7, 4, 16, 2, 11, 5, 13, 14, 20, 9, 23, 18, 19, 15, 3, 6, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t1g2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 9, 17, 15, 22, 12, 7, 20, 2, 16, 11, 6, 13, 14, 4, 10, 3, 18, 19, 8, 23, 5, 21]
  invFun := ![0, 1, 9, 17, 15, 22, 12, 7, 20, 2, 16, 11, 6, 13, 14, 4, 10, 3, 18, 19, 8, 23, 5, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t1g3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 9, 7, 4, 12, 10, 3, 14, 2, 6, 11, 5, 15, 8, 13, 22, 17, 18, 23, 20, 21, 16, 19]
  invFun := ![0, 1, 9, 7, 4, 12, 10, 3, 14, 2, 6, 11, 5, 15, 8, 13, 22, 17, 18, 23, 20, 21, 16, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t1g4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 11, 7, 9, 6, 4, 8, 5, 10, 3, 12, 14, 13, 15, 22, 21, 23, 20, 19, 17, 16, 18]
  invFun := ![0, 1, 2, 11, 7, 9, 6, 4, 8, 5, 10, 3, 12, 14, 13, 15, 22, 21, 23, 20, 19, 17, 16, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tGen1 : Fin 10 → Equiv.Perm (Fin 24) :=
  ![t1g0, t1g1, t1g2, t1g3, t1g4, (t1g0)⁻¹, (t1g1)⁻¹, (t1g2)⁻¹, (t1g3)⁻¹, (t1g4)⁻¹]

def tWords1 : Fin 10 → List (Fin 14) :=
  ![[8], [9], [10], [11], [7, 7, 12], [1], [2], [3], [4], [5, 0, 0]]

theorem tGen1_word : ∀ i, tGen1 i = evalWord tGen0 (tWords1 i) := by
  decide +kernel

theorem tLevel1_le : generated tGen1 ≤ generated tGen0 := by
  apply generated_le
  intro i
  rw [tGen1_word]
  exact word_mem _ _ (gen_mem tGen0) _

theorem tLevel1_fix : ∀ k : generated tGen1,
    (k : Equiv.Perm (Fin 24)) 0 = 0 :=
  generated_fix _ _ (by decide +kernel)

def tRepWords1 : Fin 8 → List (Fin 10) :=
  ![[], [0], [1], [2], [1, 0], [2, 0], [3, 0], [2, 1, 0]]

def tRep1 (i : Fin 8) : Equiv.Perm (Fin 24) :=
  evalWord tGen1 (tRepWords1 i)

theorem tRep1_inj : Function.Injective (fun i => tRep1 i (2 : Fin 24)) := by
  decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
