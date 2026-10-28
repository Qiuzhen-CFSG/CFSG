module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.T1

/-!
# Centralizer true, stabilizer level 2

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

def t2g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 7, 15, 6, 16, 17, 14, 9, 12, 11, 22, 4, 20, 13, 5, 3, 18, 21, 8, 23, 10, 19]
  invFun := ![0, 1, 2, 17, 13, 16, 5, 3, 20, 9, 22, 11, 10, 15, 8, 4, 6, 7, 18, 23, 14, 19, 12, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t2g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 20, 7, 16, 5, 23, 17, 22, 9, 11, 12, 8, 15, 21, 6, 13, 18, 3, 19, 14, 10, 4]
  invFun := ![0, 1, 2, 19, 23, 6, 16, 4, 13, 10, 22, 11, 12, 17, 21, 14, 5, 8, 18, 20, 3, 15, 9, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t2g2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 11, 7, 9, 6, 4, 8, 5, 10, 3, 12, 14, 13, 15, 22, 21, 23, 20, 19, 17, 16, 18]
  invFun := ![0, 1, 2, 11, 7, 9, 6, 4, 8, 5, 10, 3, 12, 14, 13, 15, 22, 21, 23, 20, 19, 17, 16, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tGen2 : Fin 6 → Equiv.Perm (Fin 24) :=
  ![t2g0, t2g1, t2g2, (t2g0)⁻¹, (t2g1)⁻¹, (t2g2)⁻¹]

def tWords2 : Fin 6 → List (Fin 10) :=
  ![[7, 8], [6, 7, 8, 5], [9], [3, 2], [0, 3, 2, 1], [4]]

theorem tGen2_word : ∀ i, tGen2 i = evalWord tGen1 (tWords2 i) := by
  decide +kernel

theorem tLevel2_le : generated tGen2 ≤ generated tGen1 := by
  apply generated_le
  intro i
  rw [tGen2_word]
  exact word_mem _ _ (gen_mem tGen1) _

theorem tLevel2_fix : ∀ k : generated tGen2,
    (k : Equiv.Perm (Fin 24)) 2 = 2 :=
  generated_fix _ _ (by decide +kernel)

def tRepWords2 : Fin 14 → List (Fin 6) :=
  ![[], [0], [1], [2], [3], [4], [1, 0], [2, 0], [0, 1], [3, 1], [1, 3], [2, 3], [2, 1, 0], [0, 2, 0]]

def tRep2 (i : Fin 14) : Equiv.Perm (Fin 24) :=
  evalWord tGen2 (tRepWords2 i)

theorem tRep2_inj : Function.Injective (fun i => tRep2 i (3 : Fin 24)) := by
  decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
