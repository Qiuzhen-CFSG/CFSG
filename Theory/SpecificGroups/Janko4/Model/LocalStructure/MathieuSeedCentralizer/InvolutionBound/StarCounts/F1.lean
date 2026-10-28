module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.F0

/-!
# Centralizer false, stabilizer level 1

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

def f1g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 3, 2, 1, 6, 5, 4, 7, 9, 8, 10, 11, 12, 13, 15, 14, 23, 22, 21, 20, 19, 18, 17, 16]
  invFun := ![0, 3, 2, 1, 6, 5, 4, 7, 9, 8, 10, 11, 12, 13, 15, 14, 23, 22, 21, 20, 19, 18, 17, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f1g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 14, 2, 15, 8, 5, 9, 7, 4, 6, 10, 11, 12, 13, 1, 3, 22, 23, 19, 18, 21, 20, 16, 17]
  invFun := ![0, 14, 2, 15, 8, 5, 9, 7, 4, 6, 10, 11, 12, 13, 1, 3, 22, 23, 19, 18, 21, 20, 16, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f1g2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 9, 2, 8, 15, 5, 14, 7, 3, 1, 10, 11, 12, 13, 6, 4, 19, 21, 22, 16, 23, 17, 18, 20]
  invFun := ![0, 9, 2, 8, 15, 5, 14, 7, 3, 1, 10, 11, 12, 13, 6, 4, 19, 21, 22, 16, 23, 17, 18, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f1g3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 21, 2, 20, 6, 5, 4, 7, 9, 8, 22, 23, 16, 17, 19, 18, 11, 10, 3, 1, 15, 14, 13, 12]
  invFun := ![0, 19, 2, 18, 6, 5, 4, 7, 9, 8, 17, 16, 23, 22, 21, 20, 12, 13, 15, 14, 3, 1, 10, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f1g4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 3, 2, 1, 12, 7, 10, 5, 11, 13, 16, 23, 22, 17, 14, 15, 20, 19, 8, 9, 6, 4, 21, 18]
  invFun := ![0, 3, 2, 1, 21, 7, 20, 5, 18, 19, 6, 8, 4, 9, 14, 15, 10, 13, 23, 17, 16, 22, 12, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def fGen1 : Fin 10 → Equiv.Perm (Fin 24) :=
  ![f1g0, f1g1, f1g2, f1g3, f1g4, (f1g0)⁻¹, (f1g1)⁻¹, (f1g2)⁻¹, (f1g3)⁻¹, (f1g4)⁻¹]

def fWords1 : Fin 10 → List (Fin 14) :=
  ![[6, 9, 13, 11, 9, 4], [7, 11, 9, 4, 9], [7, 9, 13, 9, 10, 12, 8, 9], [11, 6, 8, 12, 10], [7, 13, 9, 11, 8, 9], [11, 2, 4, 6, 2, 13], [2, 11, 2, 4, 0], [2, 1, 5, 3, 2, 6, 2, 0], [3, 5, 1, 13, 4], [2, 1, 4, 2, 6, 0]]

theorem fGen1_word : ∀ i, fGen1 i = evalWord fGen0 (fWords1 i) := by
  decide +kernel

theorem fLevel1_le : generated fGen1 ≤ generated fGen0 := by
  apply generated_le
  intro i
  rw [fGen1_word]
  exact word_mem _ _ (gen_mem fGen0) _

theorem fLevel1_fix : ∀ k : generated fGen1,
    (k : Equiv.Perm (Fin 24)) 0 = 0 :=
  generated_fix _ _ (by decide +kernel)

def fRepWords1 : Fin 20 → List (Fin 10) :=
  ![[], [0], [1], [2], [3], [8], [1, 0], [2, 0], [3, 0], [8, 0], [2, 1], [4, 2], [2, 3], [4, 3], [9, 3], [2, 8], [4, 2, 0], [2, 3, 0], [4, 2, 1], [4, 4, 3]]

def fRep1 (i : Fin 20) : Equiv.Perm (Fin 24) :=
  evalWord fGen1 (fRepWords1 i)

theorem fRep1_inj : Function.Injective (fun i => fRep1 i (1 : Fin 24)) := by
  decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
