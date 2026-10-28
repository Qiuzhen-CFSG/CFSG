module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.F1

/-!
# Centralizer false, stabilizer level 2

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

def f2g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 6, 5, 4, 7, 9, 8, 11, 10, 13, 12, 14, 15, 22, 23, 20, 21, 18, 19, 16, 17]
  invFun := ![0, 1, 2, 3, 6, 5, 4, 7, 9, 8, 11, 10, 13, 12, 14, 15, 22, 23, 20, 21, 18, 19, 16, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f2g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 9, 5, 8, 7, 6, 4, 12, 13, 10, 11, 14, 15, 23, 22, 19, 18, 21, 20, 17, 16]
  invFun := ![0, 1, 2, 3, 9, 5, 8, 7, 6, 4, 12, 13, 10, 11, 14, 15, 23, 22, 19, 18, 21, 20, 17, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f2g2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 17, 5, 23, 7, 16, 22, 21, 19, 20, 18, 14, 15, 8, 4, 13, 11, 12, 10, 9, 6]
  invFun := ![0, 1, 2, 3, 17, 5, 23, 7, 16, 22, 21, 19, 20, 18, 14, 15, 8, 4, 13, 11, 12, 10, 9, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def f2g3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 21, 7, 20, 5, 18, 19, 8, 6, 9, 4, 15, 14, 13, 10, 17, 23, 22, 16, 11, 12]
  invFun := ![0, 1, 2, 3, 13, 7, 11, 5, 10, 12, 17, 22, 23, 16, 15, 14, 21, 18, 8, 9, 6, 4, 20, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def fGen2 : Fin 8 → Equiv.Perm (Fin 24) :=
  ![f2g0, f2g1, f2g2, f2g3, (f2g0)⁻¹, (f2g1)⁻¹, (f2g2)⁻¹, (f2g3)⁻¹]

def fWords2 : Fin 8 → List (Fin 10) :=
  ![[9, 8, 8, 4, 1, 0], [8, 6, 3, 5], [7, 8, 5, 7], [5, 9, 3, 3, 1], [5, 6, 9, 3, 3, 4], [0, 8, 1, 3], [2, 0, 3, 2], [6, 8, 8, 4, 0]]

theorem fGen2_word : ∀ i, fGen2 i = evalWord fGen1 (fWords2 i) := by
  decide +kernel

theorem fLevel2_le : generated fGen2 ≤ generated fGen1 := by
  apply generated_le
  intro i
  rw [fGen2_word]
  exact word_mem _ _ (gen_mem fGen1) _

theorem fLevel2_fix : ∀ k : generated fGen2,
    (k : Equiv.Perm (Fin 24)) 1 = 1 :=
  generated_fix _ _ (by decide +kernel)

def fRepWords2 : Fin 16 → List (Fin 8) :=
  ![[], [0], [1], [2], [3], [7], [1, 0], [2, 0], [3, 0], [7, 0], [2, 1], [3, 1], [7, 1], [3, 2], [7, 2], [3, 3]]

def fRep2 (i : Fin 16) : Equiv.Perm (Fin 24) :=
  evalWord fGen2 (fRepWords2 i)

theorem fRep2_inj : Function.Injective (fun i => fRep2 i (4 : Fin 24)) := by
  decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
