module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.T2

/-!
# Centralizer true, stabilizer level 3

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

def t3g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 21, 5, 22, 15, 13, 6, 12, 4, 16, 19, 7, 14, 10, 18, 20, 8, 17, 11, 9, 23]
  invFun := ![0, 1, 2, 3, 11, 5, 9, 14, 19, 22, 16, 21, 10, 8, 15, 7, 12, 20, 17, 13, 18, 4, 6, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def t3g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 18, 16, 9, 4, 21, 22, 5, 19, 12, 15, 8, 17, 10, 13, 7, 20, 11, 14, 6, 23]
  invFun := ![0, 1, 2, 3, 7, 10, 22, 18, 14, 6, 16, 20, 12, 17, 21, 13, 5, 15, 4, 11, 19, 8, 9, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tGen3 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![t3g0, t3g1, (t3g0)⁻¹, (t3g1)⁻¹]

def tWords3 : Fin 4 → List (Fin 6) :=
  ![[2, 0, 2], [4, 5, 4], [5, 3, 5], [1, 2, 1]]

theorem tGen3_word : ∀ i, tGen3 i = evalWord tGen2 (tWords3 i) := by
  decide +kernel

theorem tLevel3_le : generated tGen3 ≤ generated tGen2 := by
  apply generated_le
  intro i
  rw [tGen3_word]
  exact word_mem _ _ (gen_mem tGen2) _

theorem tLevel3_fix : ∀ k : generated tGen3,
    (k : Equiv.Perm (Fin 24)) 3 = 3 :=
  generated_fix _ _ (by decide +kernel)

def tRepWords3 : Fin 12 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [1, 0], [3, 0], [0, 1], [2, 1], [1, 2], [0, 3], [0, 3, 0]]

def tRep3 (i : Fin 12) : Equiv.Perm (Fin 24) :=
  evalWord tGen3 (tRepWords3 i)

theorem tRep3_inj : Function.Injective (fun i => tRep3 i (4 : Fin 24)) := by
  decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
