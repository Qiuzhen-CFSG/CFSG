module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Reduction
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.ProductA
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.ProductB
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.ProductInverse
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.Edges

/-!
# The cyclic orbit basis of the Lyons local generators

The checked matrices AQ and BQ supply the edges of the binary word tree.
Strong induction identifies Q with the word-orbit matrix, and the checked
product with its inverse gives cyclicity. Both generators commute with T,
so every word does too, giving the second clause of the certificate.

Source: the literal ATLAS program `LyG1-max4W1`; matrix and word attribution
are retained in `Atlas111Source/` and `Atlas111InvolutionSource/`.
Numerical candidate generation is in `Cyclic/source/Generate.py`.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Cyclic
open Matrix Atlas111WordCertificate Words

private theorem edge_column (j : Fin 110) :
    (fun i => qMatrix i ⟨j.val + 1, by omega⟩) =
    (if j.val % 2 = 0 then abMatrix else localBMatrix) *ᵥ
      (fun i => qMatrix i ⟨j.val / 2, by omega⟩) := by
  funext i
  change qMatrix i ⟨j.val + 1, by omega⟩ =
    ((if j.val % 2 = 0 then abMatrix else localBMatrix) * qMatrix) i
      ⟨j.val / 2, by omega⟩
  split_ifs with h
  · rw [mul_aq]
    exact congrArg (fun x : ℕ => (x : ZMod 5))
      (by simpa only [h, if_true] using edge_digits i j)
  · rw [mul_bq]
    exact congrArg (fun x : ℕ => (x : ZMod 5))
      (by simpa only [h, if_false] using edge_digits i j)

/-- The packed candidate consists exactly of the prescribed binary word columns. -/
public theorem localCyclicMatrix_eq_q : localCyclicMatrix abMatrix localBMatrix = qMatrix := by
  have hcol (n : ℕ) (hn : n < 111) :
      (fun i => qMatrix i ⟨n, hn⟩) =
      localWord abMatrix localBMatrix n *ᵥ (localSeed (n := 111) (K := ZMod 5)) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [localWord, Matrix.one_mulVec, Fin.mk_zero] using seed_column
      | succ n =>
        rw [localWord, ← Matrix.mulVec_mulVec,
          ← ih (n / 2) (by omega) (by omega)]
        exact edge_column ⟨n, by omega⟩
  ext i j
  exact (congrFun (hcol j.val j.isLt) i).symm

end Lyons.SimplicityCertificate.LocalCommutant.Cyclic

namespace Lyons.SimplicityCertificate
open Matrix LocalCommutant LocalCommutant.Cyclic Atlas111WordCertificate

private theorem word_intertwines {n : ℕ} [NeZero n] {K : Type*} [CommRing K]
    (A B T : Matrix (Fin n) (Fin n) K)
    (ha : Commute A T) (hb : Commute B T) (j : ℕ) :
    localWord A B j *ᵥ (T *ᵥ localSeed) =
      T *ᵥ (localWord A B j *ᵥ localSeed) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ localSeed)
    (localWord_commutes A B T ha.symm hb.symm j).eq.symm

/-- The exact local word orbit is a basis and intertwines the involution. -/
public theorem involutionLocal_cyclic_certificate : InvolutionLocalCyclicCertificate := by
  constructor
  · refine ⟨qiMatrix, ?_⟩
    rw [Words.image_localA, Words.image_localB, localCyclicMatrix_eq_q,
      mul_inverse, oneMatrix_eq]
  · intro j
    exact word_intertwines _ _ _ Words.image_localA_commutes
      Words.image_localB_commutes j.val

end Lyons.SimplicityCertificate
