module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair.Data
/-!
# Checked multiplication certificates for the five Hall--Janko relators

Each intermediate matrix is displayed explicitly and each single product is
checked by the Lean kernel over the quadratic field. Associativity and repeated
squaring then prove the exponents 2, 3, 7, 12, and 6 without exponential matrix
reduction. No Python output is used as an axiom.

Input: `../source/candidate.json`, with the ATLAS attribution and license recorded
in `../source/README.md`. Application: Aschbacher--Smith K.4.5, printed p.460.
The intermediate certificates are reproducible with `source/products.py`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
namespace MatrixCertificates
private def ab : Mat :=
  ![![(z+1),1,0,0,0,1,1,z],
    ![(z+1),0,1,z,z,z,1,z],
    ![(z+1),0,z,(z+1),(z+1),0,1,(z+1)],
    ![1,z,(z+1),0,1,z,z,z],
    ![1,z,(z+1),1,0,z,z,z],
    ![1,0,1,(z+1),(z+1),(z+1),0,1],
    ![z,1,0,1,1,1,0,(z+1)],
    ![1,(z+1),1,0,0,1,(z+1),(z+1)]]

private theorem ab_eq : aMatrix * bMatrix = ab := by decide +kernel

private def ab2 : Mat :=
  ![![0,(z+1),z,0,0,1,(z+1),0],
    ![(z+1),(z+1),z,1,1,1,(z+1),z],
    ![z,0,0,(z+1),(z+1),1,(z+1),1],
    ![z,0,0,(z+1),z,1,(z+1),(z+1)],
    ![z,0,0,z,(z+1),1,(z+1),(z+1)],
    ![z,z,0,z,z,z,(z+1),1],
    ![0,0,(z+1),0,0,0,1,z],
    ![1,0,(z+1),z,z,(z+1),1,1]]

private theorem ab2_eq : ab * ab = ab2 := by decide +kernel

private def ab4 : Mat :=
  ![![(z+1),0,(z+1),0,0,(z+1),(z+1),(z+1)],
    ![1,z,(z+1),z,z,1,(z+1),1],
    ![(z+1),(z+1),z,(z+1),(z+1),(z+1),0,1],
    ![(z+1),(z+1),(z+1),z,(z+1),(z+1),1,0],
    ![(z+1),(z+1),(z+1),(z+1),z,(z+1),1,0],
    ![(z+1),(z+1),1,1,1,0,(z+1),1],
    ![(z+1),0,z,1,1,z,1,(z+1)],
    ![1,z,z,(z+1),(z+1),0,(z+1),(z+1)]]

private theorem ab4_eq : ab2 * ab2 = ab4 := by decide +kernel

private def ab6 : Mat :=
  ![![(z+1),(z+1),1,z,z,(z+1),z,z],
    ![(z+1),0,0,z,z,1,1,1],
    ![1,1,(z+1),z,z,0,z,1],
    ![0,1,(z+1),0,1,(z+1),z,0],
    ![0,1,(z+1),1,0,(z+1),z,0],
    ![1,0,1,(z+1),(z+1),z,1,0],
    ![(z+1),1,0,z,z,0,0,1],
    ![1,z,1,1,1,(z+1),(z+1),(z+1)]]

private theorem ab6_eq : ab4 * ab2 = ab6 := by decide +kernel

private def abi : Mat :=
  ![![z,1,0,0,0,1,1,(z+1)],
    ![z,0,1,(z+1),(z+1),(z+1),1,(z+1)],
    ![z,0,(z+1),z,z,0,1,z],
    ![1,(z+1),z,0,1,(z+1),(z+1),(z+1)],
    ![1,(z+1),z,1,0,(z+1),(z+1),(z+1)],
    ![1,0,1,z,z,z,0,1],
    ![(z+1),1,0,1,1,1,0,z],
    ![1,z,1,0,0,1,z,z]]

private theorem abi_eq : aMatrix * bInvMatrix = abi := by decide +kernel

private def abia : Mat :=
  ![![z,1,0,z,z,0,1,1],
    ![z,0,1,1,1,(z+1),0,1],
    ![z,0,(z+1),0,0,0,z,0],
    ![1,(z+1),z,1,0,0,1,(z+1)],
    ![1,(z+1),z,0,1,0,1,(z+1)],
    ![1,0,1,(z+1),(z+1),z,1,0],
    ![(z+1),1,0,z,z,0,0,1],
    ![1,z,1,1,1,(z+1),(z+1),(z+1)]]

private theorem abia_eq : abi * aMatrix = abia := by decide +kernel

private def comm : Mat :=
  ![![z,1,(z+1),0,0,1,1,1],
    ![0,1,z,(z+1),(z+1),z,1,z],
    ![(z+1),z,(z+1),1,1,1,0,(z+1)],
    ![0,z,(z+1),0,1,0,0,(z+1)],
    ![0,z,(z+1),1,0,0,0,(z+1)],
    ![(z+1),z,1,0,0,1,(z+1),0],
    ![z,z,z,0,0,0,(z+1),(z+1)],
    ![1,z,(z+1),1,1,1,(z+1),(z+1)]]

private theorem comm_eq : abia * bMatrix = comm := by decide +kernel

private def comm2 : Mat :=
  ![![1,0,1,1,1,(z+1),0,z],
    ![0,0,z,0,0,0,z,1],
    ![(z+1),(z+1),0,0,0,1,0,0],
    ![1,0,0,0,1,(z+1),0,0],
    ![1,0,0,1,0,(z+1),0,0],
    ![0,0,z,0,0,0,0,1],
    ![0,(z+1),0,0,0,0,0,0],
    ![1,0,0,0,0,(z+1),0,0]]

private theorem comm2_eq : comm * comm = comm2 := by decide +kernel

private def comm4 : Mat :=
  ![![0,(z+1),0,0,0,(z+1),0,1],
    ![0,0,0,0,0,1,0,0],
    ![(z+1),0,0,(z+1),(z+1),z,1,(z+1)],
    ![0,0,0,0,1,0,0,1],
    ![0,0,0,1,0,0,0,1],
    ![0,1,0,0,0,1,0,0],
    ![0,0,1,0,0,0,1,(z+1)],
    ![1,0,0,1,1,(z+1),0,1]]

private theorem comm4_eq : comm2 * comm2 = comm4 := by decide +kernel

private def comm8 : Mat :=
  ![![1,(z+1),0,1,1,(z+1),0,1],
    ![0,1,0,0,0,1,0,0],
    ![(z+1),0,1,0,0,z,1,(z+1)],
    ![1,0,0,0,1,(z+1),0,0],
    ![1,0,0,1,0,(z+1),0,0],
    ![0,1,0,0,0,0,0,0],
    ![0,0,1,0,0,0,0,(z+1)],
    ![1,0,0,0,0,(z+1),0,0]]

private theorem comm8_eq : comm4 * comm4 = comm8 := by decide +kernel

private def prefix6 : Mat :=
  ![![1,(z+1),(z+1),0,0,(z+1),1,1],
    ![z,(z+1),1,1,1,z,1,0],
    ![1,(z+1),0,z,z,z,0,(z+1)],
    ![z,(z+1),0,(z+1),z,(z+1),0,(z+1)],
    ![z,(z+1),0,z,(z+1),(z+1),0,(z+1)],
    ![1,(z+1),1,(z+1),(z+1),z,z,1],
    ![0,z,0,0,0,(z+1),0,0],
    ![z,z,0,(z+1),(z+1),0,0,1]]

private theorem prefix6_eq : ab2 * abi = prefix6 := by decide +kernel

private def prefix8 : Mat :=
  ![![(z+1),(z+1),0,0,0,z,z,z],
    ![0,(z+1),(z+1),(z+1),(z+1),(z+1),0,0],
    ![0,(z+1),z,z,z,z,0,(z+1)],
    ![z,z,0,1,0,0,1,1],
    ![z,z,0,0,1,0,1,1],
    ![z,0,z,z,z,z,0,0],
    ![z,0,1,1,1,1,z,0],
    ![1,1,(z+1),0,0,0,(z+1),(z+1)]]

private theorem prefix8_eq : prefix6 * ab = prefix8 := by decide +kernel

private def word : Mat :=
  ![![1,z,(z+1),(z+1),(z+1),z,(z+1),z],
    ![(z+1),0,z,1,1,(z+1),0,0],
    ![(z+1),1,(z+1),0,0,z,0,z],
    ![(z+1),z,1,0,1,0,1,(z+1)],
    ![(z+1),z,1,1,0,0,1,(z+1)],
    ![z,z,(z+1),z,z,1,0,0],
    ![1,0,z,(z+1),(z+1),z,(z+1),1],
    ![0,(z+1),0,1,1,z,z,1]]

private theorem word_eq : prefix8 * abi = word := by decide +kernel

private def word2 : Mat :=
  ![![z,(z+1),z,1,1,z,z,z],
    ![(z+1),z,1,z,z,1,z,z],
    ![1,0,(z+1),z,z,z,1,z],
    ![(z+1),0,1,1,0,1,1,z],
    ![(z+1),0,1,0,1,1,1,z],
    ![(z+1),z,(z+1),(z+1),(z+1),z,1,z],
    ![0,0,z,0,0,0,(z+1),(z+1)],
    ![(z+1),0,(z+1),1,1,1,(z+1),(z+1)]]

private theorem word2_eq : word * word = word2 := by decide +kernel

private def word4 : Mat :=
  ![![(z+1),(z+1),z,z,z,z,z,z],
    ![(z+1),(z+1),1,1,1,1,z,z],
    ![1,0,z,1,1,z,1,z],
    ![1,0,(z+1),1,0,z,z,1],
    ![1,0,(z+1),0,1,z,z,1],
    ![(z+1),z,(z+1),1,1,(z+1),1,z],
    ![0,0,z,0,0,0,z,(z+1)],
    ![(z+1),0,(z+1),(z+1),(z+1),1,(z+1),z]]

private theorem word4_eq : word2 * word2 = word4 := by decide +kernel

theorem a_sq : aMatrix * aMatrix = 1 := by decide +kernel

theorem b_sq : bMatrix * bMatrix = bInvMatrix := by decide +kernel

theorem b_inv : bMatrix * bInvMatrix = 1 := by decide +kernel

theorem b_inv_left : bInvMatrix * bMatrix = 1 := by decide +kernel

private theorem ab7 : ab6 * ab = 1 := by decide +kernel

private theorem comm12 : comm8 * comm4 = 1 := by decide +kernel

private theorem word6 : word4 * word2 = 1 := by decide +kernel


theorem aMatrix_sq : aMatrix ^ 2 = 1 := by simpa only [pow_two] using a_sq

theorem bMatrix_cube : bMatrix ^ 3 = 1 := by
  rw [pow_succ, pow_two, b_sq, b_inv_left]

theorem ab_seventh : (aMatrix * bMatrix) ^ 7 = 1 := by
  rw [ab_eq]
  calc
    ab ^ 7 = ((ab * ab) * (ab * ab)) * (ab * ab) * ab := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [ab2_eq, ab4_eq, ab6_eq, ab7]

theorem commutator_twelfth : (aMatrix * bInvMatrix * aMatrix * bMatrix) ^ 12 = 1 := by
  rw [abi_eq, abia_eq, comm_eq]
  calc
    comm ^ 12 = (((comm * comm) * (comm * comm)) *
      ((comm * comm) * (comm * comm))) * ((comm * comm) * (comm * comm)) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [comm2_eq, comm4_eq, comm8_eq, comm12]

theorem longWord_sixth :
    (aMatrix * bMatrix * aMatrix * bMatrix * aMatrix * bInvMatrix *
      aMatrix * bMatrix * aMatrix * bInvMatrix) ^ 6 = 1 := by
  have hw : aMatrix * bMatrix * aMatrix * bMatrix * aMatrix * bInvMatrix *
      aMatrix * bMatrix * aMatrix * bInvMatrix = word := by
    calc
      _ = ((aMatrix * bMatrix) * (aMatrix * bMatrix)) *
        (aMatrix * bInvMatrix) * (aMatrix * bMatrix) * (aMatrix * bInvMatrix) := by
          simp only [mul_assoc]
      _ = word := by rw [ab_eq, ab2_eq, abi_eq, prefix6_eq, prefix8_eq, word_eq]
  rw [hw]
  calc
    word ^ 6 = ((word * word) * (word * word)) * (word * word) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [word2_eq, word4_eq, word6]

end MatrixCertificates
end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
