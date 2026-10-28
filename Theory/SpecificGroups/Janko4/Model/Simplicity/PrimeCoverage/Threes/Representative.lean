module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.RepresentativeProducts

/-!
# Exact order of the designated J4 order-three representative

Seventeen kernel-checked packed products evaluate the ATLAS word `abbabababb`
and show that its twenty-second power has cube one. Entry `(0,1)` distinguishes
that power from the identity. Faithfulness of the matrix inclusion then gives
exact order three in the actual generated subgroup, using only the supplied
generator identities. No group-order or class-coverage assertion is used.

The word is sourced and attributed in `Simplicity.Words`; the matrix data are
sourced and attributed in `Model.Data`.
-/

@[expose] public section
namespace Janko4.Simplicity
open Janko4.GeneratorCertificates ThreesCertificates

/-- The ordinary matrix evaluation of the designated ATLAS word. -/
def threeWordMatrix : BinaryMatrix :=
  matrixA * matrixB * matrixB * matrixA * matrixB * matrixA * matrixB *
    matrixA * matrixB * matrixB

private lemma decode_threeWord : decodeRows prefix10Rows = threeWordMatrix := by
  rw [← product_prefix10Rows, decode_packedMul,
    ← product_prefix9Rows, decode_packedMul,
    ← product_prefix8Rows, decode_packedMul,
    ← product_prefix7Rows, decode_packedMul,
    ← product_prefix6Rows, decode_packedMul,
    ← product_prefix5Rows, decode_packedMul,
    ← product_prefix4Rows, decode_packedMul,
    ← product_prefix3Rows, decode_packedMul,
    ← product_prefix2Rows, decode_packedMul]
  rfl

private lemma decode_threeWord_two : decodeRows power2Rows = threeWordMatrix ^ 2 := by
  rw [← product_power2Rows, decode_packedMul, decode_threeWord, pow_two]

private lemma decode_threeWord_four : decodeRows power4Rows = threeWordMatrix ^ 4 := by
  rw [← product_power4Rows, decode_packedMul, decode_threeWord_two, ← pow_add]

private lemma decode_threeWord_eight : decodeRows power8Rows = threeWordMatrix ^ 8 := by
  rw [← product_power8Rows, decode_packedMul, decode_threeWord_four, ← pow_add]

private lemma decode_threeWord_sixteen : decodeRows power16Rows = threeWordMatrix ^ 16 := by
  rw [← product_power16Rows, decode_packedMul, decode_threeWord_eight, ← pow_add]

private lemma decode_threeWord_twenty : decodeRows power20Rows = threeWordMatrix ^ 20 := by
  rw [← product_power20Rows, decode_packedMul, decode_threeWord_sixteen,
    decode_threeWord_four, ← pow_add]

private lemma decode_threeWord_twenty_two :
    decodeRows power22Rows = threeWordMatrix ^ 22 := by
  rw [← product_power22Rows, decode_packedMul, decode_threeWord_twenty,
    decode_threeWord_two, ← pow_add]

private lemma decode_threeWord_forty_four :
    decodeRows power44Rows = threeWordMatrix ^ 44 := by
  rw [← product_power44Rows, decode_packedMul, decode_threeWord_twenty_two, ← pow_add]

theorem threeWordMatrix_pow_sixty_six : threeWordMatrix ^ 66 = 1 := by
  have h := congrArg decodeRows product_packedOne
  rw [decode_packedMul, decode_threeWord_forty_four, decode_threeWord_twenty_two,
    ← pow_add, decode_packedOne] at h
  exact h

theorem threeWordMatrix_pow_twenty_two_ne_one : threeWordMatrix ^ 22 ≠ 1 := by
  rw [← decode_threeWord_twenty_two]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 1) h
  exact (by decide +kernel : decodeRows power22Rows 0 1 ≠ (1 : BinaryMatrix) 0 1) e

theorem toMatrix_three_word (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (word (a hA) (b hB) "abbabababb") = threeWordMatrix := by
  simp [word, threeWordMatrix, mul_assoc]

/-- The required prime representative has exact order three in the concrete model. -/
theorem orderOf_primeRepresentative_two
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 2) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply toMatrix_injective
    change toMatrix ((word (a hA) (b hB) "abbabababb" ^ 22) ^ 3) = toMatrix 1
    rw [map_pow, map_pow, toMatrix_three_word, map_one, ← pow_mul]
    exact threeWordMatrix_pow_sixty_six
  · intro h
    apply threeWordMatrix_pow_twenty_two_ne_one
    have hm := congrArg toMatrix h
    change toMatrix (word (a hA) (b hB) "abbabababb" ^ 22) = toMatrix 1 at hm
    simpa only [map_pow, toMatrix_three_word, map_one] using hm

end Janko4.Simplicity
