module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Representatives
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.SeedCertificates.Products
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Ambient fusion of two concrete local kernel elements

Write u=(xy)^14 and v=u*(x⁻¹*u*x), where x,y are the literal ATLAS
local generators. The checked matrix identities (u*(ababb)^5)^15=1 and
(v*a)^11=1 give odd-order products of involutions. The elementary dihedral
conjugator therefore fuses u to (ababb)^5 and v to a inside `Model`.
No ambient general-linear conjugacy or class-table information is used.

The local words come from `J4G1-max1W1`, documented in `Cardinality.Subgroup`;
the matrix witnesses and their reproducible generator are in `SeedCertificates`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.Simplicity.Max1Fusion
open Cardinality Cardinality.KernelCount Cardinality.KernelCount.Relations
open Janko4.GeneratorCertificates SeedCertificates

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- The product of the first two binary basis elements of the local kernel. -/
def kernelPair : max1Subgroup hA hB :=
  localKernelSeed hA hB *
    ((localX hA hB)⁻¹ * localKernelSeed hA hB * localX hA hB)

/-- The precise ambient conjugacy alternative needed for an element. -/
def Fuses (z : Model) : Prop :=
  ∃ g : Model, a hA = g * z * g⁻¹ ∨
    word (a hA) (b hB) "ababb" ^ 5 = g * z * g⁻¹

/-- Fusion survives a further conjugation inside the actual matrix group. -/
theorem fuses_of_conjugate {z r : Model} (g : Model)
    (hr : r = g * z * g⁻¹) (hf : Fuses hA hB r) : Fuses hA hB z := by
  obtain ⟨k, hk | hk⟩ := hf
  · rw [hr] at hk
    exact ⟨k * g, Or.inl (by simpa only [mul_inv_rev, mul_assoc] using hk)⟩
  · rw [hr] at hk
    exact ⟨k * g, Or.inr (by simpa only [mul_inv_rev, mul_assoc] using hk)⟩

/-- The first local generator is already the displayed conjugate of `a`. -/
theorem localX_fuses_first :
    ∃ g : Model, a hA = g * (localX hA hB : Model) * g⁻¹ := by
  refine ⟨a hA * b hB, ?_⟩
  change a hA = (a hA * b hB) *
    ((a hA * b hB)⁻¹ * a hA * (a hA * b hB)) * (a hA * b hB)⁻¹
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
    mul_one]

private theorem decode_second_representative :
    decodeRows d5Rows = toMatrix (word (a hA) (b hB) "ababb" ^ 5) := by
  have hc : decodeRows cRows = matrixA * matrixB := by
    rw [← product_a_b, decode_packedMul]
    rfl
  have hc2 : decodeRows c2Rows = (matrixA * matrixB) ^ 2 := by
    rw [← product_c_c, decode_packedMul, hc, pow_two]
  have hd : decodeRows dRows = matrixA * matrixB * matrixA * matrixB * matrixB := by
    rw [← product_c2_b, decode_packedMul, hc2, pow_two]
    simp only [matrixB, mul_assoc]
  have hd2 : decodeRows d2Rows = (decodeRows dRows) ^ 2 := by
    rw [← product_d_d, decode_packedMul, pow_two]
  have hd4 : decodeRows d4Rows = (decodeRows dRows) ^ 4 := by
    rw [← product_d2_d2, decode_packedMul, hd2, ← pow_add]
  rw [← product_d4_d, decode_packedMul, hd4, ← pow_succ, hd]
  simp [word, mul_assoc]

private theorem decode_ut_fifteen : (decodeRows utRows) ^ 15 = (1 : BinaryMatrix) := by
  have h2 : decodeRows ut2Rows = (decodeRows utRows) ^ 2 := by
    rw [← decoded_product product_02, pow_two]
  have h4 : decodeRows ut4Rows = (decodeRows utRows) ^ 4 := by
    rw [← decoded_product product_03, h2, ← pow_add]
  have h8 : decodeRows ut8Rows = (decodeRows utRows) ^ 8 := by
    rw [← decoded_product product_04, h4, ← pow_add]
  have h12 : decodeRows ut12Rows = (decodeRows utRows) ^ 12 := by
    rw [← decoded_product product_05, h8, h4, ← pow_add]
  have h14 : decodeRows ut14Rows = (decodeRows utRows) ^ 14 := by
    rw [← decoded_product product_06, h12, h2, ← pow_add]
  have h := decoded_product product_07
  rw [h14, ← pow_succ, decode_packedOne] at h
  exact h

private theorem decode_va_eleven : (decodeRows vaRows) ^ 11 = (1 : BinaryMatrix) := by
  have h2 : decodeRows va2Rows = (decodeRows vaRows) ^ 2 := by
    rw [← decoded_product product_09, pow_two]
  have h4 : decodeRows va4Rows = (decodeRows vaRows) ^ 4 := by
    rw [← decoded_product product_10, h2, ← pow_add]
  have h8 : decodeRows va8Rows = (decodeRows vaRows) ^ 8 := by
    rw [← decoded_product product_11, h4, ← pow_add]
  have h10 : decodeRows va10Rows = (decodeRows vaRows) ^ 10 := by
    rw [← decoded_product product_12, h8, h2, ← pow_add]
  have h := decoded_product product_13
  rw [h10, ← pow_succ, decode_packedOne] at h
  exact h

/-- A checked odd exponent for the product with the second global representative. -/
theorem seed_mul_second_pow :
    ((localKernelSeed hA hB : Model) * word (a hA) (b hB) "ababb" ^ 5) ^ 15 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_mul, map_one, ← decode_second_representative]
  change (representation hA hB (localKernelSeed hA hB) * decodeRows d5Rows) ^ 15 = 1
  rw [representation_seed, decoded_product product_01]
  exact decode_ut_fifteen

/-- A checked odd exponent for the product with the first global representative. -/
theorem pair_mul_first_pow : ((kernelPair hA hB : Model) * a hA) ^ 11 = 1 := by
  have hv : toMatrix (kernelPair hA hB : Model) = decodeRows pairRows := by
    change representation hA hB (basis hA hB 0 * basis hA hB 1) = _
    rw [map_mul, representation_basis, representation_basis]
    exact decoded_product product_00
  apply toMatrix_injective
  rw [map_pow, map_mul, hv, toMatrix_a, map_one]
  change (decodeRows pairRows * decodeRows aRows) ^ 11 = 1
  rw [decoded_product product_08]
  exact decode_va_eleven

-- Group arguments only need the local carrier, not its matrix closure definition.
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed

/-- Both local kernel words square to one, as products of commuting basis words. -/
theorem kernelPair_sq : kernelPair hA hB ^ 2 = 1 := by
  change (basis hA hB 0 * basis hA hB 1) ^ 2 = 1
  rw [(basis_commute hA hB 0 1).mul_pow 2]
  simp only [pow_two, basis_square, mul_one]

/-- The first proposed kernel-orbit representative fuses to the second ATLAS word. -/
theorem seed_fuses_second :
    ∃ g : Model, word (a hA) (b hB) "ababb" ^ 5 =
      g * (localKernelSeed hA hB : Model) * g⁻¹ := by
  have hs : (localKernelSeed hA hB : Model) ^ 2 = 1 := by
    have h := congrArg (fun z : max1Subgroup hA hB => (z : Model))
      (basis_square hA hB 0)
    change (localKernelSeed hA hB : Model) * (localKernelSeed hA hB : Model) = 1 at h
    simpa only [pow_two] using h
  have ht : (word (a hA) (b hB) "ababb" ^ 5) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (primeRepresentative (a hA) (b hB) 1)
    rw [involutionRepresentative_one_orderOf hA hB] at h
    exact h
  have ho : Odd (orderOf ((localKernelSeed hA hB : Model) *
      word (a hA) (b hB) "ababb" ^ 5)) :=
    (by decide : Odd 15).of_dvd_nat (orderOf_dvd_of_pow_eq_one (seed_mul_second_pow hA hB))
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_involutions_odd_product _ _ hs ht ho)
  exact ⟨g, hg.symm⟩

/-- The second proposed kernel-orbit representative fuses to the first ATLAS word. -/
theorem pair_fuses_first :
    ∃ g : Model, a hA = g * (kernelPair hA hB : Model) * g⁻¹ := by
  have hv : (kernelPair hA hB : Model) ^ 2 = 1 := by
    have h := congrArg (max1Subgroup hA hB).subtype (kernelPair_sq hA hB)
    simpa only [map_pow, map_one, Subgroup.subtype_apply] using h
  have ha : a hA ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (primeRepresentative (a hA) (b hB) 0)
    rw [involutionRepresentative_zero_orderOf hA hB] at h
    exact h
  have ho : Odd (orderOf ((kernelPair hA hB : Model) * a hA)) :=
    (by decide : Odd 11).of_dvd_nat (orderOf_dvd_of_pow_eq_one (pair_mul_first_pow hA hB))
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_involutions_odd_product _ _ hv ha ho)
  exact ⟨g, hg.symm⟩

end Janko4.Simplicity.Max1Fusion
