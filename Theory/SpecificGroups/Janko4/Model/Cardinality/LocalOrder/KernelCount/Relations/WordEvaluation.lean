module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordProducts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Reduction

/-!
# Evaluation of the ATLAS local generators

These witnesses implement the ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup` and the conjugates in `KernelCount.BinarySpan`.
Packed products are checked by Lean's kernel; `decode_packedMul` transfers
these certificates to binary matrices. No external computation is trusted.
-/

public section
namespace Janko4.Cardinality.KernelCount.Relations
open Janko4.GeneratorCertificates

lemma decoded_product {a b c : Vector ℕ 112} (h : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by
  rw [← decode_packedMul, h]

lemma eval_mul {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a b : G} {A B C : M} (ha : f a = A) (hb : f b = B) (h : A * B = C) :
    f (a * b) = C := by rw [map_mul, ha, hb, h]

lemma eval_inv {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a : G} {A B : M} (ha : f a = A) (h : A * B = 1) : f a⁻¹ = B := by
  calc
    f a⁻¹ = f a⁻¹ * (A * B) := by rw [h, mul_one]
    _ = B := by rw [← ha, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

lemma eval_conj {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a g : G} {A B C : M} (ha : f a = A) (hg : f g = B)
    (h : A * B = B * C) : f (g⁻¹ * a * g) = C := by
  calc
    f (g⁻¹ * a * g) = f g⁻¹ * (A * B) := by rw [map_mul, map_mul, ha, hg, mul_assoc]
    _ = f g⁻¹ * (B * C) := by rw [h]
    _ = C := by rw [← hg, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

lemma representation_generators :
    representation hA hB (localX hA hB) = decodeRows xRows ∧
    representation hA hB (localY hA hB) = decodeRows yRows := by
  let a := sourceA hA
  let b := sourceB hB
  have ha : toMatrix a = decodeRows aRows := rfl
  have hb : toMatrix b = decodeRows bRows := rfl
  have hab := eval_mul toMatrix ha hb (decoded_product product_ab)
  have habb := eval_mul toMatrix hab hb (decoded_product product_abb)
  have hw5 := eval_mul toMatrix hab habb (decoded_product product_w5)
  have hw6 := eval_mul toMatrix hab hw5 (decoded_product product_w6)
  have hw2 := eval_mul toMatrix hw6 hw6 (decoded_product product_w2)
  have hw4 := eval_mul toMatrix hw2 hw2 (decoded_product product_w4)
  have hw8 := eval_mul toMatrix hw4 hw4 (decoded_product product_w8)
  have habbb := eval_mul toMatrix habb hb (decoded_product product_abbb)
  have hiabbb : toMatrix (((a * b) * b) * b)⁻¹ = decodeRows iabbbRows :=
    eval_inv toMatrix habbb (by rw [decoded_product product_abbb_inverse, decode_packedOne])
  have hiab : toMatrix (a * b)⁻¹ = decodeRows iabRows :=
    eval_inv toMatrix hab (by rw [decoded_product product_ab_inverse, decode_packedOne])
  have hxl := eval_mul toMatrix hiab ha (decoded_product product_xl)
  have hx := eval_mul toMatrix hxl hab (decoded_product product_x)
  have hyl := eval_mul toMatrix hiabbb hw8 (decoded_product product_yl)
  have hy := eval_mul toMatrix hyl habbb (decoded_product product_y)
  exact ⟨hx, hy⟩

lemma representation_x : representation hA hB (localX hA hB) = decodeRows xRows :=
  (representation_generators hA hB).1
lemma representation_y : representation hA hB (localY hA hB) = decodeRows yRows :=
  (representation_generators hA hB).2

lemma representation_seed :
    representation hA hB (localKernelSeed hA hB) = decodeRows e0Rows := by
  have hxy : decodeRows xyRows = decodeRows xRows * decodeRows yRows :=
    (decoded_product product_xy).symm
  have h2 : decodeRows xy2Rows = decodeRows xyRows ^ 2 := by
    rw [← decoded_product product_xy2, pow_two]
  have h4 : decodeRows xy4Rows = decodeRows xyRows ^ 4 := by
    rw [← decoded_product product_xy4, h2, ← pow_add]
  have h8 : decodeRows xy8Rows = decodeRows xyRows ^ 8 := by
    rw [← decoded_product product_xy8, h4, ← pow_add]
  have h12 : decodeRows xy12Rows = decodeRows xyRows ^ 12 := by
    rw [← decoded_product product_xy12, h8, h4, ← pow_add]
  rw [localKernelSeed, map_pow, map_mul, representation_x, representation_y,
    ← hxy, ← decoded_product product_seed, h12, h2, ← pow_add]

end Janko4.Cardinality.KernelCount.Relations
