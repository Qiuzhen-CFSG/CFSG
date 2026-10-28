module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Relations
/-!
# A large elementary normal subgroup of the native point parabolic

Eleven literal max4 words commute and square to one. In an explicitly
certified invariant basis their binary products have distinct successive
pivots, giving order at least 2048. Ten Schreier transitions for the actual
five-point action conjugate every generator into their closure; a telescoping
subgroup argument proves normalization by the whole point stabilizer.
Conjugating by the five checked transversals treats every point parabolic.

All word identities are certified in the native subgroup by the faithful
combination of its 28-dimensional restriction and its actual quotient map.
The GAP search only supplied candidate words; it is not a proof premise.

Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0, attributed in Model.Data and
SymmetricLinear.Model; Aschbacher–Smith 12.5.3–4, printed pp.818–819.
-/

public noncomputable section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup CharacteristicTwo SylowTwoPart SylowTwoPart.KernelCardinality
namespace MathieuOverlap
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

lemma generator_square (i : Fin 11) : elementaryGenerator i ^ 2 = 1 := by
  rw [pow_two]
  fin_cases i
  · exact generator_square_0
  · exact generator_square_1
  · exact generator_square_2
  · exact generator_square_3
  · exact generator_square_4
  · exact generator_square_5
  · exact generator_square_6
  · exact generator_square_7
  · exact generator_square_8
  · exact generator_square_9
  · exact generator_square_10

lemma generator_comm (i j : Fin 11) : elementaryGenerator i * elementaryGenerator j = elementaryGenerator j * elementaryGenerator i := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact generator_comm_0_1
  · exact generator_comm_0_2
  · exact generator_comm_0_3
  · exact generator_comm_0_4
  · exact generator_comm_0_5
  · exact generator_comm_0_6
  · exact generator_comm_0_7
  · exact generator_comm_0_8
  · exact generator_comm_0_9
  · exact generator_comm_0_10
  · exact generator_comm_0_1.symm
  · rfl
  · exact generator_comm_1_2
  · exact generator_comm_1_3
  · exact generator_comm_1_4
  · exact generator_comm_1_5
  · exact generator_comm_1_6
  · exact generator_comm_1_7
  · exact generator_comm_1_8
  · exact generator_comm_1_9
  · exact generator_comm_1_10
  · exact generator_comm_0_2.symm
  · exact generator_comm_1_2.symm
  · rfl
  · exact generator_comm_2_3
  · exact generator_comm_2_4
  · exact generator_comm_2_5
  · exact generator_comm_2_6
  · exact generator_comm_2_7
  · exact generator_comm_2_8
  · exact generator_comm_2_9
  · exact generator_comm_2_10
  · exact generator_comm_0_3.symm
  · exact generator_comm_1_3.symm
  · exact generator_comm_2_3.symm
  · rfl
  · exact generator_comm_3_4
  · exact generator_comm_3_5
  · exact generator_comm_3_6
  · exact generator_comm_3_7
  · exact generator_comm_3_8
  · exact generator_comm_3_9
  · exact generator_comm_3_10
  · exact generator_comm_0_4.symm
  · exact generator_comm_1_4.symm
  · exact generator_comm_2_4.symm
  · exact generator_comm_3_4.symm
  · rfl
  · exact generator_comm_4_5
  · exact generator_comm_4_6
  · exact generator_comm_4_7
  · exact generator_comm_4_8
  · exact generator_comm_4_9
  · exact generator_comm_4_10
  · exact generator_comm_0_5.symm
  · exact generator_comm_1_5.symm
  · exact generator_comm_2_5.symm
  · exact generator_comm_3_5.symm
  · exact generator_comm_4_5.symm
  · rfl
  · exact generator_comm_5_6
  · exact generator_comm_5_7
  · exact generator_comm_5_8
  · exact generator_comm_5_9
  · exact generator_comm_5_10
  · exact generator_comm_0_6.symm
  · exact generator_comm_1_6.symm
  · exact generator_comm_2_6.symm
  · exact generator_comm_3_6.symm
  · exact generator_comm_4_6.symm
  · exact generator_comm_5_6.symm
  · rfl
  · exact generator_comm_6_7
  · exact generator_comm_6_8
  · exact generator_comm_6_9
  · exact generator_comm_6_10
  · exact generator_comm_0_7.symm
  · exact generator_comm_1_7.symm
  · exact generator_comm_2_7.symm
  · exact generator_comm_3_7.symm
  · exact generator_comm_4_7.symm
  · exact generator_comm_5_7.symm
  · exact generator_comm_6_7.symm
  · rfl
  · exact generator_comm_7_8
  · exact generator_comm_7_9
  · exact generator_comm_7_10
  · exact generator_comm_0_8.symm
  · exact generator_comm_1_8.symm
  · exact generator_comm_2_8.symm
  · exact generator_comm_3_8.symm
  · exact generator_comm_4_8.symm
  · exact generator_comm_5_8.symm
  · exact generator_comm_6_8.symm
  · exact generator_comm_7_8.symm
  · rfl
  · exact generator_comm_8_9
  · exact generator_comm_8_10
  · exact generator_comm_0_9.symm
  · exact generator_comm_1_9.symm
  · exact generator_comm_2_9.symm
  · exact generator_comm_3_9.symm
  · exact generator_comm_4_9.symm
  · exact generator_comm_5_9.symm
  · exact generator_comm_6_9.symm
  · exact generator_comm_7_9.symm
  · exact generator_comm_8_9.symm
  · rfl
  · exact generator_comm_9_10
  · exact generator_comm_0_10.symm
  · exact generator_comm_1_10.symm
  · exact generator_comm_2_10.symm
  · exact generator_comm_3_10.symm
  · exact generator_comm_4_10.symm
  · exact generator_comm_5_10.symm
  · exact generator_comm_6_10.symm
  · exact generator_comm_7_10.symm
  · exact generator_comm_8_10.symm
  · exact generator_comm_9_10.symm
  · rfl

instance elementary_isElementaryAbelian : IsElementaryAbelian 2 elementary := by
  let : IsMulCommutative (Subgroup.closure (Set.range elementaryGenerator)) := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact generator_comm i j)
  change IsElementaryAbelian 2 (Subgroup.closure (Set.range elementaryGenerator))
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨i, rfl⟩
  exact generator_square i

lemma generator_mem (i : Fin 11) : elementaryGenerator i ∈ elementary :=
  subset_closure ⟨i, rfl⟩

set_option maxRecDepth 2000 in
lemma change_inverse : decode rows328 * decode rows329 = 1 :=
  (product _ _ identityRows (by decide +kernel)).trans decode_identity
set_option maxRecDepth 2000 in
lemma inverse_change : decode rows329 * decode rows328 = 1 :=
  (product _ _ identityRows (by decide +kernel)).trans decode_identity
@[expose] def changeUnit : SmallMatrixˣ :=
  ⟨decode rows328, decode rows329, change_inverse, inverse_change⟩
@[expose] def triangularRepresentation : max4Subgroup →* SmallMatrix :=
  ((Units.coeHom SmallMatrix).comp (MulAut.conj changeUnit).toMonoidHom).comp
    representation.toHomUnits

@[expose] def triangularRows : Fin 11 → Vector ℕ 28 :=
  ![rows331, rows333, rows335, rows337, rows339, rows341, rows343, rows345, rows347, rows349, rows351]

set_option maxRecDepth 2000 in
lemma triangular_image_0 : triangularRepresentation (elementaryGenerator 0) = decode (triangularRows 0) := by
  change decode rows328 * representation g082 * decode rows329 = decode rows331
  rw [image_g082, product rows328 _ rows330 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_1 : triangularRepresentation (elementaryGenerator 1) = decode (triangularRows 1) := by
  change decode rows328 * representation g110 * decode rows329 = decode rows333
  rw [image_g110, product rows328 _ rows332 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_2 : triangularRepresentation (elementaryGenerator 2) = decode (triangularRows 2) := by
  change decode rows328 * representation g121 * decode rows329 = decode rows335
  rw [image_g121, product rows328 _ rows334 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_3 : triangularRepresentation (elementaryGenerator 3) = decode (triangularRows 3) := by
  change decode rows328 * representation g015 * decode rows329 = decode rows337
  rw [image_g015, product rows328 _ rows336 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_4 : triangularRepresentation (elementaryGenerator 4) = decode (triangularRows 4) := by
  change decode rows328 * representation g125 * decode rows329 = decode rows339
  rw [image_g125, product rows328 _ rows338 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_5 : triangularRepresentation (elementaryGenerator 5) = decode (triangularRows 5) := by
  change decode rows328 * representation g147 * decode rows329 = decode rows341
  rw [image_g147, product rows328 _ rows340 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_6 : triangularRepresentation (elementaryGenerator 6) = decode (triangularRows 6) := by
  change decode rows328 * representation g153 * decode rows329 = decode rows343
  rw [image_g153, product rows328 _ rows342 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_7 : triangularRepresentation (elementaryGenerator 7) = decode (triangularRows 7) := by
  change decode rows328 * representation g157 * decode rows329 = decode rows345
  rw [image_g157, product rows328 _ rows344 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_8 : triangularRepresentation (elementaryGenerator 8) = decode (triangularRows 8) := by
  change decode rows328 * representation g019 * decode rows329 = decode rows347
  rw [image_g019, product rows328 _ rows346 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_9 : triangularRepresentation (elementaryGenerator 9) = decode (triangularRows 9) := by
  change decode rows328 * representation g018 * decode rows329 = decode rows349
  rw [image_g018, product rows328 _ rows348 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
lemma triangular_image_10 : triangularRepresentation (elementaryGenerator 10) = decode (triangularRows 10) := by
  change decode rows328 * representation g017 * decode rows329 = decode rows351
  rw [image_g017, product rows328 _ rows350 (by decide +kernel)]
  exact product _ _ _ (by decide +kernel)

lemma triangular_image (i : Fin 11) : triangularRepresentation (elementaryGenerator i) = decode (triangularRows i) := by
  fin_cases i
  · exact triangular_image_0
  · exact triangular_image_1
  · exact triangular_image_2
  · exact triangular_image_3
  · exact triangular_image_4
  · exact triangular_image_5
  · exact triangular_image_6
  · exact triangular_image_7
  · exact triangular_image_8
  · exact triangular_image_9
  · exact triangular_image_10

@[expose] def pivotR : Fin 11 → Fin 28 := ![1, 2, 4, 5, 6, 7, 8, 10, 16, 17, 18]

@[expose] def pivotC : Fin 11 → Fin 28 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma elementary_card_lower : 2048 ≤ Nat.card elementary := by
  let gen : Fin 11 → elementary := fun i => ⟨elementaryGenerator i, generator_mem i⟩
  have hi : Function.Injective (fun b : Fin 11 → Fin 2 =>
      (List.ofFn (fun i => gen i ^ (b i).val)).prod) := by
    apply OrderedBinaryProducts.binary_injective (triangularRepresentation.comp elementary.subtype)
      11 gen pivotR pivotC
    · decide +kernel
    · intro i j hij
      change OrderedBinaryProducts.RowPrefix (pivotR i)
        (triangularRepresentation (elementaryGenerator j))
      rw [triangular_image]
      have hb : ∀ i j : Fin 11, i ≤ j → ∀ k : Fin 28,
          k < pivotR i → (triangularRows j).get k = 2 ^ k.val := by decide +kernel
      have hd : ∀ i j : Fin 11, i ≤ j →
          ((triangularRows j).get (pivotR i)).testBit (pivotR i).val = true := by decide +kernel
      have ha : ∀ i j : Fin 11, i ≤ j →
          (triangularRows j).get (pivotR i) < 2 ^ ((pivotR i).val + 1) := by decide +kernel
      exact decode_prefix _ _ (hb i j hij) (hd i j hij) (ha i j hij)
    · intro i
      change triangularRepresentation (elementaryGenerator i) (pivotR i) (pivotC i) = 1
      rw [triangular_image]
      have hv : ∀ i : Fin 11,
          ((triangularRows i).get (pivotR i)).testBit (pivotC i).val = true := by decide +kernel
      simp [decode, GeneratorCertificates.bit, hv]
    · intro i j hij
      change triangularRepresentation (elementaryGenerator j) (pivotR i) (pivotC i) = 0
      rw [triangular_image]
      have hz : ∀ i j : Fin 11, i < j →
          ((triangularRows j).get (pivotR i)).testBit (pivotC i).val = false := by decide +kernel
      simp [decode, GeneratorCertificates.bit, hz i j hij]
  have hc := Nat.card_le_card_of_injective _ hi
  norm_num only [Nat.card_fun, Nat.card_fin, Nat.reducePow] at hc
  exact hc

private lemma normalizes_of_generator_images (g : max4Subgroup)
    (h : ∀ i : Fin 11, g * elementaryGenerator i * g⁻¹ ∈ elementary) :
    g ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [elementary, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact h i
  · rw [card_map_of_injective (MulAut.conj g).injective]

lemma schreier_generator_0_0 : g001 * elementaryGenerator 0 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 0 = g302 * g001 :=
    eq_of_small_and_quotient g303 g304
      (image_g303.trans image_g304.symm) (quotient_g303.trans quotient_g304.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 0) (generator_mem 1)) (generator_mem 2)) (generator_mem 3)) (generator_mem 4)) (generator_mem 8))

lemma schreier_generator_0_1 : g001 * elementaryGenerator 1 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 1 = g308 * g001 :=
    eq_of_small_and_quotient g309 g310
      (image_g309.trans image_g310.symm) (quotient_g309.trans quotient_g310.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 1) (generator_mem 2)) (generator_mem 5)) (generator_mem 6)) (generator_mem 7)) (generator_mem 10))

lemma schreier_generator_0_2 : g001 * elementaryGenerator 2 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 2 = g121 * g001 :=
    eq_of_small_and_quotient g311 g312
      (image_g311.trans image_g312.symm) (quotient_g311.trans quotient_g312.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_0_3 : g001 * elementaryGenerator 3 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 3 = g314 * g001 :=
    eq_of_small_and_quotient g315 g316
      (image_g315.trans image_g316.symm) (quotient_g315.trans quotient_g316.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 3)) (generator_mem 8)) (generator_mem 10))

lemma schreier_generator_0_4 : g001 * elementaryGenerator 4 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 4 = g321 * g001 :=
    eq_of_small_and_quotient g322 g323
      (image_g322.trans image_g323.symm) (quotient_g322.trans quotient_g323.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 4) (generator_mem 5)) (generator_mem 6)) (generator_mem 7)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_0_5 : g001 * elementaryGenerator 5 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 5 = g327 * g001 :=
    eq_of_small_and_quotient g328 g329
      (image_g328.trans image_g329.symm) (quotient_g328.trans quotient_g329.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 3)) (generator_mem 7)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_0_6 : g001 * elementaryGenerator 6 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 6 = g331 * g001 :=
    eq_of_small_and_quotient g332 g333
      (image_g332.trans image_g333.symm) (quotient_g332.trans quotient_g333.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 6)) (generator_mem 8)) (generator_mem 10))

lemma schreier_generator_0_7 : g001 * elementaryGenerator 7 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 7 = g334 * g001 :=
    eq_of_small_and_quotient g335 g336
      (image_g335.trans image_g336.symm) (quotient_g335.trans quotient_g336.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 3) (generator_mem 5)) (generator_mem 10))

lemma schreier_generator_0_8 : g001 * elementaryGenerator 8 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 8 = g337 * g001 :=
    eq_of_small_and_quotient g338 g339
      (image_g338.trans image_g339.symm) (quotient_g338.trans quotient_g339.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 8) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_0_9 : g001 * elementaryGenerator 9 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 9 = g017 * g001 :=
    eq_of_small_and_quotient g340 g341
      (image_g340.trans image_g341.symm) (quotient_g340.trans quotient_g341.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_0_10 : g001 * elementaryGenerator 10 * g001⁻¹ ∈ elementary := by
  have he : g001 * elementaryGenerator 10 = g018 * g001 :=
    eq_of_small_and_quotient g342 g343
      (image_g342.trans image_g343.symm) (quotient_g342.trans quotient_g343.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_1_0 : g161 * elementaryGenerator 0 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 0 = g349 * g161 :=
    eq_of_small_and_quotient g350 g351
      (image_g350.trans image_g351.symm) (quotient_g350.trans quotient_g351.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 1) (generator_mem 2)) (generator_mem 3)) (generator_mem 5)) (generator_mem 6)) (generator_mem 7)) (generator_mem 8)) (generator_mem 10))

lemma schreier_generator_1_1 : g161 * elementaryGenerator 1 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 1 = g356 * g161 :=
    eq_of_small_and_quotient g357 g358
      (image_g357.trans image_g358.symm) (quotient_g357.trans quotient_g358.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 0) (generator_mem 2)) (generator_mem 3)) (generator_mem 4)) (generator_mem 6)) (generator_mem 7)) (generator_mem 8))

lemma schreier_generator_1_2 : g161 * elementaryGenerator 2 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 2 = g361 * g161 :=
    eq_of_small_and_quotient g362 g363
      (image_g362.trans image_g363.symm) (quotient_g362.trans quotient_g363.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 3) (generator_mem 4)) (generator_mem 5)) (generator_mem 7)) (generator_mem 9))

lemma schreier_generator_1_3 : g161 * elementaryGenerator 3 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 3 = g365 * g161 :=
    eq_of_small_and_quotient g366 g367
      (image_g366.trans image_g367.symm) (quotient_g366.trans quotient_g367.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 4)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_1_4 : g161 * elementaryGenerator 4 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 4 = g369 * g161 :=
    eq_of_small_and_quotient g370 g371
      (image_g370.trans image_g371.symm) (quotient_g370.trans quotient_g371.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 4) (generator_mem 5)) (generator_mem 7)) (generator_mem 10))

lemma schreier_generator_1_5 : g161 * elementaryGenerator 5 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 5 = g372 * g161 :=
    eq_of_small_and_quotient g373 g374
      (image_g373.trans image_g374.symm) (quotient_g373.trans quotient_g374.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 7) (generator_mem 8)) (generator_mem 9))

lemma schreier_generator_1_6 : g161 * elementaryGenerator 6 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 6 = g375 * g161 :=
    eq_of_small_and_quotient g376 g377
      (image_g376.trans image_g377.symm) (quotient_g376.trans quotient_g377.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 4) (generator_mem 6)) (generator_mem 7))

lemma schreier_generator_1_7 : g161 * elementaryGenerator 7 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 7 = g277 * g161 :=
    eq_of_small_and_quotient g378 g379
      (image_g378.trans image_g379.symm) (quotient_g378.trans quotient_g379.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (generator_mem 5) (generator_mem 10))

lemma schreier_generator_1_8 : g161 * elementaryGenerator 8 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 8 = g019 * g161 :=
    eq_of_small_and_quotient g380 g381
      (image_g380.trans image_g381.symm) (quotient_g380.trans quotient_g381.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_1_9 : g161 * elementaryGenerator 9 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 9 = g295 * g161 :=
    eq_of_small_and_quotient g382 g383
      (image_g382.trans image_g383.symm) (quotient_g382.trans quotient_g383.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (generator_mem 8) (generator_mem 10))

lemma schreier_generator_1_10 : g161 * elementaryGenerator 10 * g161⁻¹ ∈ elementary := by
  have he : g161 * elementaryGenerator 10 = g293 * g161 :=
    eq_of_small_and_quotient g384 g385
      (image_g384.trans image_g385.symm) (quotient_g384.trans quotient_g385.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (generator_mem 8) (generator_mem 9))

lemma schreier_generator_2_0 : g163 * elementaryGenerator 0 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 0 = g388 * g163 :=
    eq_of_small_and_quotient g389 g390
      (image_g389.trans image_g390.symm) (quotient_g389.trans quotient_g390.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 0) (generator_mem 2)) (generator_mem 3)) (generator_mem 5)) (generator_mem 6)) (generator_mem 10))

lemma schreier_generator_2_1 : g163 * elementaryGenerator 1 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 1 = g395 * g163 :=
    eq_of_small_and_quotient g396 g397
      (image_g396.trans image_g397.symm) (quotient_g396.trans quotient_g397.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 0) (generator_mem 1)) (generator_mem 4)) (generator_mem 7)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_2_2 : g163 * elementaryGenerator 2 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 2 = g399 * g163 :=
    eq_of_small_and_quotient g400 g401
      (image_g400.trans image_g401.symm) (quotient_g400.trans quotient_g401.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 4)) (generator_mem 6)) (generator_mem 7))

lemma schreier_generator_2_3 : g163 * elementaryGenerator 3 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 3 = g015 * g163 :=
    eq_of_small_and_quotient g402 g403
      (image_g402.trans image_g403.symm) (quotient_g402.trans quotient_g403.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_2_4 : g163 * elementaryGenerator 4 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 4 = g404 * g163 :=
    eq_of_small_and_quotient g405 g406
      (image_g405.trans image_g406.symm) (quotient_g405.trans quotient_g406.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 3) (generator_mem 6)) (generator_mem 7))

lemma schreier_generator_2_5 : g163 * elementaryGenerator 5 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 5 = g409 * g163 :=
    eq_of_small_and_quotient g410 g411
      (image_g410.trans image_g411.symm) (quotient_g410.trans quotient_g411.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 3)) (generator_mem 4)) (generator_mem 7)) (generator_mem 10))

lemma schreier_generator_2_6 : g163 * elementaryGenerator 6 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 6 = g415 * g163 :=
    eq_of_small_and_quotient g416 g417
      (image_g416.trans image_g417.symm) (quotient_g416.trans quotient_g417.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 3)) (generator_mem 5)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_2_7 : g163 * elementaryGenerator 7 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 7 = g421 * g163 :=
    eq_of_small_and_quotient g422 g423
      (image_g422.trans image_g423.symm) (quotient_g422.trans quotient_g423.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 4)) (generator_mem 5)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_2_8 : g163 * elementaryGenerator 8 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 8 = g019 * g163 :=
    eq_of_small_and_quotient g424 g425
      (image_g424.trans image_g425.symm) (quotient_g424.trans quotient_g425.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_2_9 : g163 * elementaryGenerator 9 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 9 = g018 * g163 :=
    eq_of_small_and_quotient g426 g427
      (image_g426.trans image_g427.symm) (quotient_g426.trans quotient_g427.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_2_10 : g163 * elementaryGenerator 10 * g163⁻¹ ∈ elementary := by
  have he : g163 * elementaryGenerator 10 = g337 * g163 :=
    eq_of_small_and_quotient g428 g429
      (image_g428.trans image_g429.symm) (quotient_g428.trans quotient_g429.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 8) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_3_0 : g166 * elementaryGenerator 0 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 0 = g082 * g166 :=
    eq_of_small_and_quotient g430 g431
      (image_g430.trans image_g431.symm) (quotient_g430.trans quotient_g431.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_3_1 : g166 * elementaryGenerator 1 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 1 = g110 * g166 :=
    eq_of_small_and_quotient g432 g433
      (image_g432.trans image_g433.symm) (quotient_g432.trans quotient_g433.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_3_2 : g166 * elementaryGenerator 2 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 2 = g121 * g166 :=
    eq_of_small_and_quotient g434 g435
      (image_g434.trans image_g435.symm) (quotient_g434.trans quotient_g435.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_3_3 : g166 * elementaryGenerator 3 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 3 = g015 * g166 :=
    eq_of_small_and_quotient g436 g437
      (image_g436.trans image_g437.symm) (quotient_g436.trans quotient_g437.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_3_4 : g166 * elementaryGenerator 4 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 4 = g125 * g166 :=
    eq_of_small_and_quotient g438 g439
      (image_g438.trans image_g439.symm) (quotient_g438.trans quotient_g439.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_3_5 : g166 * elementaryGenerator 5 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 5 = g147 * g166 :=
    eq_of_small_and_quotient g440 g441
      (image_g440.trans image_g441.symm) (quotient_g440.trans quotient_g441.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_3_6 : g166 * elementaryGenerator 6 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 6 = g153 * g166 :=
    eq_of_small_and_quotient g442 g443
      (image_g442.trans image_g443.symm) (quotient_g442.trans quotient_g443.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_3_7 : g166 * elementaryGenerator 7 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 7 = g157 * g166 :=
    eq_of_small_and_quotient g444 g445
      (image_g444.trans image_g445.symm) (quotient_g444.trans quotient_g445.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_3_8 : g166 * elementaryGenerator 8 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 8 = g019 * g166 :=
    eq_of_small_and_quotient g446 g447
      (image_g446.trans image_g447.symm) (quotient_g446.trans quotient_g447.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_3_9 : g166 * elementaryGenerator 9 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 9 = g018 * g166 :=
    eq_of_small_and_quotient g448 g449
      (image_g448.trans image_g449.symm) (quotient_g448.trans quotient_g449.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_3_10 : g166 * elementaryGenerator 10 * g166⁻¹ ∈ elementary := by
  have he : g166 * elementaryGenerator 10 = g017 * g166 :=
    eq_of_small_and_quotient g450 g451
      (image_g450.trans image_g451.symm) (quotient_g450.trans quotient_g451.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_4_0 : g169 * elementaryGenerator 0 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 0 = g082 * g169 :=
    eq_of_small_and_quotient g452 g453
      (image_g452.trans image_g453.symm) (quotient_g452.trans quotient_g453.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_4_1 : g169 * elementaryGenerator 1 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 1 = g110 * g169 :=
    eq_of_small_and_quotient g454 g455
      (image_g454.trans image_g455.symm) (quotient_g454.trans quotient_g455.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_4_2 : g169 * elementaryGenerator 2 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 2 = g121 * g169 :=
    eq_of_small_and_quotient g456 g457
      (image_g456.trans image_g457.symm) (quotient_g456.trans quotient_g457.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_4_3 : g169 * elementaryGenerator 3 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 3 = g015 * g169 :=
    eq_of_small_and_quotient g458 g459
      (image_g458.trans image_g459.symm) (quotient_g458.trans quotient_g459.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_4_4 : g169 * elementaryGenerator 4 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 4 = g125 * g169 :=
    eq_of_small_and_quotient g460 g461
      (image_g460.trans image_g461.symm) (quotient_g460.trans quotient_g461.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_4_5 : g169 * elementaryGenerator 5 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 5 = g147 * g169 :=
    eq_of_small_and_quotient g462 g463
      (image_g462.trans image_g463.symm) (quotient_g462.trans quotient_g463.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_4_6 : g169 * elementaryGenerator 6 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 6 = g153 * g169 :=
    eq_of_small_and_quotient g464 g465
      (image_g464.trans image_g465.symm) (quotient_g464.trans quotient_g465.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_4_7 : g169 * elementaryGenerator 7 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 7 = g157 * g169 :=
    eq_of_small_and_quotient g466 g467
      (image_g466.trans image_g467.symm) (quotient_g466.trans quotient_g467.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_4_8 : g169 * elementaryGenerator 8 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 8 = g019 * g169 :=
    eq_of_small_and_quotient g468 g469
      (image_g468.trans image_g469.symm) (quotient_g468.trans quotient_g469.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_4_9 : g169 * elementaryGenerator 9 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 9 = g018 * g169 :=
    eq_of_small_and_quotient g470 g471
      (image_g470.trans image_g471.symm) (quotient_g470.trans quotient_g471.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_4_10 : g169 * elementaryGenerator 10 * g169⁻¹ ∈ elementary := by
  have he : g169 * elementaryGenerator 10 = g017 * g169 :=
    eq_of_small_and_quotient g472 g473
      (image_g472.trans image_g473.symm) (quotient_g472.trans quotient_g473.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_5_0 : g170 * elementaryGenerator 0 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 0 = g082 * g170 :=
    eq_of_small_and_quotient g474 g475
      (image_g474.trans image_g475.symm) (quotient_g474.trans quotient_g475.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_5_1 : g170 * elementaryGenerator 1 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 1 = g110 * g170 :=
    eq_of_small_and_quotient g476 g477
      (image_g476.trans image_g477.symm) (quotient_g476.trans quotient_g477.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_5_2 : g170 * elementaryGenerator 2 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 2 = g121 * g170 :=
    eq_of_small_and_quotient g478 g479
      (image_g478.trans image_g479.symm) (quotient_g478.trans quotient_g479.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_5_3 : g170 * elementaryGenerator 3 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 3 = g015 * g170 :=
    eq_of_small_and_quotient g480 g481
      (image_g480.trans image_g481.symm) (quotient_g480.trans quotient_g481.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_5_4 : g170 * elementaryGenerator 4 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 4 = g125 * g170 :=
    eq_of_small_and_quotient g482 g483
      (image_g482.trans image_g483.symm) (quotient_g482.trans quotient_g483.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_5_5 : g170 * elementaryGenerator 5 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 5 = g147 * g170 :=
    eq_of_small_and_quotient g484 g485
      (image_g484.trans image_g485.symm) (quotient_g484.trans quotient_g485.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_5_6 : g170 * elementaryGenerator 6 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 6 = g153 * g170 :=
    eq_of_small_and_quotient g486 g487
      (image_g486.trans image_g487.symm) (quotient_g486.trans quotient_g487.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_5_7 : g170 * elementaryGenerator 7 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 7 = g157 * g170 :=
    eq_of_small_and_quotient g488 g489
      (image_g488.trans image_g489.symm) (quotient_g488.trans quotient_g489.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_5_8 : g170 * elementaryGenerator 8 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 8 = g019 * g170 :=
    eq_of_small_and_quotient g490 g491
      (image_g490.trans image_g491.symm) (quotient_g490.trans quotient_g491.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_5_9 : g170 * elementaryGenerator 9 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 9 = g018 * g170 :=
    eq_of_small_and_quotient g492 g493
      (image_g492.trans image_g493.symm) (quotient_g492.trans quotient_g493.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_5_10 : g170 * elementaryGenerator 10 * g170⁻¹ ∈ elementary := by
  have he : g170 * elementaryGenerator 10 = g017 * g170 :=
    eq_of_small_and_quotient g494 g495
      (image_g494.trans image_g495.symm) (quotient_g494.trans quotient_g495.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_6_0 : g171 * elementaryGenerator 0 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 0 = g082 * g171 :=
    eq_of_small_and_quotient g496 g497
      (image_g496.trans image_g497.symm) (quotient_g496.trans quotient_g497.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_6_1 : g171 * elementaryGenerator 1 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 1 = g110 * g171 :=
    eq_of_small_and_quotient g498 g499
      (image_g498.trans image_g499.symm) (quotient_g498.trans quotient_g499.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_6_2 : g171 * elementaryGenerator 2 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 2 = g121 * g171 :=
    eq_of_small_and_quotient g500 g501
      (image_g500.trans image_g501.symm) (quotient_g500.trans quotient_g501.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_6_3 : g171 * elementaryGenerator 3 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 3 = g015 * g171 :=
    eq_of_small_and_quotient g502 g503
      (image_g502.trans image_g503.symm) (quotient_g502.trans quotient_g503.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_6_4 : g171 * elementaryGenerator 4 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 4 = g125 * g171 :=
    eq_of_small_and_quotient g504 g505
      (image_g504.trans image_g505.symm) (quotient_g504.trans quotient_g505.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_6_5 : g171 * elementaryGenerator 5 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 5 = g147 * g171 :=
    eq_of_small_and_quotient g506 g507
      (image_g506.trans image_g507.symm) (quotient_g506.trans quotient_g507.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_6_6 : g171 * elementaryGenerator 6 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 6 = g153 * g171 :=
    eq_of_small_and_quotient g508 g509
      (image_g508.trans image_g509.symm) (quotient_g508.trans quotient_g509.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_6_7 : g171 * elementaryGenerator 7 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 7 = g157 * g171 :=
    eq_of_small_and_quotient g510 g511
      (image_g510.trans image_g511.symm) (quotient_g510.trans quotient_g511.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_6_8 : g171 * elementaryGenerator 8 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 8 = g019 * g171 :=
    eq_of_small_and_quotient g512 g513
      (image_g512.trans image_g513.symm) (quotient_g512.trans quotient_g513.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_6_9 : g171 * elementaryGenerator 9 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 9 = g018 * g171 :=
    eq_of_small_and_quotient g514 g515
      (image_g514.trans image_g515.symm) (quotient_g514.trans quotient_g515.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_6_10 : g171 * elementaryGenerator 10 * g171⁻¹ ∈ elementary := by
  have he : g171 * elementaryGenerator 10 = g017 * g171 :=
    eq_of_small_and_quotient g516 g517
      (image_g516.trans image_g517.symm) (quotient_g516.trans quotient_g517.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_7_0 : g173 * elementaryGenerator 0 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 0 = g082 * g173 :=
    eq_of_small_and_quotient g518 g519
      (image_g518.trans image_g519.symm) (quotient_g518.trans quotient_g519.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_7_1 : g173 * elementaryGenerator 1 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 1 = g110 * g173 :=
    eq_of_small_and_quotient g520 g521
      (image_g520.trans image_g521.symm) (quotient_g520.trans quotient_g521.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_7_2 : g173 * elementaryGenerator 2 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 2 = g121 * g173 :=
    eq_of_small_and_quotient g522 g523
      (image_g522.trans image_g523.symm) (quotient_g522.trans quotient_g523.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_7_3 : g173 * elementaryGenerator 3 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 3 = g015 * g173 :=
    eq_of_small_and_quotient g524 g525
      (image_g524.trans image_g525.symm) (quotient_g524.trans quotient_g525.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_7_4 : g173 * elementaryGenerator 4 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 4 = g125 * g173 :=
    eq_of_small_and_quotient g526 g527
      (image_g526.trans image_g527.symm) (quotient_g526.trans quotient_g527.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_7_5 : g173 * elementaryGenerator 5 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 5 = g147 * g173 :=
    eq_of_small_and_quotient g528 g529
      (image_g528.trans image_g529.symm) (quotient_g528.trans quotient_g529.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_7_6 : g173 * elementaryGenerator 6 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 6 = g153 * g173 :=
    eq_of_small_and_quotient g530 g531
      (image_g530.trans image_g531.symm) (quotient_g530.trans quotient_g531.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_7_7 : g173 * elementaryGenerator 7 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 7 = g157 * g173 :=
    eq_of_small_and_quotient g532 g533
      (image_g532.trans image_g533.symm) (quotient_g532.trans quotient_g533.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_7_8 : g173 * elementaryGenerator 8 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 8 = g019 * g173 :=
    eq_of_small_and_quotient g534 g535
      (image_g534.trans image_g535.symm) (quotient_g534.trans quotient_g535.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_7_9 : g173 * elementaryGenerator 9 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 9 = g018 * g173 :=
    eq_of_small_and_quotient g536 g537
      (image_g536.trans image_g537.symm) (quotient_g536.trans quotient_g537.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_7_10 : g173 * elementaryGenerator 10 * g173⁻¹ ∈ elementary := by
  have he : g173 * elementaryGenerator 10 = g017 * g173 :=
    eq_of_small_and_quotient g538 g539
      (image_g538.trans image_g539.symm) (quotient_g538.trans quotient_g539.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_8_0 : g175 * elementaryGenerator 0 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 0 = g543 * g175 :=
    eq_of_small_and_quotient g544 g545
      (image_g544.trans image_g545.symm) (quotient_g544.trans quotient_g545.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 0) (generator_mem 1)) (generator_mem 3)) (generator_mem 4)) (generator_mem 6)) (generator_mem 10))

lemma schreier_generator_8_1 : g175 * elementaryGenerator 1 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 1 = g548 * g175 :=
    eq_of_small_and_quotient g549 g550
      (image_g549.trans image_g550.symm) (quotient_g549.trans quotient_g550.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 1) (generator_mem 2)) (generator_mem 5)) (generator_mem 6)) (generator_mem 8)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_8_2 : g175 * elementaryGenerator 2 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 2 = g551 * g175 :=
    eq_of_small_and_quotient g552 g553
      (image_g552.trans image_g553.symm) (quotient_g552.trans quotient_g553.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 3) (generator_mem 6)) (generator_mem 10))

lemma schreier_generator_8_3 : g175 * elementaryGenerator 3 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 3 = g554 * g175 :=
    eq_of_small_and_quotient g555 g556
      (image_g555.trans image_g556.symm) (quotient_g555.trans quotient_g556.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 4)) (generator_mem 7))

lemma schreier_generator_8_4 : g175 * elementaryGenerator 4 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 4 = g557 * g175 :=
    eq_of_small_and_quotient g558 g559
      (image_g558.trans image_g559.symm) (quotient_g558.trans quotient_g559.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 6) (generator_mem 7)) (generator_mem 10))

lemma schreier_generator_8_5 : g175 * elementaryGenerator 5 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 5 = g560 * g175 :=
    eq_of_small_and_quotient g561 g562
      (image_g561.trans image_g562.symm) (quotient_g561.trans quotient_g562.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 3) (generator_mem 8)) (generator_mem 9))

lemma schreier_generator_8_6 : g175 * elementaryGenerator 6 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 6 = g565 * g175 :=
    eq_of_small_and_quotient g566 g567
      (image_g566.trans image_g567.symm) (quotient_g566.trans quotient_g567.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 2) (generator_mem 4)) (generator_mem 5)) (generator_mem 6)) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_8_7 : g175 * elementaryGenerator 7 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 7 = g568 * g175 :=
    eq_of_small_and_quotient g569 g570
      (image_g569.trans image_g570.symm) (quotient_g569.trans quotient_g570.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (elementary.mul_mem (generator_mem 4) (generator_mem 6)) (generator_mem 7)) (generator_mem 10))

lemma schreier_generator_8_8 : g175 * elementaryGenerator 8 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 8 = g017 * g175 :=
    eq_of_small_and_quotient g571 g572
      (image_g571.trans image_g572.symm) (quotient_g571.trans quotient_g572.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_generator_8_9 : g175 * elementaryGenerator 9 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 9 = g019 * g175 :=
    eq_of_small_and_quotient g573 g574
      (image_g573.trans image_g574.symm) (quotient_g573.trans quotient_g574.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_8_10 : g175 * elementaryGenerator 10 * g175⁻¹ ∈ elementary := by
  have he : g175 * elementaryGenerator 10 = g337 * g175 :=
    eq_of_small_and_quotient g575 g576
      (image_g575.trans image_g576.symm) (quotient_g575.trans quotient_g576.symm)
  rw [he, mul_inv_cancel_right]
  exact (elementary.mul_mem (elementary.mul_mem (generator_mem 8) (generator_mem 9)) (generator_mem 10))

lemma schreier_generator_9_0 : g177 * elementaryGenerator 0 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 0 = g082 * g177 :=
    eq_of_small_and_quotient g577 g578
      (image_g577.trans image_g578.symm) (quotient_g577.trans quotient_g578.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 0)

lemma schreier_generator_9_1 : g177 * elementaryGenerator 1 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 1 = g110 * g177 :=
    eq_of_small_and_quotient g579 g580
      (image_g579.trans image_g580.symm) (quotient_g579.trans quotient_g580.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 1)

lemma schreier_generator_9_2 : g177 * elementaryGenerator 2 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 2 = g121 * g177 :=
    eq_of_small_and_quotient g581 g582
      (image_g581.trans image_g582.symm) (quotient_g581.trans quotient_g582.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 2)

lemma schreier_generator_9_3 : g177 * elementaryGenerator 3 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 3 = g015 * g177 :=
    eq_of_small_and_quotient g583 g584
      (image_g583.trans image_g584.symm) (quotient_g583.trans quotient_g584.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 3)

lemma schreier_generator_9_4 : g177 * elementaryGenerator 4 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 4 = g125 * g177 :=
    eq_of_small_and_quotient g585 g586
      (image_g585.trans image_g586.symm) (quotient_g585.trans quotient_g586.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 4)

lemma schreier_generator_9_5 : g177 * elementaryGenerator 5 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 5 = g147 * g177 :=
    eq_of_small_and_quotient g587 g588
      (image_g587.trans image_g588.symm) (quotient_g587.trans quotient_g588.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 5)

lemma schreier_generator_9_6 : g177 * elementaryGenerator 6 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 6 = g153 * g177 :=
    eq_of_small_and_quotient g589 g590
      (image_g589.trans image_g590.symm) (quotient_g589.trans quotient_g590.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 6)

lemma schreier_generator_9_7 : g177 * elementaryGenerator 7 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 7 = g157 * g177 :=
    eq_of_small_and_quotient g591 g592
      (image_g591.trans image_g592.symm) (quotient_g591.trans quotient_g592.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 7)

lemma schreier_generator_9_8 : g177 * elementaryGenerator 8 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 8 = g019 * g177 :=
    eq_of_small_and_quotient g593 g594
      (image_g593.trans image_g594.symm) (quotient_g593.trans quotient_g594.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 8)

lemma schreier_generator_9_9 : g177 * elementaryGenerator 9 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 9 = g018 * g177 :=
    eq_of_small_and_quotient g595 g596
      (image_g595.trans image_g596.symm) (quotient_g595.trans quotient_g596.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 9)

lemma schreier_generator_9_10 : g177 * elementaryGenerator 10 * g177⁻¹ ∈ elementary := by
  have he : g177 * elementaryGenerator 10 = g017 * g177 :=
    eq_of_small_and_quotient g597 g598
      (image_g597.trans image_g598.symm) (quotient_g597.trans quotient_g598.symm)
  rw [he, mul_inv_cancel_right]
  exact (generator_mem 10)

lemma schreier_normalizes_0 : g001 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_0_0
  · exact schreier_generator_0_1
  · exact schreier_generator_0_2
  · exact schreier_generator_0_3
  · exact schreier_generator_0_4
  · exact schreier_generator_0_5
  · exact schreier_generator_0_6
  · exact schreier_generator_0_7
  · exact schreier_generator_0_8
  · exact schreier_generator_0_9
  · exact schreier_generator_0_10

lemma schreier_normalizes_1 : g161 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_1_0
  · exact schreier_generator_1_1
  · exact schreier_generator_1_2
  · exact schreier_generator_1_3
  · exact schreier_generator_1_4
  · exact schreier_generator_1_5
  · exact schreier_generator_1_6
  · exact schreier_generator_1_7
  · exact schreier_generator_1_8
  · exact schreier_generator_1_9
  · exact schreier_generator_1_10

lemma schreier_normalizes_2 : g163 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_2_0
  · exact schreier_generator_2_1
  · exact schreier_generator_2_2
  · exact schreier_generator_2_3
  · exact schreier_generator_2_4
  · exact schreier_generator_2_5
  · exact schreier_generator_2_6
  · exact schreier_generator_2_7
  · exact schreier_generator_2_8
  · exact schreier_generator_2_9
  · exact schreier_generator_2_10

lemma schreier_normalizes_3 : g166 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_3_0
  · exact schreier_generator_3_1
  · exact schreier_generator_3_2
  · exact schreier_generator_3_3
  · exact schreier_generator_3_4
  · exact schreier_generator_3_5
  · exact schreier_generator_3_6
  · exact schreier_generator_3_7
  · exact schreier_generator_3_8
  · exact schreier_generator_3_9
  · exact schreier_generator_3_10

lemma schreier_normalizes_4 : g169 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_4_0
  · exact schreier_generator_4_1
  · exact schreier_generator_4_2
  · exact schreier_generator_4_3
  · exact schreier_generator_4_4
  · exact schreier_generator_4_5
  · exact schreier_generator_4_6
  · exact schreier_generator_4_7
  · exact schreier_generator_4_8
  · exact schreier_generator_4_9
  · exact schreier_generator_4_10

lemma schreier_normalizes_5 : g170 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_5_0
  · exact schreier_generator_5_1
  · exact schreier_generator_5_2
  · exact schreier_generator_5_3
  · exact schreier_generator_5_4
  · exact schreier_generator_5_5
  · exact schreier_generator_5_6
  · exact schreier_generator_5_7
  · exact schreier_generator_5_8
  · exact schreier_generator_5_9
  · exact schreier_generator_5_10

lemma schreier_normalizes_6 : g171 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_6_0
  · exact schreier_generator_6_1
  · exact schreier_generator_6_2
  · exact schreier_generator_6_3
  · exact schreier_generator_6_4
  · exact schreier_generator_6_5
  · exact schreier_generator_6_6
  · exact schreier_generator_6_7
  · exact schreier_generator_6_8
  · exact schreier_generator_6_9
  · exact schreier_generator_6_10

lemma schreier_normalizes_7 : g173 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_7_0
  · exact schreier_generator_7_1
  · exact schreier_generator_7_2
  · exact schreier_generator_7_3
  · exact schreier_generator_7_4
  · exact schreier_generator_7_5
  · exact schreier_generator_7_6
  · exact schreier_generator_7_7
  · exact schreier_generator_7_8
  · exact schreier_generator_7_9
  · exact schreier_generator_7_10

lemma schreier_normalizes_8 : g175 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_8_0
  · exact schreier_generator_8_1
  · exact schreier_generator_8_2
  · exact schreier_generator_8_3
  · exact schreier_generator_8_4
  · exact schreier_generator_8_5
  · exact schreier_generator_8_6
  · exact schreier_generator_8_7
  · exact schreier_generator_8_8
  · exact schreier_generator_8_9
  · exact schreier_generator_8_10

lemma schreier_normalizes_9 : g177 ∈ (normalizer (elementary : Set max4Subgroup)) := by
  apply normalizes_of_generator_images
  intro i
  fin_cases i
  · exact schreier_generator_9_0
  · exact schreier_generator_9_1
  · exact schreier_generator_9_2
  · exact schreier_generator_9_3
  · exact schreier_generator_9_4
  · exact schreier_generator_9_5
  · exact schreier_generator_9_6
  · exact schreier_generator_9_7
  · exact schreier_generator_9_8
  · exact schreier_generator_9_9
  · exact schreier_generator_9_10

private lemma point_stabilizer_normalizes {G : Type*} [Group G] {X : Type*}
    (f : G →* Equiv.Perm X) (t : X → G) (x : X) (ht : t x = 1)
    (N : Subgroup G) (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hgen : ∀ g ∈ s, ∀ j, (t (f g j))⁻¹ * g * t j ∈ N) :
    (MulAction.stabilizer (Equiv.Perm X) x).comap f ≤ N := by
  let D : Subgroup G := {
    carrier := {g | ∀ j, (t (f g j))⁻¹ * g * t j ∈ N}
    one_mem' := by intro j; simp
    mul_mem' := by
      intro a b ha hb j
      have hh := N.mul_mem (ha (f b j)) (hb j)
      simpa only [map_mul, Equiv.Perm.mul_apply, mul_assoc, mul_inv_cancel_left] using hh
    inv_mem' := by
      intro a ha j
      have hh := N.inv_mem (ha (f a⁻¹ j))
      simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, mul_inv_rev, inv_inv,
        mul_assoc] using hh }
  have hD : D = ⊤ := top_unique (hs ▸ (Subgroup.closure_le D).mpr hgen)
  intro g hg
  have hm := (show g ∈ D from hD ▸ Subgroup.mem_top g) x
  have hf : f g x = x := hg
  simpa only [hf, ht, inv_one, one_mul, mul_one] using hm

@[expose] def transversal : Fin 5 → max4Subgroup := ![g000, g004, g002, g084, g158]

@[expose] def fiveAction : max4Subgroup →* Equiv.Perm (Fin 5) :=
  (MonoidHom.fst _ _).comp max4Projection
@[expose] def pointZero : Subgroup max4Subgroup :=
  (MulAction.stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)).comap fiveAction
lemma pointZero_normalizes : pointZero ≤ (normalizer (elementary : Set max4Subgroup)) := by
  apply point_stabilizer_normalizes fiveAction transversal 0 (by rfl)
    (normalizer (elementary : Set max4Subgroup)) {CharacteristicTwo.first, CharacteristicTwo.second}
    OrderBound.closure_generators
  intro g hg j
  rcases hg with rfl | rfl
  · change (transversal ((max4Projection Projection.first).1 j))⁻¹ *
      CharacteristicTwo.first * transversal j ∈ (normalizer (elementary : Set max4Subgroup))
    rw [max4Projection_first]
    fin_cases j
    · change (1 : max4Subgroup)⁻¹ * g001 * 1 ∈ normalizer (elementary : Set max4Subgroup)
      simpa only [inv_one, one_mul, mul_one] using schreier_normalizes_0
    · exact schreier_normalizes_1
    · exact schreier_normalizes_2
    · exact schreier_normalizes_3
    · exact schreier_normalizes_4
  · change (transversal ((max4Projection Projection.second).1 j))⁻¹ *
      CharacteristicTwo.second * transversal j ∈ (normalizer (elementary : Set max4Subgroup))
    rw [max4Projection_second]
    fin_cases j
    · change g170 * 1 ∈ normalizer (elementary : Set max4Subgroup)
      simpa only [mul_one] using schreier_normalizes_5
    · change (1 : max4Subgroup)⁻¹ * g002 * g004 ∈ normalizer (elementary : Set max4Subgroup)
      simpa only [g171, inv_one, one_mul] using schreier_normalizes_6
    · exact schreier_normalizes_7
    · exact schreier_normalizes_8
    · exact schreier_normalizes_9

lemma elementary_le_pointZero : elementary ≤ pointZero := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change (max4Projection (elementaryGenerator i)).1 0 = 0
  fin_cases i
  · change (max4Projection g082).1 0 = 0
    rw [quotient_g082]; rfl
  · change (max4Projection g110).1 0 = 0
    rw [quotient_g110]; rfl
  · change (max4Projection g121).1 0 = 0
    rw [quotient_g121]; rfl
  · change (max4Projection g015).1 0 = 0
    rw [quotient_g015]; rfl
  · change (max4Projection g125).1 0 = 0
    rw [quotient_g125]; rfl
  · change (max4Projection g147).1 0 = 0
    rw [quotient_g147]; rfl
  · change (max4Projection g153).1 0 = 0
    rw [quotient_g153]; rfl
  · change (max4Projection g157).1 0 = 0
    rw [quotient_g157]; rfl
  · change (max4Projection g019).1 0 = 0
    rw [quotient_g019]; rfl
  · change (max4Projection g018).1 0 = 0
    rw [quotient_g018]; rfl
  · change (max4Projection g017).1 0 = 0
    rw [quotient_g017]; rfl

lemma transversal_zero (j : Fin 5) : fiveAction (transversal j) 0 = j := by
  change (max4Projection (transversal j)).1 0 = j
  fin_cases j
  · change (max4Projection g000).1 0 = (0 : Fin 5)
    rw [quotient_g000]; rfl
  · change (max4Projection g004).1 0 = (1 : Fin 5)
    rw [quotient_g004]; rfl
  · change (max4Projection g002).1 0 = (2 : Fin 5)
    rw [quotient_g002]; rfl
  · change (max4Projection g084).1 0 = (3 : Fin 5)
    rw [quotient_g084]; rfl
  · change (max4Projection g158).1 0 = (4 : Fin 5)
    rw [quotient_g158]; rfl

lemma pointParabolic_as_conjugate (j : Fin 5) :
    pointParabolic j =
      (pointZero.map (MulAut.conj (transversal j)).toMonoidHom).map max4Subgroup.subtype := by
  let : MulAction max4Subgroup (Fin 5) := MulAction.compHom (Fin 5) fiveAction
  have ht : transversal j • (0 : Fin 5) = j := transversal_zero j
  have h := MulAction.stabilizer_smul_eq_stabilizer_map_conj (transversal j) (0 : Fin 5)
  rw [ht] at h
  have h0 : MulAction.stabilizer max4Subgroup (0 : Fin 5) = pointZero := rfl
  have hj : MulAction.stabilizer max4Subgroup j =
      ((MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤).comap max4Projection := by
    ext g
    simp only [mem_comap, mem_prod, mem_top, and_true, MulAction.mem_stabilizer_iff]
    rfl
  rw [h0, hj] at h
  exact congrArg (fun B : Subgroup max4Subgroup => B.map max4Subgroup.subtype) h

/-- The actual point parabolic has a normal elementary subgroup of order at
least 2048. Its eleven native word generators are retained through conjugation. -/
theorem pointParabolic_large_elementary (j : Fin 5) :
    ∃ E : Subgroup Model, E ≤ pointParabolic j ∧ IsElementaryAbelian 2 E ∧
      2048 ≤ Nat.card E ∧ pointParabolic j ≤ (normalizer (E : Set Model)) := by
  let c := (MulAut.conj (transversal j)).toMonoidHom
  let F := elementary.map c
  let E := F.map max4Subgroup.subtype
  have hF : IsElementaryAbelian 2 F := IsElementaryAbelian.map c
  let := hF
  have hEn : IsElementaryAbelian 2 E := IsElementaryAbelian.map max4Subgroup.subtype
  have hEP : E ≤ pointParabolic j := by
    rw [pointParabolic_as_conjugate]
    exact map_mono (map_mono elementary_le_pointZero)
  refine ⟨E, hEP, hEn, ?_, ?_⟩
  · change 2048 ≤ Nat.card ((elementary.map c).map max4Subgroup.subtype)
    rw [card_map_of_injective max4Subgroup.subtype_injective,
      card_map_of_injective (MulAut.conj (transversal j)).injective]
    exact elementary_card_lower
  · rw [pointParabolic_as_conjugate]
    exact (map_mono ((map_mono pointZero_normalizes).trans
      (elementary.le_normalizer_map c))).trans (F.le_normalizer_map max4Subgroup.subtype)


end MathieuOverlap
end Janko4.LocalStructure.SymmetricLinear
