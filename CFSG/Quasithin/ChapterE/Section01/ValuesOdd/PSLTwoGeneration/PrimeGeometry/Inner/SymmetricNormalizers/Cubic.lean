module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Group

/-!
# Cubic elements in four-group normalizers in PSL₂

For two distinct nonidentity elements of a four-group, choose SL₂ lifts A, B.
The lifts of all three nonidentity elements have trace zero. Consequently
A² = B² = -I and BA = -AB. The matrix X = (I + A)(I + B)/2 has determinant
one and trace one, hence X³ = -I. Direct multiplication gives XA = BX and
XB = ABX. Its projective image therefore normalizes the original four-group
and has order three, also as an element of the literal normalizer subgroup.

The construction works over every field with 2 ≠ 0; no conjugacy of
four-groups, Sylow model, or prescribed normalizer structure is assumed.
The odd-cardinality corollary supplies the cubic premise of
`SymmetricNormalizers.normalizer_equiv_symmetric_four_of_order_three`.

Source: the supporting PSL₂ calculation for Aschbacher--Smith E.1.2 and
E.1.14(6), printed pp.209--210 and 214, citing Asc82a Lemma 4.10.
This is the matrix input, not the full source-theorem assembly. The trace
lifting argument is adapted from the private calculation in
`Theory.SpecificGroups.PSL2.InvolutionFusion`, retaining its narrow matrix
imports and the existing module's private boundary.
-/

open Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
namespace SymmetricNormalizers.Cubic
variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F
local notation "PSL" => ProjectiveSpecialLinearGroup (Fin 2) F
local notation "M₂" => Matrix (Fin 2) (Fin 2) F

private theorem trace_lift (A : SL)
    (hne : QuotientGroup.mk A ≠ (1 : PSL))
    (hsq : QuotientGroup.mk A ^ 2 = (1 : PSL)) : trace A.val = 0 := by
  have hnonscalar : ¬ ∃ r : F, A.val = r • 1 := by
    rintro ⟨r, hr⟩
    apply hne
    apply (QuotientGroup.eq_one_iff A).mpr
    apply SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨r, ?_, ?_⟩
    · have hd := A.property
      rw [hr, det_smul, det_one, mul_one, Fintype.card_fin] at hd
      exact hd
    · simpa [smul_one_eq_diagonal] using hr.symm
  have hc : A ^ 2 ∈ Subgroup.center SL := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center SL)) (A ^ 2) = 1
    rw [map_pow]
    exact hsq
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have he : A.val * A.val = r • (1 : M₂) := by
    simpa only [pow_two, SpecialLinearGroup.coe_mul, scalar_apply,
      smul_one_eq_diagonal] using hr.symm
  by_contra ht
  apply hnonscalar
  refine ⟨A.val 0 0, ?_⟩
  have hb := congrArg (fun M : M₂ => M 0 1) he
  have hc := congrArg (fun M : M₂ => M 1 0) he
  have hd := congrArg (fun M : M₂ => M 0 0 - M 1 1) he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hb hc hd
  have hb0 : A.val 0 1 = 0 := (mul_eq_zero.mp (show A.val 0 1 * trace A.val = 0 by
    rw [trace_fin_two]; linear_combination hb)).resolve_right ht
  have hc0 : A.val 1 0 = 0 := (mul_eq_zero.mp (show A.val 1 0 * trace A.val = 0 by
    rw [trace_fin_two]; linear_combination hc)).resolve_right ht
  have hd0 : A.val 0 0 = A.val 1 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp (show (A.val 0 0 - A.val 1 1) * trace A.val = 0 by
      rw [trace_fin_two]; linear_combination hd)).resolve_right ht)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb0, hc0, hd0]

private theorem square_of_trace_zero (A : SL) (hA : trace A.val = 0) :
    A.val * A.val = -1 := by
  have hd := A.property
  simp only [trace_fin_two] at hA
  simp only [det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination A.val 0 0 * hA - hd
  · linear_combination A.val 0 1 * hA
  · linear_combination A.val 1 0 * hA
  · linear_combination A.val 1 1 * hA - hd

private theorem anticommute (A B : M₂)
    (hA : trace A = 0) (hB : trace B = 0) (hAB : trace (A * B) = 0) :
    B * A = -(A * B) := by
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hA hB hAB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hAB + B 0 0 * hA - A 1 1 * hB
  · linear_combination B 0 1 * hA + A 0 1 * hB
  · linear_combination B 1 0 * hA + A 1 0 * hB
  · linear_combination hAB - B 0 0 * hA + A 1 1 * hB

private theorem det_one_add (A : SL) (hA : trace A.val = 0) :
    det (1 + A.val) = 2 := by
  have hd := A.property
  simp only [trace_fin_two] at hA
  simp only [det_fin_two] at hd
  simp [det_fin_two]
  linear_combination hd + hA

private theorem cube_of_trace_one (X : SL) (hX : trace X.val = 1) :
    X ^ 3 = -1 := by
  have hd := X.property
  simp only [trace_fin_two] at hX
  simp only [det_fin_two] at hd
  have hsq : X.val * X.val = X.val - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination X.val 0 0 * hX - hd
    · linear_combination X.val 0 1 * hX
    · linear_combination X.val 1 0 * hX
    · linear_combination X.val 1 1 * hX - hd
  apply Subtype.ext
  change X.val ^ 3 = -1
  calc
    X.val ^ 3 = (X.val * X.val) * X.val := by simp [pow_succ]
    _ = -1 := by rw [hsq, sub_mul, one_mul, hsq]; abel

private theorem exists_cubic_lift (htwo : (2 : F) ≠ 0) (A B : SL)
    (hA : trace A.val = 0) (hB : trace B.val = 0)
    (hAB : trace (A.val * B.val) = 0) :
    ∃ X : SL, X ^ 3 = -1 ∧ X * A = B * X ∧ X * B = (A * B) * X := by
  let Y : M₂ := (1 + A.val) * (1 + B.val)
  have hdet : det ((2 : F)⁻¹ • Y) = 1 := by
    rw [det_smul, Fintype.card_fin, det_mul, det_one_add A hA, det_one_add B hB]
    field_simp
  let X : SL := ⟨(2 : F)⁻¹ • Y, hdet⟩
  have htrace : trace X.val = 1 := by
    change trace ((2 : F)⁻¹ • ((1 + A.val) * (1 + B.val))) = 1
    simp only [add_mul, mul_add, one_mul, mul_one, trace_smul, trace_add,
      trace_one, Fintype.card_fin, Nat.cast_ofNat, hA, hB, hAB, add_zero]
    exact inv_mul_cancel₀ htwo
  have hAA := square_of_trace_zero A hA
  have hBB := square_of_trace_zero B hB
  have hBA := anticommute A.val B.val hA hB hAB
  have hAAA : A.val * (A.val * B.val) = -B.val := by
    rw [← Matrix.mul_assoc, hAA, neg_mul, one_mul]
  have hBAB : B.val * (A.val * B.val) = A.val := by
    rw [← Matrix.mul_assoc, hBA, neg_mul, Matrix.mul_assoc, hBB,
      mul_neg, mul_one, neg_neg]
  refine ⟨X, cube_of_trace_one X htrace, ?_, ?_⟩
  · apply Subtype.ext
    change ((2 : F)⁻¹ • Y) * A.val = B.val * ((2 : F)⁻¹ • Y)
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    dsimp [Y]
    noncomm_ring [hAA, hBB, hBA, hAAA, hBAB]
  · apply Subtype.ext
    change ((2 : F)⁻¹ • Y) * B.val = (A.val * B.val) * ((2 : F)⁻¹ • Y)
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    dsimp [Y]
    noncomm_ring [hAA, hBB, hBA, hAAA, hBAB]

/-- Every four-group in PSL₂ over a field of characteristic different from two
has an actual element of order three in its normalizer. -/
public theorem exists_order_three (htwo : (2 : F) ≠ 0)
    (V : Subgroup PSL) (hV : IsKleinFour V) :
    ∃ x : Subgroup.normalizer (V : Set PSL), orderOf x = 3 := by
  classical
  let := hV
  let : Finite V := Nat.finite_of_card_ne_zero (by simp)
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset V)) (t := Finset.univ) (by simp)
  simp only [Finset.mem_singleton] at ha
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset V)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by simp))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hab : a ≠ b := Ne.symm hb.2
  have hab1 : a * b ≠ 1 := by
    intro he
    apply hab
    exact (mul_eq_one_iff_eq_inv.mp he).trans (IsKleinFour.inv_eq_self b)
  have hsq (v : V) : (v : PSL) ^ 2 = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, OneMemClass.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self v)
  let π : SL →* PSL := QuotientGroup.mk' (Subgroup.center SL)
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) (a : PSL)
  obtain ⟨B, hB⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) (b : PSL)
  change π A = (a : PSL) at hA
  change π B = (b : PSL) at hB
  have hAB : π (A * B) = ((a * b : V) : PSL) := by
    rw [map_mul, hA, hB]
    rfl
  have htrace (v : V) (hv : v ≠ 1) (C : SL) (hC : π C = (v : PSL)) :
      trace C.val = 0 := by
    apply trace_lift C
    · change π C ≠ 1
      rw [hC]
      exact fun h => hv (Subtype.ext h)
    · change π C ^ 2 = 1
      rw [hC, hsq]
  obtain ⟨X, hX3, hXA, hXB⟩ := exists_cubic_lift htwo A B
    (htrace a ha A hA) (htrace b hb.1 B hB) (htrace (a * b) hab1 (A * B) hAB)
  let x : PSL := π X
  have hx3 : x ^ 3 = 1 := by
    change π X ^ 3 = 1
    rw [← map_pow, hX3]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨-1, by simp, ?_⟩
    simp [← Matrix.diagonal_neg]
  have hxa : x * (a : PSL) * x⁻¹ = (b : PSL) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    have he := congrArg π hXA
    simpa only [map_mul, hA, hB] using he
  have hxb : x * (b : PSL) * x⁻¹ = ((a * b : V) : PSL) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    have he := congrArg π hXB
    simpa only [map_mul, hA, hB, Subgroup.coe_mul] using he
  have hxne : x ≠ 1 := by
    intro he
    apply hab
    apply Subtype.ext
    simpa [he] using hxa
  have hxn : x ∈ Subgroup.normalizer (V : Set PSL) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro y ⟨z, hz, rfl⟩
      let v : V := ⟨z, hz⟩
      have hv : v = a * b ∨ v = a ∨ v = b ∨ v = 1 := by
        have hm : v ∈ ({a * b, a, b, 1} : Finset V) := by
          rw [IsKleinFour.eq_finset_univ ha hb.1 hab]
          exact Finset.mem_univ _
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      change x * z * x⁻¹ ∈ V
      rcases hv with hv | hv | hv | hv
      · have hz' : z = (a : PSL) * (b : PSL) := congrArg Subtype.val hv
        rw [hz']
        have he : x * ((a : PSL) * (b : PSL)) * x⁻¹ =
            (x * (a : PSL) * x⁻¹) * (x * (b : PSL) * x⁻¹) := by group
        rw [he, hxa, hxb]
        exact V.mul_mem b.property (a * b).property
      · have hz' : z = (a : PSL) := congrArg Subtype.val hv
        rw [hz', hxa]
        exact b.property
      · have hz' : z = (b : PSL) := congrArg Subtype.val hv
        rw [hz', hxb]
        exact (a * b).property
      · have hz' : z = 1 := congrArg Subtype.val hv
        simp [hz']
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  refine ⟨⟨x, hxn⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime hx3 hxne

/-- The uniform odd-field witness consumed by the four-group normalizer
recognition. In particular this applies when the field has odd prime order. -/
public theorem exists_order_three_of_odd_card [Finite F] (hodd : Odd (Nat.card F))
    (V : Subgroup PSL) (hV : IsKleinFour V) :
    ∃ x : Subgroup.normalizer (V : Set PSL), orderOf x = 3 := by
  apply exists_order_three _ V hV
  let : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hchar
  have heven := FiniteField.even_card_of_char_two (F := F) hchar
  have hodd' : Odd (Fintype.card F) := by simpa [Nat.card_eq_fintype_card] using hodd
  exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_iff.mpr heven)

end SymmetricNormalizers.Cubic
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
