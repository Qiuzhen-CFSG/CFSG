module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.KernelMasks

/-!
# The marked plane witness moves the first pure kernel eight

The eight kernel masks spanned by 1011, 1387 and 198 form an actual subgroup,
using the already proved XOR coordinates. The marked word carries mask 1011
to mask 1582, which is outside those eight masks. Its conjugation calculation
uses the certified max1 generator actions, not a matrix discovery assertion.

Consequently three literal PC-word comparisons suffice to prove that the
plane witness does not normalize `U 0`. These comparisons remain explicit.
Source: the local ATLAS words and coordinates in `KernelCount.Tables` and
`KernelOrbits.Coordinates`; candidate PC comparisons are recorded in
`SylowNormalEights/source/matrix-witness.json`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.Cardinality Janko4.Max1AmalgamRigidity
open Janko4.Simplicity.Max1Fusion.KernelOrbits
open Janko4.Cardinality.KernelCount Janko4.Cardinality.QuotientCount.Image
open Janko4.LocalStructure.SylowNormalEights.MatrixWords
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed
local notation "x" => (localX matrixA_mul_self matrixB_pow_four : Model)
local notation "y" => (localY matrixA_mul_self matrixB_pow_four : Model)

/-- Binary products of the three specified pure-row kernel masks. -/
def firstPureMask (i : Fin 8) : ℕ := ![0, 1011, 1387, 1688, 198, 821, 1453, 1630] i

private def xorIndex (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by decide)⟩

private theorem mask_xor : ∀ i j, firstPureMask (xorIndex i j) =
    Nat.xor (firstPureMask i) (firstPureMask j) := by decide +kernel

private theorem km_zero : kernelMask 0 = 1 := by
  simp only [kernelMask, maskValue_zero, map_one]

private theorem km_xor (m n : ℕ) :
    kernelMask (Nat.xor m n) = kernelMask m * kernelMask n := by
  simp only [kernelMask, maskValue_xor, map_mul]

/-- The actual subgroup consisting of the eight specified kernel words. -/
def firstPureMaskEight : Subgroup Model where
  carrier := Set.range (fun i : Fin 8 => kernelMask (firstPureMask i))
  one_mem' := by exact ⟨0, km_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨xorIndex i j, by
      change kernelMask (firstPureMask (xorIndex i j)) = _
      rw [mask_xor, km_xor]⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← km_xor]
    change kernelMask (firstPureMask i ^^^ firstPureMask i) = 1
    rw [Nat.xor_self, km_zero]

/-- Trace over the concrete eight kernel words, independently of the PC comparison. -/
noncomputable def firstPureMaskTrace (v : CosetVector) : CosetVector := by
  letI := Fintype.ofFinite firstPureMaskEight
  exact ∑ u : firstPureMaskEight, vectorRight v (u : Model)

private theorem right_x (m n : ℕ) (h : maskImage xMasks m = n) :
    x⁻¹ * kernelMask m * x = kernelMask n := by
  simpa only [kernelMask, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, h] using
    congrArg M.subtype (right_conj_mask_x matrixA_mul_self matrixB_pow_four m)

private theorem right_y (m n : ℕ) (h : maskImage yMasks m = n) :
    y⁻¹ * kernelMask m * y = kernelMask n := by
  simpa only [kernelMask, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, h] using
    congrArg M.subtype (right_conj_mask_y matrixA_mul_self matrixB_pow_four m)

private theorem right_mul {g h : Model} {m n p : ℕ}
    (hg : g⁻¹ * kernelMask m * g = kernelMask n)
    (hh : h⁻¹ * kernelMask n * h = kernelMask p) :
    (g * h)⁻¹ * kernelMask m * (g * h) = kernelMask p := by
  calc
    _ = h⁻¹ * (g⁻¹ * kernelMask m * g) * h := by group
    _ = _ := by rw [hg, hh]

private theorem transport_1011 :
    firstPureTransportWord⁻¹ * kernelMask 1011 * firstPureTransportWord =
      kernelMask 1270 := by
  have h0 := (right_x 1011 915 (by decide +kernel))
  have h1 := right_mul h0 (right_y 915 1381 (by decide +kernel))
  have h2 := right_mul h1 (right_y 1381 1801 (by decide +kernel))
  have h3 := right_mul h2 (right_x 1801 1190 (by decide +kernel))
  have h4 := right_mul h3 (right_y 1190 1740 (by decide +kernel))
  have h5 := right_mul h4 (right_x 1740 1644 (by decide +kernel))
  have h6 := right_mul h5 (right_y 1644 861 (by decide +kernel))
  have h7 := right_mul h6 (right_y 861 1270 (by decide +kernel))
  exact h7

private theorem transport_1582 :
    firstPureTransportWord⁻¹ * kernelMask 1582 * firstPureTransportWord =
      kernelMask 1849 := by
  have h0 := (right_x 1582 1773 (by decide +kernel))
  have h1 := right_mul h0 (right_y 1773 601 (by decide +kernel))
  have h2 := right_mul h1 (right_y 601 1204 (by decide +kernel))
  have h3 := right_mul h2 (right_x 1204 1816 (by decide +kernel))
  have h4 := right_mul h3 (right_y 1816 951 (by decide +kernel))
  have h5 := right_mul h4 (right_x 951 955 (by decide +kernel))
  have h6 := right_mul h5 (right_y 955 1405 (by decide +kernel))
  have h7 := right_mul h6 (right_y 1405 1849 (by decide +kernel))
  exact h7

/-- The conjugation equality giving strictness, in the actual ambient model. -/
theorem firstPureStrictWitness_conj_mask :
    firstPureStrictWitness⁻¹ * kernelMask 1011 * firstPureStrictWitness = kernelMask 1582 := by
  have hx := right_x 1270 1849 (by decide +kernel)
  calc
    _ = firstPureTransportWord *
        (x⁻¹ * (firstPureTransportWord⁻¹ * kernelMask 1011 * firstPureTransportWord) * x) *
          firstPureTransportWord⁻¹ := by unfold firstPureStrictWitness; group
    _ = firstPureTransportWord * kernelMask 1849 * firstPureTransportWord⁻¹ := by
      rw [transport_1011, hx]
    _ = kernelMask 1582 := by rw [← transport_1582]; group

/-- The moved mask is outside the actual eight-word subgroup. -/
theorem kernelMask_1582_not_mem_firstPureMaskEight : kernelMask 1582 ∉ firstPureMaskEight := by
  rintro ⟨i, hi⟩
  have he : maskValue matrixA_mul_self matrixB_pow_four (firstPureMask i) =
      maskValue matrixA_mul_self matrixB_pow_four 1582 := Subtype.ext (Subtype.ext hi)
  have hb := coordinates_injective matrixA_mul_self matrixB_pow_four he
  have hne : ∀ i : Fin 8, (fun j : Fin 11 => (firstPureMask i).testBit j.val) ≠
      (fun j : Fin 11 => (1582 : ℕ).testBit j.val) := by decide +kernel
  exact hne i hb

/-- The three PC-word comparisons place every element of the first row in
its eight-word kernel subgroup. -/
theorem firstPure_le_maskEight_of_word_equalities
    (h18 : (pcGenerator 18 : Model) = kernelMask 1011)
    (h19 : (pcGenerator 19 : Model) = kernelMask 1387)
    (h20 : (pcGenerator 20 : Model) = kernelMask 198) :
    U 0 ≤ firstPureMaskEight := by
  rw [U, map_le_iff_le_comap, F_zero, closure_le]
  intro u hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨1, h18.symm⟩
  · exact ⟨2, h19.symm⟩
  · exact ⟨4, h20.symm⟩

/-- The PC comparisons identify the actual subgroups, including every kernel word. -/
theorem firstPure_eq_maskEight_of_word_equalities
    (h18 : (pcGenerator 18 : Model) = kernelMask 1011)
    (h19 : (pcGenerator 19 : Model) = kernelMask 1387)
    (h20 : (pcGenerator 20 : Model) = kernelMask 198) :
    U 0 = firstPureMaskEight := by
  apply le_antisymm (firstPure_le_maskEight_of_word_equalities h18 h19 h20)
  have hgen (j : Fin 21) (hj : pcGenerator j ∈ F 0) : (pcGenerator j : Model) ∈ U 0 := by
    change OuterReduction.OddIndex.twoSubgroup.subtype (pcGenerator j) ∈
      (F 0).map OuterReduction.OddIndex.twoSubgroup.subtype
    exact mem_map_of_mem _ hj
  have h18m : kernelMask 1011 ∈ U 0 := by
    rw [← h18]
    exact hgen 18 (by rw [F_zero]; exact subset_closure (by simp))
  have h19m : kernelMask 1387 ∈ U 0 := by
    rw [← h19]
    exact hgen 19 (by rw [F_zero]; exact subset_closure (by simp))
  have h20m : kernelMask 198 ∈ U 0 := by
    rw [← h20]
    exact hgen 20 (by rw [F_zero]; exact subset_closure (by simp))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change kernelMask 0 ∈ U 0
    rw [km_zero]
    exact (U 0).one_mem
  · exact h18m
  · exact h19m
  · change kernelMask (Nat.xor 1011 1387) ∈ U 0
    rw [km_xor]
    exact (U 0).mul_mem h18m h19m
  · exact h20m
  · change kernelMask (Nat.xor 1011 198) ∈ U 0
    rw [km_xor]
    exact (U 0).mul_mem h18m h20m
  · change kernelMask (Nat.xor 1387 198) ∈ U 0
    rw [km_xor]
    exact (U 0).mul_mem h19m h20m
  · change kernelMask (Nat.xor (Nat.xor 1011 1387) 198) ∈ U 0
    rw [km_xor, km_xor]
    exact (U 0).mul_mem ((U 0).mul_mem h18m h19m) h20m

/-- Literal subgroup equality transports the complete trace, with no order premise. -/
theorem firstPureTrace_eq_maskTrace_of_word_equalities
    (h18 : (pcGenerator 18 : Model) = kernelMask 1011)
    (h19 : (pcGenerator 19 : Model) = kernelMask 1387)
    (h20 : (pcGenerator 20 : Model) = kernelMask 198) :
    firstPureTrace = firstPureMaskTrace := by
  have he := firstPure_eq_maskEight_of_word_equalities h18 h19 h20
  let trace (A : Subgroup Model) (v : CosetVector) : CosetVector := by
    letI := Fintype.ofFinite A
    exact ∑ u : A, vectorRight v (u : Model)
  exact congrArg trace he

/-- The explicit plane witness fails to normalize the actual first row
as soon as the three finite PC-word comparisons are certified. -/
theorem firstPureStrictWitness_not_normalizer_of_word_equalities
    (h18 : (pcGenerator 18 : Model) = kernelMask 1011)
    (h19 : (pcGenerator 19 : Model) = kernelMask 1387)
    (h20 : (pcGenerator 20 : Model) = kernelMask 198) :
    firstPureStrictWitness ∉ normalizer (U 0 : Set Model) := by
  intro hn
  have hm : kernelMask 1011 ∈ U 0 := by
    rw [← h18]
    change OuterReduction.OddIndex.twoSubgroup.subtype (pcGenerator 18) ∈
      (F 0).map OuterReduction.OddIndex.twoSubgroup.subtype
    apply mem_map_of_mem
    rw [F_zero]
    exact subset_closure (Set.mem_insert _ _)
  have hc := (mem_normalizer_iff.mp ((normalizer (U 0 : Set Model)).inv_mem hn)
    (kernelMask 1011)).mp hm
  simp only [inv_inv, firstPureStrictWitness_conj_mask] at hc
  exact kernelMask_1582_not_mem_firstPureMaskEight
    (firstPure_le_maskEight_of_word_equalities h18 h19 h20 hc)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
