module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Basic

/-!
# Actual words in the eleven-generator marked kernel

Successively canceling leading generators in the eleven marked words gives
a triangular generating sequence. Back substitution then exhibits each of
g9, g11, g14, g16, g17, g18, g19 and g20 as a product of those words.
Each multiplication below is checked by the sound presentation collector;
no subgroup order or elementary-abelian assertion is used for membership.

The core and every slice with vanishing g13 and g15 coordinates consequently
belong to the literal `abstractKernel`. These are the two kernel fields of
`WordCalculus`, consumed by the interval catalogue's kernel branch.
Source context: Aschbacher–Smith A.3.12, pp.47–48; the eleven literal words
and their provenance in `OutsideKernelOrders/Candidates.lean` and its source README.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

private theorem multiply_mem {u v w : List (Fin 21)} (fuel : ℕ)
    (hu : wordValue u ∈ abstractKernel) (hv : wordValue v ∈ abstractKernel)
    (hc : collect fuel (u ++ v) = w) : wordValue w ∈ abstractKernel := by
  rw [← wordValue_eq_of_collect fuel _ _ hc, wordValue_append]
  exact abstractKernel.mul_mem hu hv

abbrev kernelIndices : List (Fin 21) := [9, 11, 14, 16, 17, 18, 19, 20]

theorem kernel_generators : ∀ i ∈ kernelIndices, generator i ∈ abstractKernel := by
  have hk : ∀ w ∈ kernelWords, wordValue w ∈ abstractKernel :=
    (wordSubgroup_le_iff generator kernelWords abstractKernel).mp le_rfl
  have k0 : wordValue [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k1 : wordValue [6, 11, 14, 16, 18, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k2 : wordValue [0, 5, 6, 8, 10, 12, 13, 15, 19, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k3 : wordValue [0, 5, 6, 8, 9, 10, 12, 13, 15, 18, 19] ∈ abstractKernel := hk _ (by decide +kernel)
  have k4 : wordValue [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k5 : wordValue [0, 3, 5, 6, 8, 9, 10, 11, 16, 19, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k6 : wordValue [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19] ∈ abstractKernel := hk _ (by decide +kernel)
  have k7 : wordValue [14, 17, 18, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k8 : wordValue [6, 9, 11, 14, 16, 17, 18, 19] ∈ abstractKernel := hk _ (by decide +kernel)
  have k9 : wordValue [0, 3, 5, 6, 8, 10, 16, 17, 19, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have k10 : wordValue [6, 9, 14, 17, 18, 20] ∈ abstractKernel := hk _ (by decide +kernel)
  have t0 : wordValue [3, 11, 12, 13, 14, 15, 16, 17, 19] ∈ abstractKernel :=
    multiply_mem 220 k2 k0 (by decide +kernel)
  have t1 : wordValue [3, 9, 11, 12, 13, 14, 15, 16, 17, 18] ∈ abstractKernel :=
    multiply_mem 248 k3 k0 (by decide +kernel)
  have t2 : wordValue [9, 19] ∈ abstractKernel :=
    multiply_mem 75 t1 t0 (by decide +kernel)
  have t3 : wordValue [6, 14, 16] ∈ abstractKernel :=
    multiply_mem 66 k4 t0 (by decide +kernel)
  have t4 : wordValue [11, 18, 20] ∈ abstractKernel :=
    multiply_mem 8 t3 k1 (by decide +kernel)
  have t5 : wordValue [9, 11, 14, 16, 17, 18, 19, 20] ∈ abstractKernel :=
    multiply_mem 191 k5 k0 (by decide +kernel)
  have t6 : wordValue [11, 14, 16, 17, 18, 20] ∈ abstractKernel :=
    multiply_mem 10 t5 t2 (by decide +kernel)
  have t7 : wordValue [14, 16, 17] ∈ abstractKernel :=
    multiply_mem 9 t6 t4 (by decide +kernel)
  have t8 : wordValue [3, 6, 12, 13, 14, 15, 16, 18, 19, 20] ∈ abstractKernel :=
    multiply_mem 166 k6 k0 (by decide +kernel)
  have t9 : wordValue [6, 11, 16, 17, 20] ∈ abstractKernel :=
    multiply_mem 67 t8 t0 (by decide +kernel)
  have t10 : wordValue [14, 17, 18] ∈ abstractKernel :=
    multiply_mem 17 t9 k1 (by decide +kernel)
  have t11 : wordValue [16, 18] ∈ abstractKernel :=
    multiply_mem 7 t10 t7 (by decide +kernel)
  have t12 : wordValue [16, 18, 20] ∈ abstractKernel :=
    multiply_mem 10 k7 t7 (by decide +kernel)
  have t13 : wordValue [20] ∈ abstractKernel :=
    multiply_mem 5 t12 t11 (by decide +kernel)
  have t14 : wordValue [9, 17, 19, 20] ∈ abstractKernel :=
    multiply_mem 25 k8 k1 (by decide +kernel)
  have t15 : wordValue [17, 20] ∈ abstractKernel :=
    multiply_mem 6 t14 t2 (by decide +kernel)
  have t16 : wordValue [14, 16, 18] ∈ abstractKernel :=
    multiply_mem 186 k9 k0 (by decide +kernel)
  have t17 : wordValue [17, 18] ∈ abstractKernel :=
    multiply_mem 6 t16 t7 (by decide +kernel)
  have t18 : wordValue [18, 20] ∈ abstractKernel :=
    multiply_mem 2 t17 t15 (by decide +kernel)
  have t19 : wordValue [9, 11, 16, 17] ∈ abstractKernel :=
    multiply_mem 20 k10 k1 (by decide +kernel)
  have t20 : wordValue [11, 16, 17, 19] ∈ abstractKernel :=
    multiply_mem 4 t19 t2 (by decide +kernel)
  have t21 : wordValue [16, 17, 18, 19, 20] ∈ abstractKernel :=
    multiply_mem 5 t20 t4 (by decide +kernel)
  have t22 : wordValue [17, 19, 20] ∈ abstractKernel :=
    multiply_mem 8 t21 t11 (by decide +kernel)
  have t23 : wordValue [19] ∈ abstractKernel :=
    multiply_mem 4 t22 t15 (by decide +kernel)
  have t24 : wordValue [18] ∈ abstractKernel :=
    multiply_mem 1 t18 t13 (by decide +kernel)
  have t25 : wordValue [17] ∈ abstractKernel :=
    multiply_mem 1 t15 t13 (by decide +kernel)
  have t26 : wordValue [16] ∈ abstractKernel :=
    multiply_mem 1 t11 t24 (by decide +kernel)
  have t27 : wordValue [14, 17] ∈ abstractKernel :=
    multiply_mem 2 t7 t26 (by decide +kernel)
  have t28 : wordValue [14] ∈ abstractKernel :=
    multiply_mem 1 t27 t25 (by decide +kernel)
  have t29 : wordValue [11, 20] ∈ abstractKernel :=
    multiply_mem 2 t4 t24 (by decide +kernel)
  have t30 : wordValue [11] ∈ abstractKernel :=
    multiply_mem 1 t29 t13 (by decide +kernel)
  have t31 : wordValue [9] ∈ abstractKernel :=
    multiply_mem 1 t2 t23 (by decide +kernel)
  intro i hi
  simp only [kernelIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t31
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t30
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t28
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t26
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t25
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t24
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t23
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using t13

theorem core_kernel : core ≤ abstractKernel := by
  apply (wordSubgroup_le_iff generator coreWords _).mpr
  intro w hw
  apply word_mem
  intro i hi
  exact kernel_generators i ((by decide +kernel : ∀ w ∈ coreWords, ∀ i ∈ w,
    i ∈ kernelIndices) w hw i hi)

theorem slice_kernel (n : Code) (hn : kernelCode n) : sliceValue n ∈ abstractKernel := by
  apply word_mem
  intro i hi
  exact kernel_generators i ((by decide +kernel : ∀ n : Code,
    kernelCode n → ∀ i ∈ sliceWord n, i ∈ kernelIndices) n hn i hi)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
