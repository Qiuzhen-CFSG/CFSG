module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.Basic

/-!
# The literal kernel contains the envelope section with g13 and g15 zero

Generated from the literal presentation by `source/generate.py`.
Every displayed equation is checked by the proved bounded collector.
No discovered group order or subgroup catalogue is used.
Source: SylowNormalEights/source/README.md; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

theorem kernel_word_mem (w : List (Fin 21)) (hw : w ∈ kernelWords) :
    wordValue w ∈ abstractKernel :=
  (wordSubgroup_le_iff generator kernelWords abstractKernel).mp le_rfl w hw

/-- The eight pure generator directions in the marked kernel section. -/
theorem section_generators_mem_kernel :
    ∀ i ∈ ([9,11,14,16,17,18,19,20] : List (Fin 21)), generator i ∈ abstractKernel := by
  have h1983849 := kernel_word_mem [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] (by decide +kernel)
  have h1394752 := kernel_word_mem [6, 11, 14, 16, 18, 20] (by decide +kernel)
  have h1619297 := kernel_word_mem [0, 5, 6, 8, 10, 12, 13, 15, 19, 20] (by decide +kernel)
  have h833377 := kernel_word_mem [0, 5, 6, 8, 9, 10, 12, 13, 15, 18, 19] (by decide +kernel)
  have h2078792 := kernel_word_mem [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20] (by decide +kernel)
  have h1642345 := kernel_word_mem [0, 3, 5, 6, 8, 9, 10, 11, 16, 19, 20] (by decide +kernel)
  have h769313 := kernel_word_mem [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19] (by decide +kernel)
  have h1458176 := kernel_word_mem [14, 17, 18, 20] (by decide +kernel)
  have h1002048 := kernel_word_mem [6, 9, 11, 14, 16, 17, 18, 19] (by decide +kernel)
  have h1770857 := kernel_word_mem [0, 3, 5, 6, 8, 10, 16, 17, 19, 20] (by decide +kernel)
  have h1458752 := kernel_word_mem [6, 9, 14, 17, 18, 20] (by decide +kernel)
  have h784392 := inv_product_word_mem abstractKernel [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [0, 5, 6, 8, 10, 12, 13, 15, 19, 20] [3, 11, 12, 13, 14, 15, 16, 17, 19] 331
    h1983849 h1619297 (by decide +kernel)
  have h522760 := inv_product_word_mem abstractKernel [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [0, 5, 6, 8, 9, 10, 12, 13, 15, 18, 19] [3, 9, 11, 12, 13, 14, 15, 16, 17, 18] 350
    h1983849 h833377 (by decide +kernel)
  have h524800 := inv_product_word_mem abstractKernel [3, 11, 12, 13, 14, 15, 16, 17, 19] [3, 9, 11, 12, 13, 14, 15, 16, 17, 18] [9, 19] 172
    h784392 h522760 (by decide +kernel)
  have h81984 := inv_product_word_mem abstractKernel [3, 11, 12, 13, 14, 15, 16, 17, 19] [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20] [6, 14, 16] 176
    h784392 h2078792 (by decide +kernel)
  have h1312768 := inv_product_word_mem abstractKernel [6, 11, 14, 16, 18, 20] [6, 14, 16] [11, 18, 20] 28
    h1394752 h81984 (by decide +kernel)
  have h2050560 := inv_product_word_mem abstractKernel [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [0, 3, 5, 6, 8, 9, 10, 11, 16, 19, 20] [9, 11, 14, 16, 17, 18, 19, 20] 373
    h1983849 h1642345 (by decide +kernel)
  have h1525760 := inv_product_word_mem abstractKernel [9, 19] [9, 11, 14, 16, 17, 18, 19, 20] [11, 14, 16, 17, 18, 20] 9
    h524800 h2050560 (by decide +kernel)
  have h212992 := inv_product_word_mem abstractKernel [11, 18, 20] [11, 14, 16, 17, 18, 20] [14, 16, 17] 15
    h1312768 h1525760 (by decide +kernel)
  have h1962056 := inv_product_word_mem abstractKernel [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19] [3, 6, 12, 13, 14, 15, 16, 18, 19, 20] 322
    h1983849 h769313 (by decide +kernel)
  have h1247296 := inv_product_word_mem abstractKernel [3, 11, 12, 13, 14, 15, 16, 17, 19] [3, 6, 12, 13, 14, 15, 16, 18, 19, 20] [6, 11, 16, 17, 20] 161
    h784392 h1962056 (by decide +kernel)
  have h409600 := inv_product_word_mem abstractKernel [6, 11, 14, 16, 18, 20] [6, 11, 16, 17, 20] [14, 17, 18] 32
    h1394752 h1247296 (by decide +kernel)
  have h327680 := inv_product_word_mem abstractKernel [14, 16, 17] [14, 17, 18] [16, 18] 7
    h212992 h409600 (by decide +kernel)
  have h1376256 := inv_product_word_mem abstractKernel [14, 16, 17] [14, 17, 18, 20] [16, 18, 20] 7
    h212992 h1458176 (by decide +kernel)
  have h1048576 := inv_product_word_mem abstractKernel [16, 18] [16, 18, 20] [20] 4
    h327680 h1376256 (by decide +kernel)
  have h1704448 := inv_product_word_mem abstractKernel [6, 11, 14, 16, 18, 20] [6, 9, 11, 14, 16, 17, 18, 19] [9, 17, 19, 20] 43
    h1394752 h1002048 (by decide +kernel)
  have h1179648 := inv_product_word_mem abstractKernel [9, 19] [9, 17, 19, 20] [17, 20] 5
    h524800 h1704448 (by decide +kernel)
  have h344064 := inv_product_word_mem abstractKernel [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [0, 3, 5, 6, 8, 10, 16, 17, 19, 20] [14, 16, 18] 366
    h1983849 h1770857 (by decide +kernel)
  have h393216 := inv_product_word_mem abstractKernel [14, 16, 17] [14, 16, 18] [17, 18] 8
    h212992 h344064 (by decide +kernel)
  have h1310720 := inv_product_word_mem abstractKernel [17, 20] [17, 18] [18, 20] 4
    h1179648 h393216 (by decide +kernel)
  have h199168 := inv_product_word_mem abstractKernel [6, 11, 14, 16, 18, 20] [6, 9, 14, 17, 18, 20] [9, 11, 16, 17] 35
    h1394752 h1458752 (by decide +kernel)
  have h722944 := inv_product_word_mem abstractKernel [9, 19] [9, 11, 16, 17] [11, 16, 17, 19] 6
    h524800 h199168 (by decide +kernel)
  have h2031616 := inv_product_word_mem abstractKernel [11, 18, 20] [11, 16, 17, 19] [16, 17, 18, 19, 20] 11
    h1312768 h722944 (by decide +kernel)
  have h1703936 := inv_product_word_mem abstractKernel [16, 18] [16, 17, 18, 19, 20] [17, 19, 20] 5
    h327680 h2031616 (by decide +kernel)
  have h524288 := inv_product_word_mem abstractKernel [17, 20] [17, 19, 20] [19] 5
    h1179648 h1703936 (by decide +kernel)
  have h262144 := product_word_mem abstractKernel [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  have h131072 := product_word_mem abstractKernel [17, 20] [20] [17] 1
    h1179648 h1048576 (by decide +kernel)
  have h65536 := product_word_mem abstractKernel [16, 18] [18] [16] 1
    h327680 h262144 (by decide +kernel)
  have h147456 := product_word_mem abstractKernel [14, 16, 17] [16] [14, 17] 2
    h212992 h65536 (by decide +kernel)
  have h16384 := product_word_mem abstractKernel [14, 17] [17] [14] 1
    h147456 h131072 (by decide +kernel)
  have h1050624 := product_word_mem abstractKernel [11, 18, 20] [18] [11, 20] 2
    h1312768 h262144 (by decide +kernel)
  have h2048 := product_word_mem abstractKernel [11, 20] [20] [11] 1
    h1050624 h1048576 (by decide +kernel)
  have h512 := product_word_mem abstractKernel [9, 19] [19] [9] 1
    h524800 h524288 (by decide +kernel)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h512
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h2048
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h16384
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h131072
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem tail_le_kernel : tail ≤ abstractKernel := by
  apply (span_le_iff _ _).mpr
  intro i hi
  exact section_generators_mem_kernel i
    ((by decide +kernel : ∀ i : Fin 21, i ∈ [18,19,20] →
      i ∈ [9,11,14,16,17,18,19,20]) i hi)

theorem rep_mem_kernel (n : Fin 128)
    (h : ¬ (n.val / 4 % 2 = 1 ∨ n.val / 16 % 2 = 1)) :
    wordValue (repWord n) ∈ abstractKernel := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact section_generators_mem_kernel i
    ((by decide +kernel : ∀ n : Fin 128,
      ¬ (n.val / 4 % 2 = 1 ∨ n.val / 16 % 2 = 1) → ∀ i ∈ repWord n,
        i ∈ [9,11,14,16,17,18,19,20]) n h i hi)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
