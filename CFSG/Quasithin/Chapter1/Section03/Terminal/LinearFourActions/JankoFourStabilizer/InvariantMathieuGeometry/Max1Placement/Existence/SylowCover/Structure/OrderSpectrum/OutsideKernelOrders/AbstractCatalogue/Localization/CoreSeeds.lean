module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.Basic

/-!
# Recovering the whole core from its g16 coset

Generated from the literal presentation by `source/generate.py`.
Every displayed equation is checked by the proved bounded collector.
No discovered group order or subgroup catalogue is used.
Source: SylowNormalEights/source/README.md; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

theorem core_seed_0 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 0) ∈ N) : core ≤ N := by
  have h65536 : wordValue [16] ∈ N := hx
  have h1114112 := conjugate_word_mem N hn [16] [16, 20] 0 4
    h65536 (by decide +kernel)
  have h1048576 := product_word_mem N [16, 20] [16] [20] 2
    h1114112 h65536 (by decide +kernel)
  have h1376256 := conjugate_word_mem N hn [16] [16, 18, 20] 1 2
    h65536 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 18, 20] [16] [18, 20] 3
    h1376256 h65536 (by decide +kernel)
  have h589824 := conjugate_word_mem N hn [16] [16, 19] 4 2
    h65536 (by decide +kernel)
  have h524288 := product_word_mem N [16, 19] [16] [19] 2
    h589824 h65536 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_1 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 1) ∈ N) : core ≤ N := by
  have h327680 : wordValue [16, 18] ∈ N := hx
  have h1376256 := conjugate_word_mem N hn [16, 18] [16, 18, 20] 0 6
    h327680 (by decide +kernel)
  have h1048576 := product_word_mem N [16, 18, 20] [16, 18] [20] 5
    h1376256 h327680 (by decide +kernel)
  have h1114112 := conjugate_word_mem N hn [16, 18] [16, 20] 1 5
    h327680 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 20] [16, 18] [18, 20] 3
    h1114112 h327680 (by decide +kernel)
  have h851968 := conjugate_word_mem N hn [16, 18] [16, 18, 19] 4 4
    h327680 (by decide +kernel)
  have h524288 := product_word_mem N [16, 18, 19] [16, 18] [19] 5
    h851968 h327680 (by decide +kernel)
  have h65536 := product_word_mem N [16, 20] [20] [16] 1
    h1114112 h1048576 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_2 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 2) ∈ N) : core ≤ N := by
  have h589824 : wordValue [16, 19] ∈ N := hx
  have h1900544 := conjugate_word_mem N hn [16, 19] [16, 18, 19, 20] 1 4
    h589824 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 18, 19, 20] [16, 19] [18, 20] 6
    h1900544 h589824 (by decide +kernel)
  have h65536 := conjugate_word_mem N hn [16, 19] [16] 4 4
    h589824 (by decide +kernel)
  have h524288 := product_word_mem N [16] [16, 19] [19] 1
    h65536 h589824 (by decide +kernel)
  have h1638400 := conjugate_word_mem N hn [16, 19] [16, 19, 20] 5 3
    h589824 (by decide +kernel)
  have h1048576 := product_word_mem N [16, 19, 20] [16, 19] [20] 5
    h1638400 h589824 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_3 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 3) ∈ N) : core ≤ N := by
  have h851968 : wordValue [16, 18, 19] ∈ N := hx
  have h1638400 := conjugate_word_mem N hn [16, 18, 19] [16, 19, 20] 1 7
    h851968 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 19, 20] [16, 18, 19] [18, 20] 7
    h1638400 h851968 (by decide +kernel)
  have h1376256 := conjugate_word_mem N hn [16, 18, 19] [16, 18, 20] 2 8
    h851968 (by decide +kernel)
  have h1572864 := product_word_mem N [16, 18, 20] [16, 18, 19] [19, 20] 6
    h1376256 h851968 (by decide +kernel)
  have h327680 := conjugate_word_mem N hn [16, 18, 19] [16, 18] 4 6
    h851968 (by decide +kernel)
  have h524288 := product_word_mem N [16, 18] [16, 18, 19] [19] 3
    h327680 h851968 (by decide +kernel)
  have h1048576 := product_word_mem N [19] [19, 20] [20] 1
    h524288 h1572864 (by decide +kernel)
  have h65536 := product_word_mem N [16, 19, 20] [19, 20] [16] 3
    h1638400 h1572864 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_4 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 4) ∈ N) : core ≤ N := by
  have h1114112 : wordValue [16, 20] ∈ N := hx
  have h65536 := conjugate_word_mem N hn [16, 20] [16] 0 6
    h1114112 (by decide +kernel)
  have h1048576 := product_word_mem N [16] [16, 20] [20] 1
    h65536 h1114112 (by decide +kernel)
  have h327680 := conjugate_word_mem N hn [16, 20] [16, 18] 1 4
    h1114112 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 18] [16, 20] [18, 20] 2
    h327680 h1114112 (by decide +kernel)
  have h1638400 := conjugate_word_mem N hn [16, 20] [16, 19, 20] 4 3
    h1114112 (by decide +kernel)
  have h524288 := product_word_mem N [16, 19, 20] [16, 20] [19] 4
    h1638400 h1114112 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_5 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 5) ∈ N) : core ≤ N := by
  have h1376256 : wordValue [16, 18, 20] ∈ N := hx
  have h327680 := conjugate_word_mem N hn [16, 18, 20] [16, 18] 0 8
    h1376256 (by decide +kernel)
  have h1048576 := product_word_mem N [16, 18] [16, 18, 20] [20] 3
    h327680 h1376256 (by decide +kernel)
  have h65536 := conjugate_word_mem N hn [16, 18, 20] [16] 1 7
    h1376256 (by decide +kernel)
  have h1310720 := product_word_mem N [16] [16, 18, 20] [18, 20] 1
    h65536 h1376256 (by decide +kernel)
  have h1900544 := conjugate_word_mem N hn [16, 18, 20] [16, 18, 19, 20] 4 5
    h1376256 (by decide +kernel)
  have h524288 := product_word_mem N [16, 18, 19, 20] [16, 18, 20] [19] 8
    h1900544 h1376256 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_6 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 6) ∈ N) : core ≤ N := by
  have h1638400 : wordValue [16, 19, 20] ∈ N := hx
  have h851968 := conjugate_word_mem N hn [16, 19, 20] [16, 18, 19] 1 6
    h1638400 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 18, 19] [16, 19, 20] [18, 20] 4
    h851968 h1638400 (by decide +kernel)
  have h1114112 := conjugate_word_mem N hn [16, 19, 20] [16, 20] 4 5
    h1638400 (by decide +kernel)
  have h524288 := product_word_mem N [16, 20] [16, 19, 20] [19] 4
    h1114112 h1638400 (by decide +kernel)
  have h589824 := conjugate_word_mem N hn [16, 19, 20] [16, 19] 5 5
    h1638400 (by decide +kernel)
  have h1048576 := product_word_mem N [16, 19] [16, 19, 20] [20] 3
    h589824 h1638400 (by decide +kernel)
  have h65536 := product_word_mem N [16, 20] [20] [16] 1
    h1114112 h1048576 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

theorem core_seed_7 (N : Subgroup Carrier) (hn : N.Normal)
    (hx : wordValue ([16] ++ tailWord 7) ∈ N) : core ≤ N := by
  have h1900544 : wordValue [16, 18, 19, 20] ∈ N := hx
  have h589824 := conjugate_word_mem N hn [16, 18, 19, 20] [16, 19] 1 9
    h1900544 (by decide +kernel)
  have h1310720 := product_word_mem N [16, 19] [16, 18, 19, 20] [18, 20] 4
    h589824 h1900544 (by decide +kernel)
  have h327680 := conjugate_word_mem N hn [16, 18, 19, 20] [16, 18] 2 10
    h1900544 (by decide +kernel)
  have h1572864 := product_word_mem N [16, 18] [16, 18, 19, 20] [19, 20] 3
    h327680 h1900544 (by decide +kernel)
  have h1376256 := conjugate_word_mem N hn [16, 18, 19, 20] [16, 18, 20] 4 7
    h1900544 (by decide +kernel)
  have h524288 := product_word_mem N [16, 18, 20] [16, 18, 19, 20] [19] 7
    h1376256 h1900544 (by decide +kernel)
  have h1048576 := product_word_mem N [19] [19, 20] [20] 1
    h524288 h1572864 (by decide +kernel)
  have h1114112 := product_word_mem N [16, 19] [19, 20] [16, 20] 1
    h589824 h1572864 (by decide +kernel)
  have h65536 := product_word_mem N [16, 20] [20] [16] 1
    h1114112 h1048576 (by decide +kernel)
  have h262144 := product_word_mem N [18, 20] [20] [18] 1
    h1310720 h1048576 (by decide +kernel)
  rw [core_eq_span]
  apply (span_le_iff _ _).mpr
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h262144
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h524288
  · simpa only [wordValue_cons, wordValue_nil, mul_one] using h1048576

/-- A member in g16 times the last-three-generator tail forces the whole core. -/
theorem core_seed (N : Subgroup Carrier) (hn : N.Normal) (n : Fin 8)
    (hx : wordValue ([16] ++ tailWord n) ∈ N) : core ≤ N := by
  fin_cases n
  · exact core_seed_0 N hn hx
  · exact core_seed_1 N hn hx
  · exact core_seed_2 N hn hx
  · exact core_seed_3 N hn hx
  · exact core_seed_4 N hn hx
  · exact core_seed_5 N hn hx
  · exact core_seed_6 N hn hx
  · exact core_seed_7 N hn hx

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
