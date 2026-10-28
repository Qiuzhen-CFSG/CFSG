module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.Basic

/-!
# Recovering the core coordinate modulo the normal tail

Generated from the literal presentation by `source/generate.py`.
Every displayed equation is checked by the proved bounded collector.
No discovered group order or subgroup catalogue is used.
Source: SylowNormalEights/source/README.md; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

theorem rep_seed_4 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 4) ∈ N) : generator 16 ∈ N := by
  have h8192 : wordValue [13] ∈ N := hx
  have h73728 := conjugate_mod_tail N hn ht [13] [13, 16] [18, 19] 2 4
    h8192 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 16] [13] [16] [] 2
    h73728 h8192 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_5 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 5) ∈ N) : generator 16 ∈ N := by
  have h8704 : wordValue [9, 13] ∈ N := hx
  have h90624 := conjugate_mod_tail N hn ht [9, 13] [9, 13, 14, 16] [18, 20] 0 25
    h8704 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 13, 14, 16] [9, 13] [14, 16] [19, 20] 12
    h90624 h8704 (by decide +kernel) (by decide +kernel)
  have h25088 := conjugate_mod_tail N hn ht [9, 13] [9, 13, 14] [18] 5 8
    h8704 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14] [9, 13] [14] [19, 20] 8
    h25088 h8704 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_6 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 6) ∈ N) : generator 16 ∈ N := by
  have h10240 : wordValue [11, 13] ∈ N := hx
  have h206848 := conjugate_mod_tail N hn ht [11, 13] [11, 13, 16, 17] [18, 19] 0 18
    h10240 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 16, 17] [11, 13] [16, 17] [] 7
    h206848 h10240 (by decide +kernel) (by decide +kernel)
  have h141312 := conjugate_mod_tail N hn ht [11, 13] [11, 13, 17] [18, 19] 4 6
    h10240 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 17] [11, 13] [17] [] 5
    h141312 h10240 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_7 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 7) ∈ N) : generator 16 ∈ N := by
  have h10752 : wordValue [9, 11, 13] ∈ N := hx
  have h92672 := conjugate_mod_tail N hn ht [9, 11, 13] [9, 11, 13, 14, 16] [18] 0 27
    h10752 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 14, 16] [9, 11, 13] [14, 16] [19, 20] 18
    h92672 h10752 (by decide +kernel) (by decide +kernel)
  have h27136 := conjugate_mod_tail N hn ht [9, 11, 13] [9, 11, 13, 14] [18, 20] 5 11
    h10752 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14] [9, 11, 13] [14] [19, 20] 13
    h27136 h10752 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_12 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 12) ∈ N) : generator 16 ∈ N := by
  have h24576 : wordValue [13, 14] ∈ N := hx
  have h57344 := conjugate_mod_tail N hn ht [13, 14] [13, 14, 15] [18, 19] 1 4
    h24576 (by decide +kernel) (by decide +kernel)
  have h32768 := product_mod_tail N ht [13, 14, 15] [13, 14] [15] [20] 7
    h57344 h24576 (by decide +kernel) (by decide +kernel)
  have h98304 := conjugate_mod_tail N hn ht [15] [15, 16] [18, 19, 20] 0 4
    h32768 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16] [15] [16] [] 2
    h98304 h32768 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_13 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 13) ∈ N) : generator 16 ∈ N := by
  have h25088 : wordValue [9, 13, 14] ∈ N := hx
  have h90624 := conjugate_mod_tail N hn ht [9, 13, 14] [9, 13, 14, 16] [18, 19] 2 15
    h25088 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 16] [9, 13, 14] [16] [19, 20] 16
    h90624 h25088 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_14 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 14) ∈ N) : generator 16 ∈ N := by
  have h26624 : wordValue [11, 13, 14] ∈ N := hx
  have h223232 := conjugate_mod_tail N hn ht [11, 13, 14] [11, 13, 14, 16, 17] [18, 19] 0 13
    h26624 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 14, 16, 17] [11, 13, 14] [16, 17] [20] 15
    h223232 h26624 (by decide +kernel) (by decide +kernel)
  have h157696 := conjugate_mod_tail N hn ht [11, 13, 14] [11, 13, 14, 17] [18, 19, 20] 2 18
    h26624 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 14, 17] [11, 13, 14] [17] [20] 11
    h157696 h26624 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_15 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 15) ∈ N) : generator 16 ∈ N := by
  have h27136 : wordValue [9, 11, 13, 14] ∈ N := hx
  have h76288 := conjugate_mod_tail N hn ht [9, 11, 13, 14] [9, 11, 13, 16] [18] 0 25
    h27136 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 16] [9, 11, 13, 14] [14, 16] [19] 14
    h76288 h27136 (by decide +kernel) (by decide +kernel)
  have h10752 := conjugate_mod_tail N hn ht [9, 11, 13, 14] [9, 11, 13] [18] 5 16
    h27136 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13] [9, 11, 13, 14] [14] [19] 9
    h10752 h27136 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_16 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 16) ∈ N) : generator 16 ∈ N := by
  have h32768 : wordValue [15] ∈ N := hx
  have h98304 := conjugate_mod_tail N hn ht [15] [15, 16] [18, 19, 20] 0 4
    h32768 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16] [15] [16] [] 2
    h98304 h32768 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_17 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 17) ∈ N) : generator 16 ∈ N := by
  have h33280 : wordValue [9, 15] ∈ N := hx
  have h246272 := conjugate_mod_tail N hn ht [9, 15] [9, 14, 15, 16, 17] [18] 0 21
    h33280 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 14, 15, 16, 17] [9, 15] [14, 16, 17] [] 8
    h246272 h33280 (by decide +kernel) (by decide +kernel)
  have h164352 := conjugate_mod_tail N hn ht [9, 15] [9, 15, 17] [18] 2 6
    h33280 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 15, 17] [9, 15] [17] [] 5
    h164352 h33280 (by decide +kernel) (by decide +kernel)
  have h49664 := conjugate_mod_tail N hn ht [9, 15] [9, 14, 15] [18, 20] 5 5
    h33280 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 14, 15] [9, 15] [14] [] 4
    h49664 h33280 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_18 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 18) ∈ N) : generator 16 ∈ N := by
  have h34816 : wordValue [11, 15] ∈ N := hx
  have h100352 := conjugate_mod_tail N hn ht [11, 15] [11, 15, 16] [18, 19] 0 13
    h34816 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 15, 16] [11, 15] [16] [20] 7
    h100352 h34816 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_19 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 19) ∈ N) : generator 16 ∈ N := by
  have h35328 : wordValue [9, 11, 15] ∈ N := hx
  have h231936 := conjugate_mod_tail N hn ht [9, 11, 15] [9, 11, 15, 16, 17] [18, 20] 2 12
    h35328 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 11, 15, 16, 17] [9, 11, 15] [16, 17] [20] 15
    h231936 h35328 (by decide +kernel) (by decide +kernel)
  have h166400 := conjugate_mod_tail N hn ht [9, 11, 15] [9, 11, 15, 17] [18, 19] 4 7
    h35328 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 11, 15, 17] [9, 11, 15] [17] [20] 11
    h166400 h35328 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_20 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 20) ∈ N) : generator 16 ∈ N := by
  have h40960 : wordValue [13, 15] ∈ N := hx
  have h106496 := conjugate_mod_tail N hn ht [13, 15] [13, 15, 16] [19] 2 10
    h40960 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 15, 16] [13, 15] [16] [] 5
    h106496 h40960 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_21 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 21) ∈ N) : generator 16 ∈ N := by
  have h41472 : wordValue [9, 13, 15] ∈ N := hx
  have h57856 := conjugate_mod_tail N hn ht [9, 13, 15] [9, 13, 14, 15] [19] 0 33
    h41472 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 15] [9, 13, 15] [14] [19, 20] 15
    h57856 h41472 (by decide +kernel) (by decide +kernel)
  have h238080 := conjugate_mod_tail N hn ht [9, 13, 15] [9, 13, 15, 16, 17] [19] 2 14
    h41472 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 13, 15, 16, 17] [9, 13, 15] [16, 17] [19] 17
    h238080 h41472 (by decide +kernel) (by decide +kernel)
  have h147456 := conjugate_mod_tail N hn ht [14] [14, 17] [] 2 4
    h16384 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 17] [14] [17] [] 2
    h147456 h16384 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_22 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 22) ∈ N) : generator 16 ∈ N := by
  have h43008 : wordValue [11, 13, 15] ∈ N := hx
  have h223232 := conjugate_mod_tail N hn ht [11, 13, 15] [11, 13, 14, 16, 17] [18, 19] 1 24
    h43008 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 14, 16, 17] [11, 13, 15] [14, 15, 16, 17] [20] 14
    h223232 h43008 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_23 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 23) ∈ N) : generator 16 ∈ N := by
  have h43520 : wordValue [9, 11, 13, 15] ∈ N := hx
  have h59904 := conjugate_mod_tail N hn ht [9, 11, 13, 15] [9, 11, 13, 14, 15] [19, 20] 0 38
    h43520 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 15] [9, 11, 13, 15] [14] [19] 23
    h59904 h43520 (by decide +kernel) (by decide +kernel)
  have h223744 := conjugate_mod_tail N hn ht [9, 11, 13, 15] [9, 11, 13, 14, 16, 17] [18, 20] 1 34
    h43520 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 14, 16, 17] [9, 11, 13, 15] [14, 15, 16, 17] [19, 20] 27
    h223744 h43520 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_24 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 24) ∈ N) : generator 16 ∈ N := by
  have h49152 : wordValue [14, 15] ∈ N := hx
  have h114688 := conjugate_mod_tail N hn ht [14, 15] [14, 15, 16] [18, 19, 20] 0 3
    h49152 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 16] [14, 15] [16] [] 5
    h114688 h49152 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_25 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 25) ∈ N) : generator 16 ∈ N := by
  have h49664 : wordValue [9, 14, 15] ∈ N := hx
  have h229888 := conjugate_mod_tail N hn ht [9, 14, 15] [9, 15, 16, 17] [18] 0 18
    h49664 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 15, 16, 17] [9, 14, 15] [14, 16, 17] [] 10
    h229888 h49664 (by decide +kernel) (by decide +kernel)
  have h33280 := conjugate_mod_tail N hn ht [9, 14, 15] [9, 15] [18] 5 9
    h49664 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 15] [9, 14, 15] [14] [] 4
    h33280 h49664 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h81920 := conjugate_mod_tail N hn ht [14, 16, 17] [14, 16] [] 2 8
    h212992 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 16] [14, 16, 17] [17] [] 3
    h81920 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_26 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 26) ∈ N) : generator 16 ∈ N := by
  have h51200 : wordValue [11, 14, 15] ∈ N := hx
  have h116736 := conjugate_mod_tail N hn ht [11, 14, 15] [11, 14, 15, 16] [18, 19] 0 11
    h51200 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 14, 15, 16] [11, 14, 15] [16] [20] 12
    h116736 h51200 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_27 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 27) ∈ N) : generator 16 ∈ N := by
  have h51712 : wordValue [9, 11, 14, 15] ∈ N := hx
  have h117248 := conjugate_mod_tail N hn ht [9, 11, 14, 15] [9, 11, 14, 15, 16] [18, 20] 2 17
    h51712 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 11, 14, 15, 16] [9, 11, 14, 15] [16] [20] 17
    h117248 h51712 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_28 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 28) ∈ N) : generator 16 ∈ N := by
  have h57344 : wordValue [13, 14, 15] ∈ N := hx
  have h188416 := conjugate_mod_tail N hn ht [13, 14, 15] [13, 14, 15, 17] [] 0 26
    h57344 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [13, 14, 15, 17] [13, 14, 15] [17] [20] 13
    h188416 h57344 (by decide +kernel) (by decide +kernel)
  have h253952 := conjugate_mod_tail N hn ht [13, 14, 15] [13, 14, 15, 16, 17] [19] 2 17
    h57344 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [13, 14, 15, 16, 17] [13, 14, 15] [16, 17] [20] 17
    h253952 h57344 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_29 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 29) ∈ N) : generator 16 ∈ N := by
  have h57856 : wordValue [9, 13, 14, 15] ∈ N := hx
  have h123392 := conjugate_mod_tail N hn ht [9, 13, 14, 15] [9, 13, 14, 15, 16] [19] 2 21
    h57856 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 15, 16] [9, 13, 14, 15] [16] [19, 20] 25
    h123392 h57856 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_30 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 30) ∈ N) : generator 16 ∈ N := by
  have h59392 : wordValue [11, 13, 14, 15] ∈ N := hx
  have h206848 := conjugate_mod_tail N hn ht [11, 13, 14, 15] [11, 13, 16, 17] [] 1 32
    h59392 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 16, 17] [11, 13, 14, 15] [14, 15, 16, 17] [] 11
    h206848 h59392 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_31 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 31) ∈ N) : generator 16 ∈ N := by
  have h59904 : wordValue [9, 11, 13, 14, 15] ∈ N := hx
  have h43520 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15] [9, 11, 13, 15] [19, 20] 0 36
    h59904 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 15] [9, 11, 13, 14, 15] [14] [19, 20] 20
    h43520 h59904 (by decide +kernel) (by decide +kernel)
  have h207360 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15] [9, 11, 13, 16, 17] [19, 20] 1 44
    h59904 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 16, 17] [9, 11, 13, 14, 15] [14, 15, 16, 17] [19] 22
    h207360 h59904 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_36 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 36) ∈ N) : generator 16 ∈ N := by
  have h73728 : wordValue [13, 16] ∈ N := hx
  have h8192 := conjugate_mod_tail N hn ht [13, 16] [13] [18, 19] 2 8
    h73728 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13] [13, 16] [16] [] 1
    h8192 h73728 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_37 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 37) ∈ N) : generator 16 ∈ N := by
  have h74240 : wordValue [9, 13, 16] ∈ N := hx
  have h25088 := conjugate_mod_tail N hn ht [9, 13, 16] [9, 13, 14] [18] 0 30
    h74240 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 13, 14] [9, 13, 16] [14, 16] [19, 20] 10
    h25088 h74240 (by decide +kernel) (by decide +kernel)
  have h90624 := conjugate_mod_tail N hn ht [9, 13, 16] [9, 13, 14, 16] [18] 5 10
    h74240 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 16] [9, 13, 16] [14] [19, 20] 15
    h90624 h74240 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_38 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 38) ∈ N) : generator 16 ∈ N := by
  have h75776 : wordValue [11, 13, 16] ∈ N := hx
  have h141312 := conjugate_mod_tail N hn ht [11, 13, 16] [11, 13, 17] [18, 19, 20] 0 25
    h75776 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 17] [11, 13, 16] [16, 17] [] 6
    h141312 h75776 (by decide +kernel) (by decide +kernel)
  have h206848 := conjugate_mod_tail N hn ht [11, 13, 16] [11, 13, 16, 17] [18] 4 11
    h75776 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 16, 17] [11, 13, 16] [17] [] 9
    h206848 h75776 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_39 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 39) ∈ N) : generator 16 ∈ N := by
  have h76288 : wordValue [9, 11, 13, 16] ∈ N := hx
  have h27136 := conjugate_mod_tail N hn ht [9, 11, 13, 16] [9, 11, 13, 14] [18, 20] 0 32
    h76288 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 14] [9, 11, 13, 16] [14, 16] [19, 20] 15
    h27136 h76288 (by decide +kernel) (by decide +kernel)
  have h92672 := conjugate_mod_tail N hn ht [9, 11, 13, 16] [9, 11, 13, 14, 16] [18, 20] 5 14
    h76288 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 16] [9, 11, 13, 16] [14] [19, 20] 21
    h92672 h76288 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_44 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 44) ∈ N) : generator 16 ∈ N := by
  have h90112 : wordValue [13, 14, 16] ∈ N := hx
  have h122880 := conjugate_mod_tail N hn ht [13, 14, 16] [13, 14, 15, 16] [19, 20] 1 9
    h90112 (by decide +kernel) (by decide +kernel)
  have h32768 := product_mod_tail N ht [13, 14, 15, 16] [13, 14, 16] [15] [20] 12
    h122880 h90112 (by decide +kernel) (by decide +kernel)
  have h98304 := conjugate_mod_tail N hn ht [15] [15, 16] [18, 19, 20] 0 4
    h32768 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16] [15] [16] [] 2
    h98304 h32768 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_45 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 45) ∈ N) : generator 16 ∈ N := by
  have h90624 : wordValue [9, 13, 14, 16] ∈ N := hx
  have h25088 := conjugate_mod_tail N hn ht [9, 13, 14, 16] [9, 13, 14] [18, 19] 2 19
    h90624 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14] [9, 13, 14, 16] [16] [19, 20] 13
    h25088 h90624 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_46 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 46) ∈ N) : generator 16 ∈ N := by
  have h92160 : wordValue [11, 13, 14, 16] ∈ N := hx
  have h157696 := conjugate_mod_tail N hn ht [11, 13, 14, 16] [11, 13, 14, 17] [18, 19, 20] 0 20
    h92160 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 14, 17] [11, 13, 14, 16] [16, 17] [20] 13
    h157696 h92160 (by decide +kernel) (by decide +kernel)
  have h223232 := conjugate_mod_tail N hn ht [11, 13, 14, 16] [11, 13, 14, 16, 17] [18, 19, 20] 2 23
    h92160 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 14, 16, 17] [11, 13, 14, 16] [17] [20] 18
    h223232 h92160 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_47 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 47) ∈ N) : generator 16 ∈ N := by
  have h92672 : wordValue [9, 11, 13, 14, 16] ∈ N := hx
  have h10752 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 16] [9, 11, 13] [18, 20] 0 30
    h92672 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13] [9, 11, 13, 14, 16] [14, 16] [19] 10
    h10752 h92672 (by decide +kernel) (by decide +kernel)
  have h76288 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 16] [9, 11, 13, 16] [18] 5 18
    h92672 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 16] [9, 11, 13, 14, 16] [14] [19] 16
    h76288 h92672 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_48 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 48) ∈ N) : generator 16 ∈ N := by
  have h98304 : wordValue [15, 16] ∈ N := hx
  have h32768 := conjugate_mod_tail N hn ht [15, 16] [15] [18, 19] 0 10
    h98304 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15] [15, 16] [16] [] 1
    h32768 h98304 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_49 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 49) ∈ N) : generator 16 ∈ N := by
  have h98816 : wordValue [9, 15, 16] ∈ N := hx
  have h180736 := conjugate_mod_tail N hn ht [9, 15, 16] [9, 14, 15, 17] [18, 20] 0 25
    h98816 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 14, 15, 17] [9, 15, 16] [14, 16, 17] [] 7
    h180736 h98816 (by decide +kernel) (by decide +kernel)
  have h229888 := conjugate_mod_tail N hn ht [9, 15, 16] [9, 15, 16, 17] [18] 2 9
    h98816 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 15, 16, 17] [9, 15, 16] [17] [] 9
    h229888 h98816 (by decide +kernel) (by decide +kernel)
  have h115200 := conjugate_mod_tail N hn ht [9, 15, 16] [9, 14, 15, 16] [18, 20] 5 8
    h98816 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 14, 15, 16] [9, 15, 16] [14] [] 7
    h115200 h98816 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_50 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 50) ∈ N) : generator 16 ∈ N := by
  have h100352 : wordValue [11, 15, 16] ∈ N := hx
  have h34816 := conjugate_mod_tail N hn ht [11, 15, 16] [11, 15] [18, 19, 20] 0 17
    h100352 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 15] [11, 15, 16] [16] [20] 5
    h34816 h100352 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_51 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 51) ∈ N) : generator 16 ∈ N := by
  have h100864 : wordValue [9, 11, 15, 16] ∈ N := hx
  have h166400 := conjugate_mod_tail N hn ht [9, 11, 15, 16] [9, 11, 15, 17] [18, 20] 2 17
    h100864 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 11, 15, 17] [9, 11, 15, 16] [16, 17] [20] 13
    h166400 h100864 (by decide +kernel) (by decide +kernel)
  have h231936 := conjugate_mod_tail N hn ht [9, 11, 15, 16] [9, 11, 15, 16, 17] [18] 4 12
    h100864 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 11, 15, 16, 17] [9, 11, 15, 16] [17] [20] 18
    h231936 h100864 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_52 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 52) ∈ N) : generator 16 ∈ N := by
  have h106496 : wordValue [13, 15, 16] ∈ N := hx
  have h40960 := conjugate_mod_tail N hn ht [13, 15, 16] [13, 15] [19] 2 13
    h106496 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 15] [13, 15, 16] [16] [] 3
    h40960 h106496 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_53 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 53) ∈ N) : generator 16 ∈ N := by
  have h107008 : wordValue [9, 13, 15, 16] ∈ N := hx
  have h123392 := conjugate_mod_tail N hn ht [9, 13, 15, 16] [9, 13, 14, 15, 16] [19, 20] 0 37
    h107008 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 15, 16] [9, 13, 15, 16] [14] [19, 20] 23
    h123392 h107008 (by decide +kernel) (by decide +kernel)
  have h172544 := conjugate_mod_tail N hn ht [9, 13, 15, 16] [9, 13, 15, 17] [19] 2 18
    h107008 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 13, 15, 17] [9, 13, 15, 16] [16, 17] [19] 15
    h172544 h107008 (by decide +kernel) (by decide +kernel)
  have h147456 := conjugate_mod_tail N hn ht [14] [14, 17] [] 2 4
    h16384 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 17] [14] [17] [] 2
    h147456 h16384 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_54 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 54) ∈ N) : generator 16 ∈ N := by
  have h108544 : wordValue [11, 13, 15, 16] ∈ N := hx
  have h157696 := conjugate_mod_tail N hn ht [11, 13, 15, 16] [11, 13, 14, 17] [19, 20] 1 31
    h108544 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 14, 17] [11, 13, 15, 16] [14, 15, 16, 17] [20] 12
    h157696 h108544 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_55 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 55) ∈ N) : generator 16 ∈ N := by
  have h109056 : wordValue [9, 11, 13, 15, 16] ∈ N := hx
  have h125440 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 16] [9, 11, 13, 14, 15, 16] [19] 0 42
    h109056 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 15, 16] [9, 11, 13, 15, 16] [14] [19] 32
    h125440 h109056 (by decide +kernel) (by decide +kernel)
  have h158208 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 16] [9, 11, 13, 14, 17] [] 1 42
    h109056 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 14, 17] [9, 11, 13, 15, 16] [14, 15, 16, 17] [19, 20] 24
    h158208 h109056 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_56 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 56) ∈ N) : generator 16 ∈ N := by
  have h114688 : wordValue [14, 15, 16] ∈ N := hx
  have h49152 := conjugate_mod_tail N hn ht [14, 15, 16] [14, 15] [18, 19] 0 9
    h114688 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15] [14, 15, 16] [16] [] 3
    h49152 h114688 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_57 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 57) ∈ N) : generator 16 ∈ N := by
  have h115200 : wordValue [9, 14, 15, 16] ∈ N := hx
  have h164352 := conjugate_mod_tail N hn ht [9, 14, 15, 16] [9, 15, 17] [18, 20] 0 22
    h115200 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 15, 17] [9, 14, 15, 16] [14, 16, 17] [] 8
    h164352 h115200 (by decide +kernel) (by decide +kernel)
  have h98816 := conjugate_mod_tail N hn ht [9, 14, 15, 16] [9, 15, 16] [18] 5 11
    h115200 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 15, 16] [9, 14, 15, 16] [14] [] 8
    h98816 h115200 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h81920 := conjugate_mod_tail N hn ht [14, 16, 17] [14, 16] [] 2 8
    h212992 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 16] [14, 16, 17] [17] [] 3
    h81920 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_58 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 58) ∈ N) : generator 16 ∈ N := by
  have h116736 : wordValue [11, 14, 15, 16] ∈ N := hx
  have h51200 := conjugate_mod_tail N hn ht [11, 14, 15, 16] [11, 14, 15] [18, 19, 20] 0 15
    h116736 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 14, 15] [11, 14, 15, 16] [16] [20] 9
    h51200 h116736 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_59 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 59) ∈ N) : generator 16 ∈ N := by
  have h117248 : wordValue [9, 11, 14, 15, 16] ∈ N := hx
  have h51712 := conjugate_mod_tail N hn ht [9, 11, 14, 15, 16] [9, 11, 14, 15] [18, 20] 2 21
    h117248 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 11, 14, 15] [9, 11, 14, 15, 16] [16] [20] 13
    h51712 h117248 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_60 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 60) ∈ N) : generator 16 ∈ N := by
  have h122880 : wordValue [13, 14, 15, 16] ∈ N := hx
  have h253952 := conjugate_mod_tail N hn ht [13, 14, 15, 16] [13, 14, 15, 16, 17] [20] 0 30
    h122880 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [13, 14, 15, 16, 17] [13, 14, 15, 16] [17] [20] 20
    h253952 h122880 (by decide +kernel) (by decide +kernel)
  have h188416 := conjugate_mod_tail N hn ht [13, 14, 15, 16] [13, 14, 15, 17] [19] 2 21
    h122880 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [13, 14, 15, 17] [13, 14, 15, 16] [16, 17] [20] 15
    h188416 h122880 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_61 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 61) ∈ N) : generator 16 ∈ N := by
  have h123392 : wordValue [9, 13, 14, 15, 16] ∈ N := hx
  have h57856 := conjugate_mod_tail N hn ht [9, 13, 14, 15, 16] [9, 13, 14, 15] [19] 2 24
    h123392 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 15] [9, 13, 14, 15, 16] [16] [19, 20] 21
    h57856 h123392 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_62 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 62) ∈ N) : generator 16 ∈ N := by
  have h124928 : wordValue [11, 13, 14, 15, 16] ∈ N := hx
  have h141312 := conjugate_mod_tail N hn ht [11, 13, 14, 15, 16] [11, 13, 17] [18, 20] 1 35
    h124928 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 17] [11, 13, 14, 15, 16] [14, 15, 16, 17] [] 8
    h141312 h124928 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_63 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 63) ∈ N) : generator 16 ∈ N := by
  have h125440 : wordValue [9, 11, 13, 14, 15, 16] ∈ N := hx
  have h109056 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 16] [9, 11, 13, 15, 16] [19] 0 40
    h125440 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 15, 16] [9, 11, 13, 14, 15, 16] [14] [19, 20] 30
    h109056 h125440 (by decide +kernel) (by decide +kernel)
  have h141824 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 16] [9, 11, 13, 17] [18, 19] 1 52
    h125440 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 17] [9, 11, 13, 14, 15, 16] [14, 15, 16, 17] [19] 18
    h141824 h125440 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_68 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 68) ∈ N) : generator 16 ∈ N := by
  have h139264 : wordValue [13, 17] ∈ N := hx
  have h204800 := conjugate_mod_tail N hn ht [13, 17] [13, 16, 17] [18, 19] 2 7
    h139264 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 16, 17] [13, 17] [16] [] 4
    h204800 h139264 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_69 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 69) ∈ N) : generator 16 ∈ N := by
  have h139776 : wordValue [9, 13, 17] ∈ N := hx
  have h221696 := conjugate_mod_tail N hn ht [9, 13, 17] [9, 13, 14, 16, 17] [18] 0 29
    h139776 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 13, 14, 16, 17] [9, 13, 17] [14, 16] [19, 20] 19
    h221696 h139776 (by decide +kernel) (by decide +kernel)
  have h156160 := conjugate_mod_tail N hn ht [9, 13, 17] [9, 13, 14, 17] [18] 5 10
    h139776 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 17] [9, 13, 17] [14] [19, 20] 15
    h156160 h139776 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_70 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 70) ∈ N) : generator 16 ∈ N := by
  have h141312 : wordValue [11, 13, 17] ∈ N := hx
  have h75776 := conjugate_mod_tail N hn ht [11, 13, 17] [11, 13, 16] [18, 19, 20] 0 24
    h141312 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 16] [11, 13, 17] [16, 17] [] 5
    h75776 h141312 (by decide +kernel) (by decide +kernel)
  have h10240 := conjugate_mod_tail N hn ht [11, 13, 17] [11, 13] [18, 19] 4 10
    h141312 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13] [11, 13, 17] [17] [] 3
    h10240 h141312 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_71 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 71) ∈ N) : generator 16 ∈ N := by
  have h141824 : wordValue [9, 11, 13, 17] ∈ N := hx
  have h223744 := conjugate_mod_tail N hn ht [9, 11, 13, 17] [9, 11, 13, 14, 16, 17] [18, 20] 0 31
    h141824 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 14, 16, 17] [9, 11, 13, 17] [14, 16] [19, 20] 26
    h223744 h141824 (by decide +kernel) (by decide +kernel)
  have h158208 := conjugate_mod_tail N hn ht [9, 11, 13, 17] [9, 11, 13, 14, 17] [18, 20] 5 14
    h141824 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 17] [9, 11, 13, 17] [14] [19, 20] 21
    h158208 h141824 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_76 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 76) ∈ N) : generator 16 ∈ N := by
  have h155648 : wordValue [13, 14, 17] ∈ N := hx
  have h188416 := conjugate_mod_tail N hn ht [13, 14, 17] [13, 14, 15, 17] [18, 20] 1 8
    h155648 (by decide +kernel) (by decide +kernel)
  have h32768 := product_mod_tail N ht [13, 14, 15, 17] [13, 14, 17] [15] [20] 12
    h188416 h155648 (by decide +kernel) (by decide +kernel)
  have h98304 := conjugate_mod_tail N hn ht [15] [15, 16] [18, 19, 20] 0 4
    h32768 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16] [15] [16] [] 2
    h98304 h32768 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_77 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 77) ∈ N) : generator 16 ∈ N := by
  have h156160 : wordValue [9, 13, 14, 17] ∈ N := hx
  have h221696 := conjugate_mod_tail N hn ht [9, 13, 14, 17] [9, 13, 14, 16, 17] [18, 19] 2 18
    h156160 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 16, 17] [9, 13, 14, 17] [16] [19, 20] 24
    h221696 h156160 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_78 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 78) ∈ N) : generator 16 ∈ N := by
  have h157696 : wordValue [11, 13, 14, 17] ∈ N := hx
  have h92160 := conjugate_mod_tail N hn ht [11, 13, 14, 17] [11, 13, 14, 16] [18, 19, 20] 0 19
    h157696 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 14, 16] [11, 13, 14, 17] [16, 17] [20] 12
    h92160 h157696 (by decide +kernel) (by decide +kernel)
  have h26624 := conjugate_mod_tail N hn ht [11, 13, 14, 17] [11, 13, 14] [18, 19, 20] 2 23
    h157696 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 14] [11, 13, 14, 17] [17] [20] 8
    h26624 h157696 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_79 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 79) ∈ N) : generator 16 ∈ N := by
  have h158208 : wordValue [9, 11, 13, 14, 17] ∈ N := hx
  have h207360 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 17] [9, 11, 13, 16, 17] [18, 20] 0 29
    h158208 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 16, 17] [9, 11, 13, 14, 17] [14, 16] [19] 21
    h207360 h158208 (by decide +kernel) (by decide +kernel)
  have h141824 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 17] [9, 11, 13, 17] [18] 5 18
    h158208 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 17] [9, 11, 13, 14, 17] [14] [19] 16
    h141824 h158208 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_80 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 80) ∈ N) : generator 16 ∈ N := by
  have h163840 : wordValue [15, 17] ∈ N := hx
  have h229376 := conjugate_mod_tail N hn ht [15, 17] [15, 16, 17] [18, 19] 0 9
    h163840 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16, 17] [15, 17] [16] [] 4
    h229376 h163840 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_81 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 81) ∈ N) : generator 16 ∈ N := by
  have h164352 : wordValue [9, 15, 17] ∈ N := hx
  have h115200 := conjugate_mod_tail N hn ht [9, 15, 17] [9, 14, 15, 16] [18, 20] 0 24
    h164352 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 14, 15, 16] [9, 15, 17] [14, 16, 17] [] 6
    h115200 h164352 (by decide +kernel) (by decide +kernel)
  have h33280 := conjugate_mod_tail N hn ht [9, 15, 17] [9, 15] [18] 2 9
    h164352 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 15] [9, 15, 17] [17] [] 3
    h33280 h164352 (by decide +kernel) (by decide +kernel)
  have h180736 := conjugate_mod_tail N hn ht [9, 15, 17] [9, 14, 15, 17] [18, 20] 5 8
    h164352 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 14, 15, 17] [9, 15, 17] [14] [] 7
    h180736 h164352 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_82 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 82) ∈ N) : generator 16 ∈ N := by
  have h165888 : wordValue [11, 15, 17] ∈ N := hx
  have h231424 := conjugate_mod_tail N hn ht [11, 15, 17] [11, 15, 16, 17] [18, 19, 20] 0 16
    h165888 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 15, 16, 17] [11, 15, 17] [16] [20] 12
    h231424 h165888 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_83 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 83) ∈ N) : generator 16 ∈ N := by
  have h166400 : wordValue [9, 11, 15, 17] ∈ N := hx
  have h100864 := conjugate_mod_tail N hn ht [9, 11, 15, 17] [9, 11, 15, 16] [18, 20] 2 16
    h166400 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 11, 15, 16] [9, 11, 15, 17] [16, 17] [20] 12
    h100864 h166400 (by decide +kernel) (by decide +kernel)
  have h35328 := conjugate_mod_tail N hn ht [9, 11, 15, 17] [9, 11, 15] [18, 19] 4 11
    h166400 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 11, 15] [9, 11, 15, 17] [17] [20] 8
    h35328 h166400 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_84 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 84) ∈ N) : generator 16 ∈ N := by
  have h172032 : wordValue [13, 15, 17] ∈ N := hx
  have h237568 := conjugate_mod_tail N hn ht [13, 15, 17] [13, 15, 16, 17] [19] 2 12
    h172032 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 15, 16, 17] [13, 15, 17] [16] [] 8
    h237568 h172032 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_85 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 85) ∈ N) : generator 16 ∈ N := by
  have h172544 : wordValue [9, 13, 15, 17] ∈ N := hx
  have h188928 := conjugate_mod_tail N hn ht [9, 13, 15, 17] [9, 13, 14, 15, 17] [19, 20] 0 37
    h172544 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 15, 17] [9, 13, 15, 17] [14] [19, 20] 23
    h188928 h172544 (by decide +kernel) (by decide +kernel)
  have h107008 := conjugate_mod_tail N hn ht [9, 13, 15, 17] [9, 13, 15, 16] [19] 2 17
    h172544 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 13, 15, 16] [9, 13, 15, 17] [16, 17] [19] 14
    h107008 h172544 (by decide +kernel) (by decide +kernel)
  have h147456 := conjugate_mod_tail N hn ht [14] [14, 17] [] 2 4
    h16384 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 17] [14] [17] [] 2
    h147456 h16384 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_86 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 86) ∈ N) : generator 16 ∈ N := by
  have h174080 : wordValue [11, 13, 15, 17] ∈ N := hx
  have h92160 := conjugate_mod_tail N hn ht [11, 13, 15, 17] [11, 13, 14, 16] [18, 20] 1 29
    h174080 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 14, 16] [11, 13, 15, 17] [14, 15, 16, 17] [20] 11
    h92160 h174080 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_87 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 87) ∈ N) : generator 16 ∈ N := by
  have h174592 : wordValue [9, 11, 13, 15, 17] ∈ N := hx
  have h190976 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 17] [9, 11, 13, 14, 15, 17] [19] 0 42
    h174592 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 15, 17] [9, 11, 13, 15, 17] [14] [19] 32
    h190976 h174592 (by decide +kernel) (by decide +kernel)
  have h92672 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 17] [9, 11, 13, 14, 16] [18, 19] 1 40
    h174592 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 14, 16] [9, 11, 13, 15, 17] [14, 15, 16, 17] [19, 20] 23
    h92672 h174592 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_88 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 88) ∈ N) : generator 16 ∈ N := by
  have h180224 : wordValue [14, 15, 17] ∈ N := hx
  have h245760 := conjugate_mod_tail N hn ht [14, 15, 17] [14, 15, 16, 17] [18, 19] 0 8
    h180224 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 16, 17] [14, 15, 17] [16] [] 8
    h245760 h180224 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_89 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 89) ∈ N) : generator 16 ∈ N := by
  have h180736 : wordValue [9, 14, 15, 17] ∈ N := hx
  have h98816 := conjugate_mod_tail N hn ht [9, 14, 15, 17] [9, 15, 16] [18, 20] 0 21
    h180736 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 15, 16] [9, 14, 15, 17] [14, 16, 17] [] 7
    h98816 h180736 (by decide +kernel) (by decide +kernel)
  have h164352 := conjugate_mod_tail N hn ht [9, 14, 15, 17] [9, 15, 17] [18] 5 11
    h180736 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 15, 17] [9, 14, 15, 17] [14] [] 8
    h164352 h180736 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h81920 := conjugate_mod_tail N hn ht [14, 16, 17] [14, 16] [] 2 8
    h212992 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 16] [14, 16, 17] [17] [] 3
    h81920 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_90 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 90) ∈ N) : generator 16 ∈ N := by
  have h182272 : wordValue [11, 14, 15, 17] ∈ N := hx
  have h247808 := conjugate_mod_tail N hn ht [11, 14, 15, 17] [11, 14, 15, 16, 17] [18, 19, 20] 0 14
    h182272 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 14, 15, 16, 17] [11, 14, 15, 17] [16] [20] 18
    h247808 h182272 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_91 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 91) ∈ N) : generator 16 ∈ N := by
  have h182784 : wordValue [9, 11, 14, 15, 17] ∈ N := hx
  have h248320 := conjugate_mod_tail N hn ht [9, 11, 14, 15, 17] [9, 11, 14, 15, 16, 17] [18, 20] 2 20
    h182784 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 11, 14, 15, 16, 17] [9, 11, 14, 15, 17] [16] [20] 24
    h248320 h182784 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_92 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 92) ∈ N) : generator 16 ∈ N := by
  have h188416 : wordValue [13, 14, 15, 17] ∈ N := hx
  have h57344 := conjugate_mod_tail N hn ht [13, 14, 15, 17] [13, 14, 15] [20] 0 30
    h188416 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [13, 14, 15] [13, 14, 15, 17] [17] [20] 10
    h57344 h188416 (by decide +kernel) (by decide +kernel)
  have h122880 := conjugate_mod_tail N hn ht [13, 14, 15, 17] [13, 14, 15, 16] [19] 2 20
    h188416 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [13, 14, 15, 16] [13, 14, 15, 17] [16, 17] [20] 14
    h122880 h188416 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_93 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 93) ∈ N) : generator 16 ∈ N := by
  have h188928 : wordValue [9, 13, 14, 15, 17] ∈ N := hx
  have h254464 := conjugate_mod_tail N hn ht [9, 13, 14, 15, 17] [9, 13, 14, 15, 16, 17] [19] 2 23
    h188928 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 15, 16, 17] [9, 13, 14, 15, 17] [16] [19, 20] 34
    h254464 h188928 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_94 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 94) ∈ N) : generator 16 ∈ N := by
  have h190464 : wordValue [11, 13, 14, 15, 17] ∈ N := hx
  have h75776 := conjugate_mod_tail N hn ht [11, 13, 14, 15, 17] [11, 13, 16] [19, 20] 1 34
    h190464 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 16] [11, 13, 14, 15, 17] [14, 15, 16, 17] [] 7
    h75776 h190464 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_95 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 95) ∈ N) : generator 16 ∈ N := by
  have h190976 : wordValue [9, 11, 13, 14, 15, 17] ∈ N := hx
  have h174592 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 17] [9, 11, 13, 15, 17] [19] 0 40
    h190976 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 15, 17] [9, 11, 13, 14, 15, 17] [14] [19, 20] 30
    h174592 h190976 (by decide +kernel) (by decide +kernel)
  have h76288 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 17] [9, 11, 13, 16] [] 1 51
    h190976 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 16] [9, 11, 13, 14, 15, 17] [14, 15, 16, 17] [19] 17
    h76288 h190976 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_100 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 100) ∈ N) : generator 16 ∈ N := by
  have h204800 : wordValue [13, 16, 17] ∈ N := hx
  have h139264 := conjugate_mod_tail N hn ht [13, 16, 17] [13, 17] [18, 19] 2 11
    h204800 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 17] [13, 16, 17] [16] [] 4
    h139264 h204800 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_101 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 101) ∈ N) : generator 16 ∈ N := by
  have h205312 : wordValue [9, 13, 16, 17] ∈ N := hx
  have h156160 := conjugate_mod_tail N hn ht [9, 13, 16, 17] [9, 13, 14, 17] [18, 20] 0 34
    h205312 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 13, 14, 17] [9, 13, 16, 17] [14, 16] [19, 20] 18
    h156160 h205312 (by decide +kernel) (by decide +kernel)
  have h221696 := conjugate_mod_tail N hn ht [9, 13, 16, 17] [9, 13, 14, 16, 17] [18] 5 12
    h205312 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 16, 17] [9, 13, 16, 17] [14] [19, 20] 23
    h221696 h205312 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_102 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 102) ∈ N) : generator 16 ∈ N := by
  have h206848 : wordValue [11, 13, 16, 17] ∈ N := hx
  have h10240 := conjugate_mod_tail N hn ht [11, 13, 16, 17] [11, 13] [18, 19] 0 31
    h206848 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13] [11, 13, 16, 17] [16, 17] [] 3
    h10240 h206848 (by decide +kernel) (by decide +kernel)
  have h75776 := conjugate_mod_tail N hn ht [11, 13, 16, 17] [11, 13, 16] [18] 4 14
    h206848 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 16] [11, 13, 16, 17] [17] [] 6
    h75776 h206848 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_103 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 103) ∈ N) : generator 16 ∈ N := by
  have h207360 : wordValue [9, 11, 13, 16, 17] ∈ N := hx
  have h158208 := conjugate_mod_tail N hn ht [9, 11, 13, 16, 17] [9, 11, 13, 14, 17] [18] 0 36
    h207360 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 14, 17] [9, 11, 13, 16, 17] [14, 16] [19, 20] 24
    h158208 h207360 (by decide +kernel) (by decide +kernel)
  have h223744 := conjugate_mod_tail N hn ht [9, 11, 13, 16, 17] [9, 11, 13, 14, 16, 17] [18, 20] 5 17
    h207360 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 16, 17] [9, 11, 13, 16, 17] [14] [19, 20] 30
    h223744 h207360 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_108 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 108) ∈ N) : generator 16 ∈ N := by
  have h221184 : wordValue [13, 14, 16, 17] ∈ N := hx
  have h253952 := conjugate_mod_tail N hn ht [13, 14, 16, 17] [13, 14, 15, 16, 17] [] 1 15
    h221184 (by decide +kernel) (by decide +kernel)
  have h32768 := product_mod_tail N ht [13, 14, 15, 16, 17] [13, 14, 16, 17] [15] [20] 18
    h253952 h221184 (by decide +kernel) (by decide +kernel)
  have h98304 := conjugate_mod_tail N hn ht [15] [15, 16] [18, 19, 20] 0 4
    h32768 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 16] [15] [16] [] 2
    h98304 h32768 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_109 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 109) ∈ N) : generator 16 ∈ N := by
  have h221696 : wordValue [9, 13, 14, 16, 17] ∈ N := hx
  have h156160 := conjugate_mod_tail N hn ht [9, 13, 14, 16, 17] [9, 13, 14, 17] [18, 19] 2 22
    h221696 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 17] [9, 13, 14, 16, 17] [16] [19, 20] 22
    h156160 h221696 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_110 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 110) ∈ N) : generator 16 ∈ N := by
  have h223232 : wordValue [11, 13, 14, 16, 17] ∈ N := hx
  have h26624 := conjugate_mod_tail N hn ht [11, 13, 14, 16, 17] [11, 13, 14] [18, 19] 0 26
    h223232 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [11, 13, 14] [11, 13, 14, 16, 17] [16, 17] [20] 9
    h26624 h223232 (by decide +kernel) (by decide +kernel)
  have h92160 := conjugate_mod_tail N hn ht [11, 13, 14, 16, 17] [11, 13, 14, 16] [18, 19, 20] 2 28
    h223232 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [11, 13, 14, 16] [11, 13, 14, 16, 17] [17] [20] 14
    h92160 h223232 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_111 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 111) ∈ N) : generator 16 ∈ N := by
  have h223744 : wordValue [9, 11, 13, 14, 16, 17] ∈ N := hx
  have h141824 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 16, 17] [9, 11, 13, 17] [18] 0 34
    h223744 (by decide +kernel) (by decide +kernel)
  have h81920 := product_mod_tail N ht [9, 11, 13, 17] [9, 11, 13, 14, 16, 17] [14, 16] [19] 18
    h141824 h223744 (by decide +kernel) (by decide +kernel)
  have h207360 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 16, 17] [9, 11, 13, 16, 17] [18] 5 20
    h223744 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 16, 17] [9, 11, 13, 14, 16, 17] [14] [19] 24
    h207360 h223744 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14] [14, 16] [16] [] 1
    h16384 h81920 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_112 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 112) ∈ N) : generator 16 ∈ N := by
  have h229376 : wordValue [15, 16, 17] ∈ N := hx
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_113 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 113) ∈ N) : generator 16 ∈ N := by
  have h229888 : wordValue [9, 15, 16, 17] ∈ N := hx
  have h49664 := conjugate_mod_tail N hn ht [9, 15, 16, 17] [9, 14, 15] [18] 0 30
    h229888 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 14, 15] [9, 15, 16, 17] [14, 16, 17] [] 4
    h49664 h229888 (by decide +kernel) (by decide +kernel)
  have h98816 := conjugate_mod_tail N hn ht [9, 15, 16, 17] [9, 15, 16] [18] 2 12
    h229888 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 15, 16] [9, 15, 16, 17] [17] [] 6
    h98816 h229888 (by decide +kernel) (by decide +kernel)
  have h246272 := conjugate_mod_tail N hn ht [9, 15, 16, 17] [9, 14, 15, 16, 17] [18, 20] 5 11
    h229888 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 14, 15, 16, 17] [9, 15, 16, 17] [14] [] 11
    h246272 h229888 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_114 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 114) ∈ N) : generator 16 ∈ N := by
  have h231424 : wordValue [11, 15, 16, 17] ∈ N := hx
  have h165888 := conjugate_mod_tail N hn ht [11, 15, 16, 17] [11, 15, 17] [18, 19] 0 22
    h231424 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 15, 17] [11, 15, 16, 17] [16] [20] 11
    h165888 h231424 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_115 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 115) ∈ N) : generator 16 ∈ N := by
  have h231936 : wordValue [9, 11, 15, 16, 17] ∈ N := hx
  have h35328 := conjugate_mod_tail N hn ht [9, 11, 15, 16, 17] [9, 11, 15] [18, 20] 2 21
    h231936 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 11, 15] [9, 11, 15, 16, 17] [16, 17] [20] 9
    h35328 h231936 (by decide +kernel) (by decide +kernel)
  have h100864 := conjugate_mod_tail N hn ht [9, 11, 15, 16, 17] [9, 11, 15, 16] [18] 4 15
    h231936 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [9, 11, 15, 16] [9, 11, 15, 16, 17] [17] [20] 14
    h100864 h231936 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_116 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 116) ∈ N) : generator 16 ∈ N := by
  have h237568 : wordValue [13, 15, 16, 17] ∈ N := hx
  have h172032 := conjugate_mod_tail N hn ht [13, 15, 16, 17] [13, 15, 17] [19] 2 15
    h237568 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [13, 15, 17] [13, 15, 16, 17] [16] [] 7
    h172032 h237568 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_117 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 117) ∈ N) : generator 16 ∈ N := by
  have h238080 : wordValue [9, 13, 15, 16, 17] ∈ N := hx
  have h254464 := conjugate_mod_tail N hn ht [9, 13, 15, 16, 17] [9, 13, 14, 15, 16, 17] [19] 0 41
    h238080 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 13, 14, 15, 16, 17] [9, 13, 15, 16, 17] [14] [19, 20] 32
    h254464 h238080 (by decide +kernel) (by decide +kernel)
  have h41472 := conjugate_mod_tail N hn ht [9, 13, 15, 16, 17] [9, 13, 15] [19] 2 21
    h238080 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [9, 13, 15] [9, 13, 15, 16, 17] [16, 17] [19] 11
    h41472 h238080 (by decide +kernel) (by decide +kernel)
  have h147456 := conjugate_mod_tail N hn ht [14] [14, 17] [] 2 4
    h16384 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 17] [14] [17] [] 2
    h147456 h16384 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_118 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 118) ∈ N) : generator 16 ∈ N := by
  have h239616 : wordValue [11, 13, 15, 16, 17] ∈ N := hx
  have h26624 := conjugate_mod_tail N hn ht [11, 13, 15, 16, 17] [11, 13, 14] [] 1 38
    h239616 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13, 14] [11, 13, 15, 16, 17] [14, 15, 16, 17] [20] 8
    h26624 h239616 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_119 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 119) ∈ N) : generator 16 ∈ N := by
  have h240128 : wordValue [9, 11, 13, 15, 16, 17] ∈ N := hx
  have h256512 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 16, 17] [9, 11, 13, 14, 15, 16, 17] [19, 20] 0 46
    h240128 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 14, 15, 16, 17] [9, 11, 13, 15, 16, 17] [14] [19] 42
    h256512 h240128 (by decide +kernel) (by decide +kernel)
  have h27136 := conjugate_mod_tail N hn ht [9, 11, 13, 15, 16, 17] [9, 11, 13, 14] [19, 20] 1 44
    h240128 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13, 14] [9, 11, 13, 15, 16, 17] [14, 15, 16, 17] [19, 20] 19
    h27136 h240128 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_120 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 120) ∈ N) : generator 16 ∈ N := by
  have h245760 : wordValue [14, 15, 16, 17] ∈ N := hx
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_121 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 121) ∈ N) : generator 16 ∈ N := by
  have h246272 : wordValue [9, 14, 15, 16, 17] ∈ N := hx
  have h33280 := conjugate_mod_tail N hn ht [9, 14, 15, 16, 17] [9, 15] [18] 0 27
    h246272 (by decide +kernel) (by decide +kernel)
  have h212992 := product_mod_tail N ht [9, 15] [9, 14, 15, 16, 17] [14, 16, 17] [] 4
    h33280 h246272 (by decide +kernel) (by decide +kernel)
  have h229888 := conjugate_mod_tail N hn ht [9, 14, 15, 16, 17] [9, 15, 16, 17] [18] 5 13
    h246272 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 15, 16, 17] [9, 14, 15, 16, 17] [14] [] 13
    h229888 h246272 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [14] [14, 16, 17] [16, 17] [] 1
    h16384 h212992 (by decide +kernel) (by decide +kernel)
  have h81920 := conjugate_mod_tail N hn ht [14, 16, 17] [14, 16] [] 2 8
    h212992 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [14, 16] [14, 16, 17] [17] [] 3
    h81920 h212992 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_122 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 122) ∈ N) : generator 16 ∈ N := by
  have h247808 : wordValue [11, 14, 15, 16, 17] ∈ N := hx
  have h182272 := conjugate_mod_tail N hn ht [11, 14, 15, 16, 17] [11, 14, 15, 17] [18, 19] 0 20
    h247808 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [11, 14, 15, 17] [11, 14, 15, 16, 17] [16] [20] 16
    h182272 h247808 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_123 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 123) ∈ N) : generator 16 ∈ N := by
  have h248320 : wordValue [9, 11, 14, 15, 16, 17] ∈ N := hx
  have h182784 := conjugate_mod_tail N hn ht [9, 11, 14, 15, 16, 17] [9, 11, 14, 15, 17] [18, 20] 2 24
    h248320 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 11, 14, 15, 17] [9, 11, 14, 15, 16, 17] [16] [20] 21
    h182784 h248320 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_124 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 124) ∈ N) : generator 16 ∈ N := by
  have h253952 : wordValue [13, 14, 15, 16, 17] ∈ N := hx
  have h122880 := conjugate_mod_tail N hn ht [13, 14, 15, 16, 17] [13, 14, 15, 16] [] 0 34
    h253952 (by decide +kernel) (by decide +kernel)
  have h131072 := product_mod_tail N ht [13, 14, 15, 16] [13, 14, 15, 16, 17] [17] [20] 16
    h122880 h253952 (by decide +kernel) (by decide +kernel)
  have h57344 := conjugate_mod_tail N hn ht [13, 14, 15, 16, 17] [13, 14, 15] [19] 2 24
    h253952 (by decide +kernel) (by decide +kernel)
  have h196608 := product_mod_tail N ht [13, 14, 15] [13, 14, 15, 16, 17] [16, 17] [20] 11
    h57344 h253952 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [16, 17] [17] [16] [] 1
    h196608 h131072 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_125 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 125) ∈ N) : generator 16 ∈ N := by
  have h254464 : wordValue [9, 13, 14, 15, 16, 17] ∈ N := hx
  have h188928 := conjugate_mod_tail N hn ht [9, 13, 14, 15, 16, 17] [9, 13, 14, 15, 17] [19] 2 26
    h254464 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [9, 13, 14, 15, 17] [9, 13, 14, 15, 16, 17] [16] [19, 20] 31
    h188928 h254464 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_126 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 126) ∈ N) : generator 16 ∈ N := by
  have h256000 : wordValue [11, 13, 14, 15, 16, 17] ∈ N := hx
  have h10240 := conjugate_mod_tail N hn ht [11, 13, 14, 15, 16, 17] [11, 13] [18, 19] 1 41
    h256000 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [11, 13] [11, 13, 14, 15, 16, 17] [14, 15, 16, 17] [] 3
    h10240 h256000 (by decide +kernel) (by decide +kernel)
  have h180224 := conjugate_mod_tail N hn ht [14, 15, 16, 17] [14, 15, 17] [18, 19, 20] 0 12
    h245760 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [14, 15, 17] [14, 15, 16, 17] [16] [] 7
    h180224 h245760 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

theorem rep_seed_127 (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (hx : wordValue (repWord 127) ∈ N) : generator 16 ∈ N := by
  have h256512 : wordValue [9, 11, 13, 14, 15, 16, 17] ∈ N := hx
  have h240128 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 16, 17] [9, 11, 13, 15, 16, 17] [19, 20] 0 44
    h256512 (by decide +kernel) (by decide +kernel)
  have h16384 := product_mod_tail N ht [9, 11, 13, 15, 16, 17] [9, 11, 13, 14, 15, 16, 17] [14] [19, 20] 41
    h240128 h256512 (by decide +kernel) (by decide +kernel)
  have h10752 := conjugate_mod_tail N hn ht [9, 11, 13, 14, 15, 16, 17] [9, 11, 13] [18, 20] 1 57
    h256512 (by decide +kernel) (by decide +kernel)
  have h245760 := product_mod_tail N ht [9, 11, 13] [9, 11, 13, 14, 15, 16, 17] [14, 15, 16, 17] [19] 12
    h10752 h256512 (by decide +kernel) (by decide +kernel)
  have h229376 := product_mod_tail N ht [14, 15, 16, 17] [14] [15, 16, 17] [] 4
    h245760 h16384 (by decide +kernel) (by decide +kernel)
  have h163840 := conjugate_mod_tail N hn ht [15, 16, 17] [15, 17] [18, 19, 20] 0 13
    h229376 (by decide +kernel) (by decide +kernel)
  have h65536 := product_mod_tail N ht [15, 17] [15, 16, 17] [16] [] 4
    h163840 h229376 (by decide +kernel) (by decide +kernel)
  simpa only [wordValue_cons, wordValue_nil, mul_one] using h65536

/-- Each representative using g13 or g15 forces g16 modulo the tail. -/
theorem rep_seed (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (n : Fin 128) (hout : n.val / 4 % 2 = 1 ∨ n.val / 16 % 2 = 1)
    (hx : wordValue (repWord n) ∈ N) : generator 16 ∈ N := by
  fin_cases n
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_4 N hn ht hx
  · exact rep_seed_5 N hn ht hx
  · exact rep_seed_6 N hn ht hx
  · exact rep_seed_7 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_12 N hn ht hx
  · exact rep_seed_13 N hn ht hx
  · exact rep_seed_14 N hn ht hx
  · exact rep_seed_15 N hn ht hx
  · exact rep_seed_16 N hn ht hx
  · exact rep_seed_17 N hn ht hx
  · exact rep_seed_18 N hn ht hx
  · exact rep_seed_19 N hn ht hx
  · exact rep_seed_20 N hn ht hx
  · exact rep_seed_21 N hn ht hx
  · exact rep_seed_22 N hn ht hx
  · exact rep_seed_23 N hn ht hx
  · exact rep_seed_24 N hn ht hx
  · exact rep_seed_25 N hn ht hx
  · exact rep_seed_26 N hn ht hx
  · exact rep_seed_27 N hn ht hx
  · exact rep_seed_28 N hn ht hx
  · exact rep_seed_29 N hn ht hx
  · exact rep_seed_30 N hn ht hx
  · exact rep_seed_31 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_36 N hn ht hx
  · exact rep_seed_37 N hn ht hx
  · exact rep_seed_38 N hn ht hx
  · exact rep_seed_39 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_44 N hn ht hx
  · exact rep_seed_45 N hn ht hx
  · exact rep_seed_46 N hn ht hx
  · exact rep_seed_47 N hn ht hx
  · exact rep_seed_48 N hn ht hx
  · exact rep_seed_49 N hn ht hx
  · exact rep_seed_50 N hn ht hx
  · exact rep_seed_51 N hn ht hx
  · exact rep_seed_52 N hn ht hx
  · exact rep_seed_53 N hn ht hx
  · exact rep_seed_54 N hn ht hx
  · exact rep_seed_55 N hn ht hx
  · exact rep_seed_56 N hn ht hx
  · exact rep_seed_57 N hn ht hx
  · exact rep_seed_58 N hn ht hx
  · exact rep_seed_59 N hn ht hx
  · exact rep_seed_60 N hn ht hx
  · exact rep_seed_61 N hn ht hx
  · exact rep_seed_62 N hn ht hx
  · exact rep_seed_63 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_68 N hn ht hx
  · exact rep_seed_69 N hn ht hx
  · exact rep_seed_70 N hn ht hx
  · exact rep_seed_71 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_76 N hn ht hx
  · exact rep_seed_77 N hn ht hx
  · exact rep_seed_78 N hn ht hx
  · exact rep_seed_79 N hn ht hx
  · exact rep_seed_80 N hn ht hx
  · exact rep_seed_81 N hn ht hx
  · exact rep_seed_82 N hn ht hx
  · exact rep_seed_83 N hn ht hx
  · exact rep_seed_84 N hn ht hx
  · exact rep_seed_85 N hn ht hx
  · exact rep_seed_86 N hn ht hx
  · exact rep_seed_87 N hn ht hx
  · exact rep_seed_88 N hn ht hx
  · exact rep_seed_89 N hn ht hx
  · exact rep_seed_90 N hn ht hx
  · exact rep_seed_91 N hn ht hx
  · exact rep_seed_92 N hn ht hx
  · exact rep_seed_93 N hn ht hx
  · exact rep_seed_94 N hn ht hx
  · exact rep_seed_95 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_100 N hn ht hx
  · exact rep_seed_101 N hn ht hx
  · exact rep_seed_102 N hn ht hx
  · exact rep_seed_103 N hn ht hx
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · norm_num at hout
  · exact rep_seed_108 N hn ht hx
  · exact rep_seed_109 N hn ht hx
  · exact rep_seed_110 N hn ht hx
  · exact rep_seed_111 N hn ht hx
  · exact rep_seed_112 N hn ht hx
  · exact rep_seed_113 N hn ht hx
  · exact rep_seed_114 N hn ht hx
  · exact rep_seed_115 N hn ht hx
  · exact rep_seed_116 N hn ht hx
  · exact rep_seed_117 N hn ht hx
  · exact rep_seed_118 N hn ht hx
  · exact rep_seed_119 N hn ht hx
  · exact rep_seed_120 N hn ht hx
  · exact rep_seed_121 N hn ht hx
  · exact rep_seed_122 N hn ht hx
  · exact rep_seed_123 N hn ht hx
  · exact rep_seed_124 N hn ht hx
  · exact rep_seed_125 N hn ht hx
  · exact rep_seed_126 N hn ht hx
  · exact rep_seed_127 N hn ht hx

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
