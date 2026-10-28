module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.KernelSection

/-!
# Realizing the Boolean kernel pattern in the original eleven-word subgroup

The eight pure directions already constructed in `KernelSection`, together with
four literal kernel words, recover g6 and the four possible prefixes on the
constrained coordinates. Inserting g6, g9, g11 and g14 gives the 64 allowed
prefixes below coordinate 16. Each insertion is a short checked collection,
with its remaining suffix removed using known kernel generators. The five
higher coordinates then follow from subgroup closure.

The resulting membership theorem is unconditional: neither the order of the
presentation nor normality of the kernel is used. In particular it discharges
exactly `KernelPatternMembership` in the pointwise exclusion interface, keeping
the original `Candidates.kernelWords` and ascending-word convention.

Source: the literal presentation and kernel provenance in
`SylowNormalEights/source/README.md` and `OutsideKernelOrders/source/README.md`;
Aschbacher–Smith A.3.12, pp.47–48. The adjacent `KernelMembership/source`
directory records the small certificate generation.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles
open PointwiseCalculation

namespace KernelMembershipCalculation

private theorem sectionWord_mem (w : List (Fin 21))
    (h : ∀ i ∈ w, i ∈ ([9,11,14,16,17,18,19,20] : List (Fin 21))) :
    wordValue w ∈ abstractKernel := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact section_generators_mem_kernel i (h i hi)

private theorem six_mem : generator 6 ∈ abstractKernel := by
  have hk := kernel_word_mem [6,11,14,16,18,20] (by decide +kernel)
  change generator 6 * wordValue [11,14,16,18,20] ∈ abstractKernel at hk
  exact (abstractKernel.mul_mem_cancel_right
    (sectionWord_mem [11,14,16,18,20] (by decide +kernel))).mp hk

private theorem freeWord_mem (w : List (Fin 21))
    (h : ∀ i ∈ w, i ∈ ([6,9,11,14,16,17,18,19,20] : List (Fin 21))) :
    wordValue w ∈ abstractKernel := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rcases List.mem_cons.mp (h i hi) with rfl | hi
  · exact six_mem
  · exact section_generators_mem_kernel i hi

private theorem product_strip (a b c t : List (Fin 21)) (fuel : ℕ)
    (ha : wordValue a ∈ abstractKernel) (hb : wordValue b ∈ abstractKernel)
    (ht : ∀ i ∈ t, i ∈ ([9,11,14,16,17,18,19,20] : List (Fin 21)))
    (hc : collect fuel (a ++ b) = c ++ t) : wordValue c ∈ abstractKernel := by
  have hm := abstractKernel.mul_mem ha hb
  rw [← wordValue_append, wordValue_eq_of_collect fuel _ _ hc, wordValue_append] at hm
  exact (abstractKernel.mul_mem_cancel_right (sectionWord_mem t ht)).mp hm

/-- The six free bits below coordinate 16, in the original ascending order. -/
private def prefixWord (a c d e f h : Bool) : List (Fin 21) :=
  (if a then [0] else []) ++ (if c then [3] else []) ++
  (if a then [5] else []) ++ (if d then [6] else []) ++
  (if a then [8] else []) ++ (if e then [9] else []) ++
  (if a then [10] else []) ++ (if f then [11] else []) ++
  (if a ^^ c then [12] else []) ++ (if a ^^ c then [13] else []) ++
  (if h then [14] else []) ++
  (if a ^^ c then [15] else [])

private theorem prefix_mem (a c d e f h : Bool) :
    wordValue (prefixWord a c d e f h) ∈ abstractKernel := by
  have h0 : wordValue [] ∈ abstractKernel := abstractKernel.one_mem
  have h1 := product_strip [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19] [11]
    [0, 5, 8, 10, 12, 13, 15] [16, 17, 19, 20] 10
    (kernel_word_mem _ (by decide +kernel)) (freeWord_mem _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  have h2 := product_strip [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20] [6, 11]
    [3, 12, 13, 15] [17, 19, 20] 36
    (kernel_word_mem _ (by decide +kernel)) (freeWord_mem _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  have h3 := product_strip [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20] [6]
    [0, 3, 5, 8, 10] [14, 16, 17, 19, 20] 18
    (kernel_word_mem _ (by decide +kernel)) (freeWord_mem _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  have h4 := product_strip [] [6]
    [6] [] 0
    h0 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h5 := product_strip [0, 5, 8, 10, 12, 13, 15] [6]
    [0, 5, 6, 8, 10, 12, 13, 15] [20] 21
    h1 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h6 := product_strip [3, 12, 13, 15] [6]
    [3, 6, 12, 13, 15] [16, 18, 20] 12
    h2 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h7 := product_strip [0, 3, 5, 8, 10] [6]
    [0, 3, 5, 6, 8, 10] [16, 18] 8
    h3 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h8 := product_strip [] [9]
    [9] [] 0
    h0 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h9 := product_strip [0, 5, 8, 10, 12, 13, 15] [9]
    [0, 5, 8, 9, 10, 12, 13, 15] [18, 19, 20] 16
    h1 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h10 := product_strip [3, 12, 13, 15] [9]
    [3, 9, 12, 13, 15] [18] 7
    h2 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h11 := product_strip [0, 3, 5, 8, 10] [9]
    [0, 3, 5, 8, 9, 10] [19, 20] 1
    h3 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h12 := product_strip [9] [6]
    [6, 9] [] 1
    h8 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h13 := product_strip [0, 5, 8, 9, 10, 12, 13, 15] [6]
    [0, 5, 6, 8, 9, 10, 12, 13, 15] [20] 25
    h9 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h14 := product_strip [3, 9, 12, 13, 15] [6]
    [3, 6, 9, 12, 13, 15] [16, 18, 20] 13
    h10 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h15 := product_strip [0, 3, 5, 8, 9, 10] [6]
    [0, 3, 5, 6, 8, 9, 10] [16, 18] 12
    h11 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h16 := product_strip [] [11]
    [11] [] 0
    h0 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h17 := product_strip [0, 5, 8, 10, 12, 13, 15] [11]
    [0, 5, 8, 10, 11, 12, 13, 15] [20] 3
    h1 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h18 := product_strip [3, 12, 13, 15] [11]
    [3, 11, 12, 13, 15] [20] 3
    h2 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h19 := product_strip [0, 3, 5, 8, 10] [11]
    [0, 3, 5, 8, 10, 11] [] 0
    h3 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h20 := product_strip [11] [6]
    [6, 11] [] 1
    h16 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h21 := product_strip [0, 5, 8, 10, 11, 12, 13, 15] [6]
    [0, 5, 6, 8, 10, 11, 12, 13, 15] [20] 24
    h17 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h22 := product_strip [3, 11, 12, 13, 15] [6]
    [3, 6, 11, 12, 13, 15] [16, 18, 20] 13
    h18 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h23 := product_strip [0, 3, 5, 8, 10, 11] [6]
    [0, 3, 5, 6, 8, 10, 11] [16, 18] 11
    h19 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h24 := product_strip [11] [9]
    [9, 11] [] 1
    h16 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h25 := product_strip [0, 5, 8, 10, 11, 12, 13, 15] [9]
    [0, 5, 8, 9, 10, 11, 12, 13, 15] [18, 19, 20] 19
    h17 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h26 := product_strip [3, 11, 12, 13, 15] [9]
    [3, 9, 11, 12, 13, 15] [18] 8
    h18 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h27 := product_strip [0, 3, 5, 8, 10, 11] [9]
    [0, 3, 5, 8, 9, 10, 11] [19, 20] 4
    h19 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h28 := product_strip [9, 11] [6]
    [6, 9, 11] [] 2
    h24 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h29 := product_strip [0, 5, 8, 9, 10, 11, 12, 13, 15] [6]
    [0, 5, 6, 8, 9, 10, 11, 12, 13, 15] [20] 28
    h25 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h30 := product_strip [3, 9, 11, 12, 13, 15] [6]
    [3, 6, 9, 11, 12, 13, 15] [16, 18, 20] 14
    h26 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h31 := product_strip [0, 3, 5, 8, 9, 10, 11] [6]
    [0, 3, 5, 6, 8, 9, 10, 11] [16, 18] 15
    h27 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h32 := product_strip [] [14]
    [14] [] 0
    h0 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h33 := product_strip [0, 5, 8, 10, 12, 13, 15] [14]
    [0, 5, 8, 10, 12, 13, 14, 15] [] 1
    h1 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h34 := product_strip [3, 12, 13, 15] [14]
    [3, 12, 13, 14, 15] [] 1
    h2 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h35 := product_strip [0, 3, 5, 8, 10] [14]
    [0, 3, 5, 8, 10, 14] [] 0
    h3 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h36 := product_strip [14] [6]
    [6, 14] [] 1
    h32 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h37 := product_strip [0, 5, 8, 10, 12, 13, 14, 15] [6]
    [0, 5, 6, 8, 10, 12, 13, 14, 15] [20] 23
    h33 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h38 := product_strip [3, 12, 13, 14, 15] [6]
    [3, 6, 12, 13, 14, 15] [16, 18, 20] 16
    h34 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h39 := product_strip [0, 3, 5, 8, 10, 14] [6]
    [0, 3, 5, 6, 8, 10, 14] [16, 18] 11
    h35 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h40 := product_strip [14] [9]
    [9, 14] [] 1
    h32 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h41 := product_strip [0, 5, 8, 10, 12, 13, 14, 15] [9]
    [0, 5, 8, 9, 10, 12, 13, 14, 15] [18, 19, 20] 20
    h33 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h42 := product_strip [3, 12, 13, 14, 15] [9]
    [3, 9, 12, 13, 14, 15] [18] 9
    h34 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h43 := product_strip [0, 3, 5, 8, 10, 14] [9]
    [0, 3, 5, 8, 9, 10, 14] [19, 20] 4
    h35 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h44 := product_strip [9, 14] [6]
    [6, 9, 14] [] 2
    h40 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h45 := product_strip [0, 5, 8, 9, 10, 12, 13, 14, 15] [6]
    [0, 5, 6, 8, 9, 10, 12, 13, 14, 15] [20] 27
    h41 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h46 := product_strip [3, 9, 12, 13, 14, 15] [6]
    [3, 6, 9, 12, 13, 14, 15] [16, 18, 20] 17
    h42 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h47 := product_strip [0, 3, 5, 8, 9, 10, 14] [6]
    [0, 3, 5, 6, 8, 9, 10, 14] [16, 18] 15
    h43 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h48 := product_strip [14] [11]
    [11, 14] [] 1
    h32 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h49 := product_strip [0, 5, 8, 10, 12, 13, 14, 15] [11]
    [0, 5, 8, 10, 11, 12, 13, 14, 15] [20] 4
    h33 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h50 := product_strip [3, 12, 13, 14, 15] [11]
    [3, 11, 12, 13, 14, 15] [20] 4
    h34 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h51 := product_strip [0, 3, 5, 8, 10, 14] [11]
    [0, 3, 5, 8, 10, 11, 14] [] 1
    h35 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h52 := product_strip [11, 14] [6]
    [6, 11, 14] [] 2
    h48 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h53 := product_strip [0, 5, 8, 10, 11, 12, 13, 14, 15] [6]
    [0, 5, 6, 8, 10, 11, 12, 13, 14, 15] [20] 26
    h49 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h54 := product_strip [3, 11, 12, 13, 14, 15] [6]
    [3, 6, 11, 12, 13, 14, 15] [16, 18, 20] 17
    h50 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h55 := product_strip [0, 3, 5, 8, 10, 11, 14] [6]
    [0, 3, 5, 6, 8, 10, 11, 14] [16, 18] 14
    h51 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h56 := product_strip [11, 14] [9]
    [9, 11, 14] [] 2
    h48 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h57 := product_strip [0, 5, 8, 10, 11, 12, 13, 14, 15] [9]
    [0, 5, 8, 9, 10, 11, 12, 13, 14, 15] [18, 19, 20] 23
    h49 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h58 := product_strip [3, 11, 12, 13, 14, 15] [9]
    [3, 9, 11, 12, 13, 14, 15] [18] 10
    h50 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h59 := product_strip [0, 3, 5, 8, 10, 11, 14] [9]
    [0, 3, 5, 8, 9, 10, 11, 14] [19, 20] 7
    h51 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h60 := product_strip [9, 11, 14] [6]
    [6, 9, 11, 14] [] 3
    h56 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h61 := product_strip [0, 5, 8, 9, 10, 11, 12, 13, 14, 15] [6]
    [0, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15] [20] 30
    h57 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h62 := product_strip [3, 9, 11, 12, 13, 14, 15] [6]
    [3, 6, 9, 11, 12, 13, 14, 15] [16, 18, 20] 18
    h58 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  have h63 := product_strip [0, 3, 5, 8, 9, 10, 11, 14] [6]
    [0, 3, 5, 6, 8, 9, 10, 11, 14] [16, 18] 18
    h59 (freeWord_mem _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  cases a <;> cases c <;> cases d <;> cases e <;> cases f <;> cases h
  · exact h0
  · exact h32
  · exact h16
  · exact h48
  · exact h8
  · exact h40
  · exact h24
  · exact h56
  · exact h4
  · exact h36
  · exact h20
  · exact h52
  · exact h12
  · exact h44
  · exact h28
  · exact h60
  · exact h2
  · exact h34
  · exact h18
  · exact h50
  · exact h10
  · exact h42
  · exact h26
  · exact h58
  · exact h6
  · exact h38
  · exact h22
  · exact h54
  · exact h14
  · exact h46
  · exact h30
  · exact h62
  · exact h1
  · exact h33
  · exact h17
  · exact h49
  · exact h9
  · exact h41
  · exact h25
  · exact h57
  · exact h5
  · exact h37
  · exact h21
  · exact h53
  · exact h13
  · exact h45
  · exact h29
  · exact h61
  · exact h3
  · exact h35
  · exact h19
  · exact h51
  · exact h11
  · exact h43
  · exact h27
  · exact h59
  · exact h7
  · exact h39
  · exact h23
  · exact h55
  · exact h15
  · exact h47
  · exact h31
  · exact h63

private theorem value_ite (b : Bool) (w : List (Fin 21)) :
    wordValue (if b then w else []) = if b then wordValue w else 1 := by
  cases b <;> rfl

private theorem bool_ite_mem (b : Bool) (i : Fin 21)
    (hi : i ∈ ([9,11,14,16,17,18,19,20] : List (Fin 21))) :
    (if b then generator i else 1) ∈ abstractKernel := by
  cases b
  · exact abstractKernel.one_mem
  · exact section_generators_mem_kernel i hi

private theorem pattern_mem (b : Boolean.Bits) (h : Boolean.KernelPattern b) :
    Symbolic.boolValue b ∈ abstractKernel := by
  rcases h with ⟨h1,h2,h4,h7,h5,h8,h10,h12,h13,h15⟩
  have xor_two : ∀ a c : Bool, (a ^^ c) = false → c = a := by decide
  have xor_three : ∀ a c d : Bool, (a ^^ (c ^^ d)) = false → d = (a ^^ c) := by decide
  have e5 := xor_two _ _ h5
  have e8 := xor_two _ _ h8
  have e10 := xor_two _ _ h10
  have e12 := xor_three _ _ _ h12
  have e13 := xor_three _ _ _ h13
  have e15 := xor_three _ _ _ h15
  have hm := abstractKernel.mul_mem (prefix_mem (b 0) (b 3) (b 6) (b 9) (b 11) (b 14))
    (abstractKernel.mul_mem (bool_ite_mem (b 16) 16 (by decide))
      (abstractKernel.mul_mem (bool_ite_mem (b 17) 17 (by decide))
        (abstractKernel.mul_mem (bool_ite_mem (b 18) 18 (by decide))
          (abstractKernel.mul_mem (bool_ite_mem (b 19) 19 (by decide))
            (bool_ite_mem (b 20) 20 (by decide))))))
  simp only [Symbolic.boolValue, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one]
  change (if b 0 then generator 0 else 1) *
    ((if b 1 then generator 1 else 1) *
    ((if b 2 then generator 2 else 1) *
    ((if b 3 then generator 3 else 1) *
    ((if b 4 then generator 4 else 1) *
    ((if b 5 then generator 5 else 1) *
    ((if b 6 then generator 6 else 1) *
    ((if b 7 then generator 7 else 1) *
    ((if b 8 then generator 8 else 1) *
    ((if b 9 then generator 9 else 1) *
    ((if b 10 then generator 10 else 1) *
    ((if b 11 then generator 11 else 1) *
    ((if b 12 then generator 12 else 1) *
    ((if b 13 then generator 13 else 1) *
    ((if b 14 then generator 14 else 1) *
    ((if b 15 then generator 15 else 1) *
    ((if b 16 then generator 16 else 1) *
    ((if b 17 then generator 17 else 1) *
    ((if b 18 then generator 18 else 1) *
    ((if b 19 then generator 19 else 1) *
    ((if b 20 then generator 20 else 1))))))))))))))))))))) ∈ abstractKernel
  simpa only [prefixWord, wordValue_append, value_ite, wordValue_cons,
    wordValue_nil, h1, h2, h4, h7, e5, e8, e10, e12, e13, e15,
    Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, mul_assoc] using hm

end KernelMembershipCalculation

/-- Every ascending word with the stated pattern belongs to the original
subgroup generated by the eleven literal kernel words. No order premise is needed. -/
theorem kernelPatternMembership : KernelPatternMembership :=
  KernelMembershipCalculation.pattern_mem

/-- The producer in the cardinality interface used by the pointwise assembly. -/
theorem kernelPatternMembership_of_card (_hcard : Nat.card Carrier = 2 ^ 21) :
    KernelPatternMembership := kernelPatternMembership

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
