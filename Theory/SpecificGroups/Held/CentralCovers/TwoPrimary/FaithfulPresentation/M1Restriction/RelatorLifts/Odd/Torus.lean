module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Odd.Symmetry
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# A commuting seventh-order word in the Held source presentation

Let `u = a₀*a₆*a₀*a₁*a₀`, where `aᵢ = y⁻ⁱ*x*yⁱ`. The source commutator
relation identifies all seven shifted five-letter words, so `u` commutes
with `y`. This module proves `u⁷ = 1` using the original source relations,
including the order-17 relation; no marked M₁ relator is assumed.

The private equalities check a dependency slice of an untrusted word search.
Each step is a split of a cyclic source word, an overlap, an inclusion, or a
replacement by an earlier checked equality. Alias nodes are shared, leaving
1324 equality nodes. The only long source seed is a seventh power of the
17-letter source word; its value is checked using a structural repeated-block
lemma. This intermediate result does not prove the remaining marked entry 7.

Source: John Bray's `Held/Model/Source/HeG1-P1.M`; the shifted five-letter
identities are proved in `Odd.Symmetry`. Multiplication order is unchanged.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.OddTorus

/-- The common value of the seven shifted five-letter source words. -/
def u : Presentation := value [0, 6, 0, 1, 0]

private theorem value_mod (w : List ℤ) : value (w.map (· % 7)) = value w := by
  unfold value
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro n hn
  exact (conjugate_mod_seven n).symm

/-- Shift invariance gives actual commutation with the source generator. -/
theorem u_commute_y : Commute u y := by
  have hs := five_letter_shift 1
  have hm := value_mod (([0, 6, 0, 1, 0] : List ℤ).map (· + 1))
  change value (([0, 6, 0, 1, 0] : List ℤ).map (fun n => (n + 1) % 7)) = u at hs
  rw [List.map_map] at hm
  have hs' := hm.symm.trans hs
  rw [value_shift] at hs'
  change y⁻¹ * u * y = u at hs'
  change u * y = y * u
  calc
    u * y = y * (y⁻¹ * u * y) := by group
    _ = y * u := congrArg (y * ·) hs'

private def symbol : Fin 15 → Presentation
  | 0 => u
  | 1 => u⁻¹
  | 2 => conjugate 0
  | 3 => conjugate 1
  | 4 => conjugate 2
  | 5 => conjugate 3
  | 6 => conjugate 4
  | 7 => conjugate 5
  | 8 => conjugate 6
  | 9 => y
  | 10 => y^2
  | 11 => y^3
  | 12 => y^4
  | 13 => y^5
  | 14 => y^6

private def invSymbol : Fin 15 → Fin 15
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 14
  | 10 => 13
  | 11 => 12
  | 12 => 11
  | 13 => 10
  | 14 => 9

private theorem symbol_inv (i : Fin 15) : symbol (invSymbol i) = (symbol i)⁻¹ := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  have ha (n : ℤ) : (conjugate n)⁻¹ = conjugate n :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using conjugate_sq n)
  fin_cases i
  all_goals simp only [invSymbol, symbol, inv_inv, ha]
  all_goals apply eq_inv_of_mul_eq_one_left
  all_goals convert hy using 1; group

private def V (w : List (Fin 15)) : Presentation := (w.map symbol).prod

private def inverse (w : List (Fin 15)) := w.reverse.map invSymbol

private theorem V_append (a b : List (Fin 15)) : V (a ++ b) = V a * V b := by
  simp only [V, List.map_append, List.prod_append]

private theorem V_inverse (w : List (Fin 15)) : V (inverse w) = (V w)⁻¹ := by
  induction w with
  | nil => simp [V, inverse]
  | cons a w ih =>
    simp only [inverse, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, V_append] at *
    rw [ih]
    simp [V, symbol_inv]

private theorem relation_split (w : List (Fin 15)) (hw : V w = 1)
    (flip : Bool) (offset : Nat) (l r : List (Fin 15))
    (hs : (if flip then inverse w else w).rotate offset = l ++ inverse r) :
    V l = V r := by
  have h : V (if flip then inverse w else w) = 1 := by
    cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte, V_inverse, hw, inv_one]
  have he : V ((if flip then inverse w else w).rotate offset) = 1 := by
    simpa only [V, List.map_rotate] using List.prod_rotate_eq_one_of_prod_eq_one h offset
  rw [hs, V_append, V_inverse, mul_inv_eq_one] at he
  exact he

private theorem equation_loop {l r : List (Fin 15)} (h : V l = V r) :
    V (l ++ inverse r) = 1 := by
  rw [V_append, V_inverse, h, mul_inv_cancel]

private theorem in_context {l r : List (Fin 15)} (h : V l = V r)
    (pre post : List (Fin 15)) : V (pre ++ l ++ post) = V (pre ++ r ++ post) := by
  simp only [V_append, h]

private theorem overlap {l₁ r₁ l₂ r₂ : List (Fin 15)}
    (h₁ : V l₁ = V r₁) (h₂ : V l₂ = V r₂)
    (pre post : List (Fin 15)) (hc : l₁ ++ post = pre ++ l₂) :
    V (r₁ ++ post) = V (pre ++ r₂) := by
  rw [V_append, ← h₁, ← V_append, hc, V_append, h₂, V_append]

private theorem inclusion {l₁ r₁ l₂ r₂ : List (Fin 15)}
    (h₁ : V l₁ = V r₁) (h₂ : V l₂ = V r₂)
    (pre post : List (Fin 15)) (hc : l₁ = pre ++ l₂ ++ post) :
    V r₁ = V (pre ++ r₂ ++ post) := by
  rw [← h₁, hc]
  exact in_context h₂ pre post

private theorem y_mul_conjugate (i k : ℤ) :
    y^k * conjugate i = conjugate (i-k) * y^k := by
  simp only [conjugate, zpow_sub]
  group

private theorem loop0 : V [2, 3, 4, 3, 4, 5, 4, 3, 4, 3] = 1 := by
  have hs := source_value_shift 0 0
  rw [← value_mod] at hs
  exact hs

private theorem loop1 : V [3, 4, 5, 4, 5, 6, 5, 4, 5, 4] = 1 := by
  have hs := source_value_shift 0 1
  rw [← value_mod] at hs
  exact hs

private theorem loop2 : V [4, 5, 6, 5, 6, 7, 6, 5, 6, 5] = 1 := by
  have hs := source_value_shift 0 2
  rw [← value_mod] at hs
  exact hs

private theorem loop3 : V [5, 6, 7, 6, 7, 8, 7, 6, 7, 6] = 1 := by
  have hs := source_value_shift 0 3
  rw [← value_mod] at hs
  exact hs

private theorem loop4 : V [6, 7, 8, 7, 8, 2, 8, 7, 8, 7] = 1 := by
  have hs := source_value_shift 0 4
  rw [← value_mod] at hs
  exact hs

private theorem loop5 : V [7, 8, 2, 8, 2, 3, 2, 8, 2, 8] = 1 := by
  have hs := source_value_shift 0 5
  rw [← value_mod] at hs
  exact hs

private theorem loop6 : V [8, 2, 3, 2, 3, 4, 3, 2, 3, 2] = 1 := by
  have hs := source_value_shift 0 6
  rw [← value_mod] at hs
  exact hs

private theorem loop14 : V [2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3] = 1 := by
  have hs := source_value_shift 2 0
  rw [← value_mod] at hs
  exact hs

private theorem loop15 : V [3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4] = 1 := by
  have hs := source_value_shift 2 1
  rw [← value_mod] at hs
  exact hs

private theorem loop16 : V [4, 5, 4, 5, 4, 5, 4, 5, 4, 5, 4, 5] = 1 := by
  have hs := source_value_shift 2 2
  rw [← value_mod] at hs
  exact hs

private theorem loop17 : V [5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6] = 1 := by
  have hs := source_value_shift 2 3
  rw [← value_mod] at hs
  exact hs

private theorem loop18 : V [6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7] = 1 := by
  have hs := source_value_shift 2 4
  rw [← value_mod] at hs
  exact hs

private theorem loop19 : V [7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8] = 1 := by
  have hs := source_value_shift 2 5
  rw [← value_mod] at hs
  exact hs

private theorem loop20 : V [8, 2, 8, 2, 8, 2, 8, 2, 8, 2, 8, 2] = 1 := by
  have hs := source_value_shift 2 6
  rw [← value_mod] at hs
  exact hs

private theorem loop21 : V [2, 8, 7, 6, 5, 3, 6, 5, 4, 5, 2, 4] = 1 := by
  have hs := source_value_shift 3 0
  rw [← value_mod] at hs
  exact hs

private theorem loop22 : V [3, 2, 8, 7, 6, 4, 7, 6, 5, 6, 3, 5] = 1 := by
  have hs := source_value_shift 3 1
  rw [← value_mod] at hs
  exact hs

private theorem loop23 : V [4, 3, 2, 8, 7, 5, 8, 7, 6, 7, 4, 6] = 1 := by
  have hs := source_value_shift 3 2
  rw [← value_mod] at hs
  exact hs

private theorem loop24 : V [5, 4, 3, 2, 8, 6, 2, 8, 7, 8, 5, 7] = 1 := by
  have hs := source_value_shift 3 3
  rw [← value_mod] at hs
  exact hs

private theorem loop25 : V [6, 5, 4, 3, 2, 7, 3, 2, 8, 2, 6, 8] = 1 := by
  have hs := source_value_shift 3 4
  rw [← value_mod] at hs
  exact hs

private theorem loop26 : V [7, 6, 5, 4, 3, 8, 4, 3, 2, 3, 7, 2] = 1 := by
  have hs := source_value_shift 3 5
  rw [← value_mod] at hs
  exact hs

private theorem loop27 : V [8, 7, 6, 5, 4, 2, 5, 4, 3, 4, 8, 3] = 1 := by
  have hs := source_value_shift 3 6
  rw [← value_mod] at hs
  exact hs

private theorem loop56 : V [2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 11] = 1 := by
  change V ([2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7] ++ [11]) = 1
  rw [V_append]
  change value [0, 6, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 6, 5] * y^3 = 1
  have hs := seventeen_value
  rw [← value_mod] at hs
  change value [0, 6, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 6, 5] = (y^3)⁻¹ at hs
  rw [hs, inv_mul_cancel]

private theorem loop63 : V [2, 8, 2, 3, 2, 1] = 1 := by
  change V ([2, 8, 2, 3, 2] ++ [1]) = 1
  rw [V_append]
  change value [0, 6, 0, 1, 0] * u⁻¹ = 1
  rw [show value [0, 6, 0, 1, 0] = u from five_letter_shift 0]
  exact mul_inv_cancel _

private theorem loop64 : V [3, 2, 3, 4, 3, 1] = 1 := by
  change V ([3, 2, 3, 4, 3] ++ [1]) = 1
  rw [V_append]
  change value [1, 0, 1, 2, 1] * u⁻¹ = 1
  rw [show value [1, 0, 1, 2, 1] = u from five_letter_shift 1]
  exact mul_inv_cancel _

private theorem loop65 : V [4, 3, 4, 5, 4, 1] = 1 := by
  change V ([4, 3, 4, 5, 4] ++ [1]) = 1
  rw [V_append]
  change value [2, 1, 2, 3, 2] * u⁻¹ = 1
  rw [show value [2, 1, 2, 3, 2] = u from five_letter_shift 2]
  exact mul_inv_cancel _

private theorem loop66 : V [5, 4, 5, 6, 5, 1] = 1 := by
  change V ([5, 4, 5, 6, 5] ++ [1]) = 1
  rw [V_append]
  change value [3, 2, 3, 4, 3] * u⁻¹ = 1
  rw [show value [3, 2, 3, 4, 3] = u from five_letter_shift 3]
  exact mul_inv_cancel _

private theorem loop67 : V [6, 5, 6, 7, 6, 1] = 1 := by
  change V ([6, 5, 6, 7, 6] ++ [1]) = 1
  rw [V_append]
  change value [4, 3, 4, 5, 4] * u⁻¹ = 1
  rw [show value [4, 3, 4, 5, 4] = u from five_letter_shift 4]
  exact mul_inv_cancel _

private theorem loop68 : V [7, 6, 7, 8, 7, 1] = 1 := by
  change V ([7, 6, 7, 8, 7] ++ [1]) = 1
  rw [V_append]
  change value [5, 4, 5, 6, 5] * u⁻¹ = 1
  rw [show value [5, 4, 5, 6, 5] = u from five_letter_shift 5]
  exact mul_inv_cancel _

private theorem loop69 : V [8, 7, 8, 2, 8, 1] = 1 := by
  change V ([8, 7, 8, 2, 8] ++ [1]) = 1
  rw [V_append]
  change value [6, 5, 6, 0, 6] * u⁻¹ = 1
  rw [show value [6, 5, 6, 0, 6] = u from five_letter_shift 6]
  exact mul_inv_cancel _

private theorem seed0 : V [0, 1] = V [] := by
  simp [V, symbol]

private theorem seed1 : V [1, 0] = V [] := by
  simp [V, symbol]

private theorem seed2 : V [2, 2] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 0

private theorem seed3 : V [3, 3] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 1

private theorem seed4 : V [4, 4] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 2

private theorem seed5 : V [5, 5] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 3

private theorem seed6 : V [6, 6] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 4

private theorem seed7 : V [7, 7] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 5

private theorem seed8 : V [8, 8] = V [] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_two] using conjugate_sq 6

private theorem seed11 : V [9, 11] = V [12] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^1 * y^3 = y^4
  exact (pow_add y 1 3).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed12 : V [9, 12] = V [13] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^1 * y^4 = y^5
  exact (pow_add y 1 4).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed21 : V [11, 9] = V [12] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^3 * y^1 = y^4
  exact (pow_add y 3 1).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed23 : V [11, 11] = V [14] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^3 * y^3 = y^6
  exact (pow_add y 3 3).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed24 : V [11, 12] = V [] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^3 * y^4 = y^0
  exact (pow_add y 3 4).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed25 : V [11, 13] = V [9] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^3 * y^5 = y^1
  exact (pow_add y 3 5).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed26 : V [11, 14] = V [10] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^3 * y^6 = y^2
  exact (pow_add y 3 6).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed28 : V [12, 10] = V [14] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^4 * y^2 = y^6
  exact (pow_add y 4 2).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed29 : V [12, 11] = V [] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^4 * y^3 = y^0
  exact (pow_add y 4 3).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed30 : V [12, 12] = V [9] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^4 * y^4 = y^1
  exact (pow_add y 4 4).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed32 : V [12, 14] = V [11] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^4 * y^6 = y^3
  exact (pow_add y 4 6).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed39 : V [14, 9] = V [] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^6 * y^1 = y^0
  exact (pow_add y 6 1).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed42 : V [14, 12] = V [11] := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  change y^6 * y^4 = y^3
  exact (pow_add y 6 4).symm.trans (pow_eq_pow_mod _ hy)

private theorem seed45 : V [9, 2] = V [8, 9] := by
  change y^1 * conjugate 0 = conjugate 6 * y^1
  have hs := y_mul_conjugate 0 1
  rw [conjugate_mod_seven (0 - 1)] at hs
  exact hs

private theorem seed46 : V [10, 2] = V [7, 10] := by
  change y^2 * conjugate 0 = conjugate 5 * y^2
  have hs := y_mul_conjugate 0 2
  rw [conjugate_mod_seven (0 - 2)] at hs
  exact hs

private theorem seed47 : V [11, 2] = V [6, 11] := by
  change y^3 * conjugate 0 = conjugate 4 * y^3
  have hs := y_mul_conjugate 0 3
  rw [conjugate_mod_seven (0 - 3)] at hs
  exact hs

private theorem seed48 : V [12, 2] = V [5, 12] := by
  change y^4 * conjugate 0 = conjugate 3 * y^4
  have hs := y_mul_conjugate 0 4
  rw [conjugate_mod_seven (0 - 4)] at hs
  exact hs

private theorem seed49 : V [13, 2] = V [4, 13] := by
  change y^5 * conjugate 0 = conjugate 2 * y^5
  have hs := y_mul_conjugate 0 5
  rw [conjugate_mod_seven (0 - 5)] at hs
  exact hs

private theorem seed50 : V [14, 2] = V [3, 14] := by
  change y^6 * conjugate 0 = conjugate 1 * y^6
  have hs := y_mul_conjugate 0 6
  rw [conjugate_mod_seven (0 - 6)] at hs
  exact hs

private theorem seed51 : V [9, 3] = V [2, 9] := by
  change y^1 * conjugate 1 = conjugate 0 * y^1
  have hs := y_mul_conjugate 1 1
  rw [conjugate_mod_seven (1 - 1)] at hs
  exact hs

private theorem seed52 : V [10, 3] = V [8, 10] := by
  change y^2 * conjugate 1 = conjugate 6 * y^2
  have hs := y_mul_conjugate 1 2
  rw [conjugate_mod_seven (1 - 2)] at hs
  exact hs

private theorem seed53 : V [11, 3] = V [7, 11] := by
  change y^3 * conjugate 1 = conjugate 5 * y^3
  have hs := y_mul_conjugate 1 3
  rw [conjugate_mod_seven (1 - 3)] at hs
  exact hs

private theorem seed54 : V [12, 3] = V [6, 12] := by
  change y^4 * conjugate 1 = conjugate 4 * y^4
  have hs := y_mul_conjugate 1 4
  rw [conjugate_mod_seven (1 - 4)] at hs
  exact hs

private theorem seed55 : V [13, 3] = V [5, 13] := by
  change y^5 * conjugate 1 = conjugate 3 * y^5
  have hs := y_mul_conjugate 1 5
  rw [conjugate_mod_seven (1 - 5)] at hs
  exact hs

private theorem seed56 : V [14, 3] = V [4, 14] := by
  change y^6 * conjugate 1 = conjugate 2 * y^6
  have hs := y_mul_conjugate 1 6
  rw [conjugate_mod_seven (1 - 6)] at hs
  exact hs

private theorem seed57 : V [9, 4] = V [3, 9] := by
  change y^1 * conjugate 2 = conjugate 1 * y^1
  have hs := y_mul_conjugate 2 1
  rw [conjugate_mod_seven (2 - 1)] at hs
  exact hs

private theorem seed58 : V [10, 4] = V [2, 10] := by
  change y^2 * conjugate 2 = conjugate 0 * y^2
  have hs := y_mul_conjugate 2 2
  rw [conjugate_mod_seven (2 - 2)] at hs
  exact hs

private theorem seed59 : V [11, 4] = V [8, 11] := by
  change y^3 * conjugate 2 = conjugate 6 * y^3
  have hs := y_mul_conjugate 2 3
  rw [conjugate_mod_seven (2 - 3)] at hs
  exact hs

private theorem seed60 : V [12, 4] = V [7, 12] := by
  change y^4 * conjugate 2 = conjugate 5 * y^4
  have hs := y_mul_conjugate 2 4
  rw [conjugate_mod_seven (2 - 4)] at hs
  exact hs

private theorem seed61 : V [13, 4] = V [6, 13] := by
  change y^5 * conjugate 2 = conjugate 4 * y^5
  have hs := y_mul_conjugate 2 5
  rw [conjugate_mod_seven (2 - 5)] at hs
  exact hs

private theorem seed62 : V [14, 4] = V [5, 14] := by
  change y^6 * conjugate 2 = conjugate 3 * y^6
  have hs := y_mul_conjugate 2 6
  rw [conjugate_mod_seven (2 - 6)] at hs
  exact hs

private theorem seed63 : V [9, 5] = V [4, 9] := by
  change y^1 * conjugate 3 = conjugate 2 * y^1
  have hs := y_mul_conjugate 3 1
  rw [conjugate_mod_seven (3 - 1)] at hs
  exact hs

private theorem seed64 : V [10, 5] = V [3, 10] := by
  change y^2 * conjugate 3 = conjugate 1 * y^2
  have hs := y_mul_conjugate 3 2
  rw [conjugate_mod_seven (3 - 2)] at hs
  exact hs

private theorem seed65 : V [11, 5] = V [2, 11] := by
  change y^3 * conjugate 3 = conjugate 0 * y^3
  have hs := y_mul_conjugate 3 3
  rw [conjugate_mod_seven (3 - 3)] at hs
  exact hs

private theorem seed66 : V [12, 5] = V [8, 12] := by
  change y^4 * conjugate 3 = conjugate 6 * y^4
  have hs := y_mul_conjugate 3 4
  rw [conjugate_mod_seven (3 - 4)] at hs
  exact hs

private theorem seed67 : V [13, 5] = V [7, 13] := by
  change y^5 * conjugate 3 = conjugate 5 * y^5
  have hs := y_mul_conjugate 3 5
  rw [conjugate_mod_seven (3 - 5)] at hs
  exact hs

private theorem seed68 : V [14, 5] = V [6, 14] := by
  change y^6 * conjugate 3 = conjugate 4 * y^6
  have hs := y_mul_conjugate 3 6
  rw [conjugate_mod_seven (3 - 6)] at hs
  exact hs

private theorem seed69 : V [9, 6] = V [5, 9] := by
  change y^1 * conjugate 4 = conjugate 3 * y^1
  have hs := y_mul_conjugate 4 1
  rw [conjugate_mod_seven (4 - 1)] at hs
  exact hs

private theorem seed70 : V [10, 6] = V [4, 10] := by
  change y^2 * conjugate 4 = conjugate 2 * y^2
  have hs := y_mul_conjugate 4 2
  rw [conjugate_mod_seven (4 - 2)] at hs
  exact hs

private theorem seed71 : V [11, 6] = V [3, 11] := by
  change y^3 * conjugate 4 = conjugate 1 * y^3
  have hs := y_mul_conjugate 4 3
  rw [conjugate_mod_seven (4 - 3)] at hs
  exact hs

private theorem seed72 : V [12, 6] = V [2, 12] := by
  change y^4 * conjugate 4 = conjugate 0 * y^4
  have hs := y_mul_conjugate 4 4
  rw [conjugate_mod_seven (4 - 4)] at hs
  exact hs

private theorem seed73 : V [13, 6] = V [8, 13] := by
  change y^5 * conjugate 4 = conjugate 6 * y^5
  have hs := y_mul_conjugate 4 5
  rw [conjugate_mod_seven (4 - 5)] at hs
  exact hs

private theorem seed74 : V [14, 6] = V [7, 14] := by
  change y^6 * conjugate 4 = conjugate 5 * y^6
  have hs := y_mul_conjugate 4 6
  rw [conjugate_mod_seven (4 - 6)] at hs
  exact hs

private theorem seed75 : V [9, 7] = V [6, 9] := by
  change y^1 * conjugate 5 = conjugate 4 * y^1
  have hs := y_mul_conjugate 5 1
  rw [conjugate_mod_seven (5 - 1)] at hs
  exact hs

private theorem seed76 : V [10, 7] = V [5, 10] := by
  change y^2 * conjugate 5 = conjugate 3 * y^2
  have hs := y_mul_conjugate 5 2
  rw [conjugate_mod_seven (5 - 2)] at hs
  exact hs

private theorem seed77 : V [11, 7] = V [4, 11] := by
  change y^3 * conjugate 5 = conjugate 2 * y^3
  have hs := y_mul_conjugate 5 3
  rw [conjugate_mod_seven (5 - 3)] at hs
  exact hs

private theorem seed78 : V [12, 7] = V [3, 12] := by
  change y^4 * conjugate 5 = conjugate 1 * y^4
  have hs := y_mul_conjugate 5 4
  rw [conjugate_mod_seven (5 - 4)] at hs
  exact hs

private theorem seed79 : V [13, 7] = V [2, 13] := by
  change y^5 * conjugate 5 = conjugate 0 * y^5
  have hs := y_mul_conjugate 5 5
  rw [conjugate_mod_seven (5 - 5)] at hs
  exact hs

private theorem seed80 : V [14, 7] = V [8, 14] := by
  change y^6 * conjugate 5 = conjugate 6 * y^6
  have hs := y_mul_conjugate 5 6
  rw [conjugate_mod_seven (5 - 6)] at hs
  exact hs

private theorem seed81 : V [9, 8] = V [7, 9] := by
  change y^1 * conjugate 6 = conjugate 5 * y^1
  have hs := y_mul_conjugate 6 1
  rw [conjugate_mod_seven (6 - 1)] at hs
  exact hs

private theorem seed82 : V [10, 8] = V [6, 10] := by
  change y^2 * conjugate 6 = conjugate 4 * y^2
  have hs := y_mul_conjugate 6 2
  rw [conjugate_mod_seven (6 - 2)] at hs
  exact hs

private theorem seed83 : V [11, 8] = V [5, 11] := by
  change y^3 * conjugate 6 = conjugate 3 * y^3
  have hs := y_mul_conjugate 6 3
  rw [conjugate_mod_seven (6 - 3)] at hs
  exact hs

private theorem seed84 : V [12, 8] = V [4, 12] := by
  change y^4 * conjugate 6 = conjugate 2 * y^4
  have hs := y_mul_conjugate 6 4
  rw [conjugate_mod_seven (6 - 4)] at hs
  exact hs

private theorem seed85 : V [13, 8] = V [3, 13] := by
  change y^5 * conjugate 6 = conjugate 1 * y^5
  have hs := y_mul_conjugate 6 5
  rw [conjugate_mod_seven (6 - 5)] at hs
  exact hs

private theorem seed86 : V [14, 8] = V [2, 14] := by
  change y^6 * conjugate 6 = conjugate 0 * y^6
  have hs := y_mul_conjugate 6 6
  rw [conjugate_mod_seven (6 - 6)] at hs
  exact hs

private theorem seed87 : V [9, 0] = V [0, 9] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.pow_right 1).symm.eq

private theorem seed88 : V [9, 1] = V [1, 9] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.inv_left.pow_right 1).symm.eq

private theorem seed91 : V [11, 0] = V [0, 11] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.pow_right 3).symm.eq

private theorem seed92 : V [11, 1] = V [1, 11] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.inv_left.pow_right 3).symm.eq

private theorem seed93 : V [12, 0] = V [0, 12] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.pow_right 4).symm.eq

private theorem seed94 : V [12, 1] = V [1, 12] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.inv_left.pow_right 4).symm.eq

private theorem seed97 : V [14, 0] = V [0, 14] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.pow_right 6).symm.eq

private theorem seed98 : V [14, 1] = V [1, 14] := by
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] using (u_commute_y.inv_left.pow_right 6).symm.eq

private theorem V_repeat (w : List (Fin 15)) (n : Nat) :
    V ((List.replicate n w).flatten) = V w ^ n := by
  induction n with
  | zero => simp [V]
  | succ n ih => simp only [List.replicate_succ, List.flatten_cons, V_append, ih, pow_succ']

private theorem seventeenth_seventh : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4] = 1 := by
  have hs : value ((seventeenIndices.map (· + 4)).map (· % 7)) ^ 7 = 1 := by
    rw [value_mod, value_shift, ← map_pow, seventeen_pow_seven, map_one]
  change V ((List.replicate 7 [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4]).flatten) = 1
  rw [V_repeat]
  exact hs

private theorem torus0 : V [0, 1] = V [] := by
  have h0 : V [0, 1] = V [] := seed0
  have hl : V [0, 1] = V [0, 1] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1 : V [1, 0] = V [] := by
  have h0 : V [1, 0] = V [] := seed1
  have hl : V [1, 0] = V [1, 0] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2 : V [2, 2] = V [] := by
  have h0 : V [2, 2] = V [] := seed2
  have hl : V [2, 2] = V [2, 2] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus3 : V [3, 3] = V [] := by
  have h0 : V [3, 3] = V [] := seed3
  have hl : V [3, 3] = V [3, 3] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4 : V [4, 4] = V [] := by
  have h0 : V [4, 4] = V [] := seed4
  have hl : V [4, 4] = V [4, 4] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus5 : V [5, 5] = V [] := by
  have h0 : V [5, 5] = V [] := seed5
  have hl : V [5, 5] = V [5, 5] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus6 : V [6, 6] = V [] := by
  have h0 : V [6, 6] = V [] := seed6
  have hl : V [6, 6] = V [6, 6] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus7 : V [7, 7] = V [] := by
  have h0 : V [7, 7] = V [] := seed7
  have hl : V [7, 7] = V [7, 7] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus8 : V [8, 8] = V [] := by
  have h0 : V [8, 8] = V [] := seed8
  have hl : V [8, 8] = V [8, 8] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus11 : V [9, 11] = V [12] := by
  have h0 : V [9, 11] = V [12] := seed11
  have hl : V [9, 11] = V [9, 11] :=
    rfl
  have hr : V [12] = V [12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus12 : V [9, 12] = V [13] := by
  have h0 : V [9, 12] = V [13] := seed12
  have hl : V [9, 12] = V [9, 12] :=
    rfl
  have hr : V [13] = V [13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus21 : V [11, 9] = V [12] := by
  have h0 : V [11, 9] = V [12] := seed21
  have hl : V [11, 9] = V [11, 9] :=
    rfl
  have hr : V [12] = V [12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus23 : V [11, 11] = V [14] := by
  have h0 : V [11, 11] = V [14] := seed23
  have hl : V [11, 11] = V [11, 11] :=
    rfl
  have hr : V [14] = V [14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus24 : V [11, 12] = V [] := by
  have h0 : V [11, 12] = V [] := seed24
  have hl : V [11, 12] = V [11, 12] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus25 : V [11, 13] = V [9] := by
  have h0 : V [11, 13] = V [9] := seed25
  have hl : V [11, 13] = V [11, 13] :=
    rfl
  have hr : V [9] = V [9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus26 : V [11, 14] = V [10] := by
  have h0 : V [11, 14] = V [10] := seed26
  have hl : V [11, 14] = V [11, 14] :=
    rfl
  have hr : V [10] = V [10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus28 : V [12, 10] = V [14] := by
  have h0 : V [12, 10] = V [14] := seed28
  have hl : V [12, 10] = V [12, 10] :=
    rfl
  have hr : V [14] = V [14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus29 : V [12, 11] = V [] := by
  have h0 : V [12, 11] = V [] := seed29
  have hl : V [12, 11] = V [12, 11] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus30 : V [12, 12] = V [9] := by
  have h0 : V [12, 12] = V [9] := seed30
  have hl : V [12, 12] = V [12, 12] :=
    rfl
  have hr : V [9] = V [9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus32 : V [12, 14] = V [11] := by
  have h0 : V [12, 14] = V [11] := seed32
  have hl : V [12, 14] = V [12, 14] :=
    rfl
  have hr : V [11] = V [11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus39 : V [14, 9] = V [] := by
  have h0 : V [14, 9] = V [] := seed39
  have hl : V [14, 9] = V [14, 9] :=
    rfl
  have hr : V [] = V [] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus42 : V [14, 12] = V [11] := by
  have h0 : V [14, 12] = V [11] := seed42
  have hl : V [14, 12] = V [14, 12] :=
    rfl
  have hr : V [11] = V [11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus45 : V [9, 2] = V [8, 9] := by
  have h0 : V [9, 2] = V [8, 9] := seed45
  have hl : V [9, 2] = V [9, 2] :=
    rfl
  have hr : V [8, 9] = V [8, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus46 : V [10, 2] = V [7, 10] := by
  have h0 : V [10, 2] = V [7, 10] := seed46
  have hl : V [10, 2] = V [10, 2] :=
    rfl
  have hr : V [7, 10] = V [7, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus47 : V [11, 2] = V [6, 11] := by
  have h0 : V [11, 2] = V [6, 11] := seed47
  have hl : V [11, 2] = V [11, 2] :=
    rfl
  have hr : V [6, 11] = V [6, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus48 : V [12, 2] = V [5, 12] := by
  have h0 : V [12, 2] = V [5, 12] := seed48
  have hl : V [12, 2] = V [12, 2] :=
    rfl
  have hr : V [5, 12] = V [5, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus49 : V [13, 2] = V [4, 13] := by
  have h0 : V [13, 2] = V [4, 13] := seed49
  have hl : V [13, 2] = V [13, 2] :=
    rfl
  have hr : V [4, 13] = V [4, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus50 : V [14, 2] = V [3, 14] := by
  have h0 : V [14, 2] = V [3, 14] := seed50
  have hl : V [14, 2] = V [14, 2] :=
    rfl
  have hr : V [3, 14] = V [3, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus51 : V [9, 3] = V [2, 9] := by
  have h0 : V [9, 3] = V [2, 9] := seed51
  have hl : V [9, 3] = V [9, 3] :=
    rfl
  have hr : V [2, 9] = V [2, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus52 : V [10, 3] = V [8, 10] := by
  have h0 : V [10, 3] = V [8, 10] := seed52
  have hl : V [10, 3] = V [10, 3] :=
    rfl
  have hr : V [8, 10] = V [8, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus53 : V [11, 3] = V [7, 11] := by
  have h0 : V [11, 3] = V [7, 11] := seed53
  have hl : V [11, 3] = V [11, 3] :=
    rfl
  have hr : V [7, 11] = V [7, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus54 : V [12, 3] = V [6, 12] := by
  have h0 : V [12, 3] = V [6, 12] := seed54
  have hl : V [12, 3] = V [12, 3] :=
    rfl
  have hr : V [6, 12] = V [6, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus55 : V [13, 3] = V [5, 13] := by
  have h0 : V [13, 3] = V [5, 13] := seed55
  have hl : V [13, 3] = V [13, 3] :=
    rfl
  have hr : V [5, 13] = V [5, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus56 : V [14, 3] = V [4, 14] := by
  have h0 : V [14, 3] = V [4, 14] := seed56
  have hl : V [14, 3] = V [14, 3] :=
    rfl
  have hr : V [4, 14] = V [4, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus57 : V [9, 4] = V [3, 9] := by
  have h0 : V [9, 4] = V [3, 9] := seed57
  have hl : V [9, 4] = V [9, 4] :=
    rfl
  have hr : V [3, 9] = V [3, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus58 : V [10, 4] = V [2, 10] := by
  have h0 : V [10, 4] = V [2, 10] := seed58
  have hl : V [10, 4] = V [10, 4] :=
    rfl
  have hr : V [2, 10] = V [2, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus59 : V [11, 4] = V [8, 11] := by
  have h0 : V [11, 4] = V [8, 11] := seed59
  have hl : V [11, 4] = V [11, 4] :=
    rfl
  have hr : V [8, 11] = V [8, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus60 : V [12, 4] = V [7, 12] := by
  have h0 : V [12, 4] = V [7, 12] := seed60
  have hl : V [12, 4] = V [12, 4] :=
    rfl
  have hr : V [7, 12] = V [7, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus61 : V [13, 4] = V [6, 13] := by
  have h0 : V [13, 4] = V [6, 13] := seed61
  have hl : V [13, 4] = V [13, 4] :=
    rfl
  have hr : V [6, 13] = V [6, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus62 : V [14, 4] = V [5, 14] := by
  have h0 : V [14, 4] = V [5, 14] := seed62
  have hl : V [14, 4] = V [14, 4] :=
    rfl
  have hr : V [5, 14] = V [5, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus63 : V [9, 5] = V [4, 9] := by
  have h0 : V [9, 5] = V [4, 9] := seed63
  have hl : V [9, 5] = V [9, 5] :=
    rfl
  have hr : V [4, 9] = V [4, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus64 : V [10, 5] = V [3, 10] := by
  have h0 : V [10, 5] = V [3, 10] := seed64
  have hl : V [10, 5] = V [10, 5] :=
    rfl
  have hr : V [3, 10] = V [3, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus65 : V [11, 5] = V [2, 11] := by
  have h0 : V [11, 5] = V [2, 11] := seed65
  have hl : V [11, 5] = V [11, 5] :=
    rfl
  have hr : V [2, 11] = V [2, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus66 : V [12, 5] = V [8, 12] := by
  have h0 : V [12, 5] = V [8, 12] := seed66
  have hl : V [12, 5] = V [12, 5] :=
    rfl
  have hr : V [8, 12] = V [8, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus67 : V [13, 5] = V [7, 13] := by
  have h0 : V [13, 5] = V [7, 13] := seed67
  have hl : V [13, 5] = V [13, 5] :=
    rfl
  have hr : V [7, 13] = V [7, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus68 : V [14, 5] = V [6, 14] := by
  have h0 : V [14, 5] = V [6, 14] := seed68
  have hl : V [14, 5] = V [14, 5] :=
    rfl
  have hr : V [6, 14] = V [6, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus69 : V [9, 6] = V [5, 9] := by
  have h0 : V [9, 6] = V [5, 9] := seed69
  have hl : V [9, 6] = V [9, 6] :=
    rfl
  have hr : V [5, 9] = V [5, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus70 : V [10, 6] = V [4, 10] := by
  have h0 : V [10, 6] = V [4, 10] := seed70
  have hl : V [10, 6] = V [10, 6] :=
    rfl
  have hr : V [4, 10] = V [4, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus71 : V [11, 6] = V [3, 11] := by
  have h0 : V [11, 6] = V [3, 11] := seed71
  have hl : V [11, 6] = V [11, 6] :=
    rfl
  have hr : V [3, 11] = V [3, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus72 : V [12, 6] = V [2, 12] := by
  have h0 : V [12, 6] = V [2, 12] := seed72
  have hl : V [12, 6] = V [12, 6] :=
    rfl
  have hr : V [2, 12] = V [2, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus73 : V [13, 6] = V [8, 13] := by
  have h0 : V [13, 6] = V [8, 13] := seed73
  have hl : V [13, 6] = V [13, 6] :=
    rfl
  have hr : V [8, 13] = V [8, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus74 : V [14, 6] = V [7, 14] := by
  have h0 : V [14, 6] = V [7, 14] := seed74
  have hl : V [14, 6] = V [14, 6] :=
    rfl
  have hr : V [7, 14] = V [7, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus75 : V [9, 7] = V [6, 9] := by
  have h0 : V [9, 7] = V [6, 9] := seed75
  have hl : V [9, 7] = V [9, 7] :=
    rfl
  have hr : V [6, 9] = V [6, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus76 : V [10, 7] = V [5, 10] := by
  have h0 : V [10, 7] = V [5, 10] := seed76
  have hl : V [10, 7] = V [10, 7] :=
    rfl
  have hr : V [5, 10] = V [5, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus77 : V [11, 7] = V [4, 11] := by
  have h0 : V [11, 7] = V [4, 11] := seed77
  have hl : V [11, 7] = V [11, 7] :=
    rfl
  have hr : V [4, 11] = V [4, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus78 : V [12, 7] = V [3, 12] := by
  have h0 : V [12, 7] = V [3, 12] := seed78
  have hl : V [12, 7] = V [12, 7] :=
    rfl
  have hr : V [3, 12] = V [3, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus79 : V [13, 7] = V [2, 13] := by
  have h0 : V [13, 7] = V [2, 13] := seed79
  have hl : V [13, 7] = V [13, 7] :=
    rfl
  have hr : V [2, 13] = V [2, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus80 : V [14, 7] = V [8, 14] := by
  have h0 : V [14, 7] = V [8, 14] := seed80
  have hl : V [14, 7] = V [14, 7] :=
    rfl
  have hr : V [8, 14] = V [8, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus81 : V [9, 8] = V [7, 9] := by
  have h0 : V [9, 8] = V [7, 9] := seed81
  have hl : V [9, 8] = V [9, 8] :=
    rfl
  have hr : V [7, 9] = V [7, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus82 : V [10, 8] = V [6, 10] := by
  have h0 : V [10, 8] = V [6, 10] := seed82
  have hl : V [10, 8] = V [10, 8] :=
    rfl
  have hr : V [6, 10] = V [6, 10] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus83 : V [11, 8] = V [5, 11] := by
  have h0 : V [11, 8] = V [5, 11] := seed83
  have hl : V [11, 8] = V [11, 8] :=
    rfl
  have hr : V [5, 11] = V [5, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus84 : V [12, 8] = V [4, 12] := by
  have h0 : V [12, 8] = V [4, 12] := seed84
  have hl : V [12, 8] = V [12, 8] :=
    rfl
  have hr : V [4, 12] = V [4, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus85 : V [13, 8] = V [3, 13] := by
  have h0 : V [13, 8] = V [3, 13] := seed85
  have hl : V [13, 8] = V [13, 8] :=
    rfl
  have hr : V [3, 13] = V [3, 13] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus86 : V [14, 8] = V [2, 14] := by
  have h0 : V [14, 8] = V [2, 14] := seed86
  have hl : V [14, 8] = V [14, 8] :=
    rfl
  have hr : V [2, 14] = V [2, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus87 : V [9, 0] = V [0, 9] := by
  have h0 : V [9, 0] = V [0, 9] := seed87
  have hl : V [9, 0] = V [9, 0] :=
    rfl
  have hr : V [0, 9] = V [0, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus88 : V [9, 1] = V [1, 9] := by
  have h0 : V [9, 1] = V [1, 9] := seed88
  have hl : V [9, 1] = V [9, 1] :=
    rfl
  have hr : V [1, 9] = V [1, 9] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus91 : V [11, 0] = V [0, 11] := by
  have h0 : V [11, 0] = V [0, 11] := seed91
  have hl : V [11, 0] = V [11, 0] :=
    rfl
  have hr : V [0, 11] = V [0, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus92 : V [11, 1] = V [1, 11] := by
  have h0 : V [11, 1] = V [1, 11] := seed92
  have hl : V [11, 1] = V [11, 1] :=
    rfl
  have hr : V [1, 11] = V [1, 11] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus93 : V [12, 0] = V [0, 12] := by
  have h0 : V [12, 0] = V [0, 12] := seed93
  have hl : V [12, 0] = V [12, 0] :=
    rfl
  have hr : V [0, 12] = V [0, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus94 : V [12, 1] = V [1, 12] := by
  have h0 : V [12, 1] = V [1, 12] := seed94
  have hl : V [12, 1] = V [12, 1] :=
    rfl
  have hr : V [1, 12] = V [1, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus97 : V [14, 0] = V [0, 14] := by
  have h0 : V [14, 0] = V [0, 14] := seed97
  have hl : V [14, 0] = V [14, 0] :=
    rfl
  have hr : V [0, 14] = V [0, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus98 : V [14, 1] = V [1, 14] := by
  have h0 : V [14, 1] = V [1, 14] := seed98
  have hl : V [14, 1] = V [14, 1] :=
    rfl
  have hr : V [1, 14] = V [1, 14] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus99 : V [3, 4, 3, 4, 5] = V [2, 3, 4, 3, 4] := by
  have h0 : V [2, 3, 4, 3, 4] = V [3, 4, 3, 4, 5] :=
    relation_split _ loop0 true 9 _ _ (by decide)
  have hl : V [2, 3, 4, 3, 4] = V [2, 3, 4, 3, 4] :=
    rfl
  have hr : V [3, 4, 3, 4, 5] = V [3, 4, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus100 : V [4, 3, 4, 5, 4] = V [3, 2, 3, 4, 3] := by
  have h0 : V [4, 3, 4, 5, 4] = V [3, 2, 3, 4, 3] :=
    relation_split _ loop0 true 1 _ _ (by decide)
  have hl : V [4, 3, 4, 5, 4] = V [4, 3, 4, 5, 4] :=
    rfl
  have hr : V [3, 2, 3, 4, 3] = V [3, 2, 3, 4, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus102 : V [3, 4, 5, 4, 3, 4] = V [4, 3, 2, 3] := by
  have h0 : V [3, 4, 5, 4, 3, 4] = V [4, 3, 2, 3] :=
    relation_split _ loop0 true 2 _ _ (by decide)
  have hl : V [3, 4, 5, 4, 3, 4] = V [3, 4, 5, 4, 3, 4] :=
    rfl
  have hr : V [4, 3, 2, 3] = V [4, 3, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus103 : V [4, 5, 4, 3, 4] = V [3, 4, 3, 2, 3] := by
  have h0 : V [4, 5, 4, 3, 4] = V [3, 4, 3, 2, 3] :=
    relation_split _ loop0 true 3 _ _ (by decide)
  have hl : V [4, 5, 4, 3, 4] = V [4, 5, 4, 3, 4] :=
    rfl
  have hr : V [3, 4, 3, 2, 3] = V [3, 4, 3, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus104 : V [5, 4, 3, 4, 3] = V [4, 3, 4, 3, 2] := by
  have h0 : V [5, 4, 3, 4, 3] = V [4, 3, 4, 3, 2] :=
    relation_split _ loop0 true 4 _ _ (by decide)
  have hl : V [5, 4, 3, 4, 3] = V [5, 4, 3, 4, 3] :=
    rfl
  have hr : V [4, 3, 4, 3, 2] = V [4, 3, 4, 3, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus105 : V [4, 3, 4, 3, 2, 3] = V [5, 4, 3, 4] := by
  have h0 : V [4, 3, 4, 3, 2, 3] = V [5, 4, 3, 4] :=
    relation_split _ loop0 true 5 _ _ (by decide)
  have hl : V [4, 3, 4, 3, 2, 3] = V [4, 3, 4, 3, 2, 3] :=
    rfl
  have hr : V [5, 4, 3, 4] = V [5, 4, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus107 : V [4, 5, 4, 5, 6] = V [3, 4, 5, 4, 5] := by
  have h0 : V [3, 4, 5, 4, 5] = V [4, 5, 4, 5, 6] :=
    relation_split _ loop1 true 9 _ _ (by decide)
  have hl : V [3, 4, 5, 4, 5] = V [3, 4, 5, 4, 5] :=
    rfl
  have hr : V [4, 5, 4, 5, 6] = V [4, 5, 4, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus108 : V [5, 4, 5, 6, 5] = V [3, 2, 3, 4, 3] := by
  have h0 : V [5, 4, 5, 6, 5] = V [4, 3, 4, 5, 4] :=
    relation_split _ loop1 true 1 _ _ (by decide)
  have hl : V [5, 4, 5, 6, 5] = V [5, 4, 5, 6, 5] :=
    rfl
  have hr : V [4, 3, 4, 5, 4] = V [3, 2, 3, 4, 3] :=
    (in_context torus100 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus111 : V [5, 6, 5, 4, 5] = V [3, 4, 3, 2, 3] := by
  have h0 : V [5, 6, 5, 4, 5] = V [4, 5, 4, 3, 4] :=
    relation_split _ loop1 true 3 _ _ (by decide)
  have hl : V [5, 6, 5, 4, 5] = V [5, 6, 5, 4, 5] :=
    rfl
  have hr : V [4, 5, 4, 3, 4] = V [3, 4, 3, 2, 3] :=
    (in_context torus103 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus112 : V [6, 5, 4, 5, 4] = V [5, 4, 5, 4, 3] := by
  have h0 : V [6, 5, 4, 5, 4] = V [5, 4, 5, 4, 3] :=
    relation_split _ loop1 true 4 _ _ (by decide)
  have hl : V [6, 5, 4, 5, 4] = V [6, 5, 4, 5, 4] :=
    rfl
  have hr : V [5, 4, 5, 4, 3] = V [5, 4, 5, 4, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus113 : V [5, 3, 4, 3, 2, 3] = V [6, 5, 4, 5] := by
  have h0 : V [5, 4, 5, 4, 3, 4] = V [6, 5, 4, 5] :=
    relation_split _ loop1 true 5 _ _ (by decide)
  have hl : V [5, 4, 5, 4, 3, 4] = V [5, 3, 4, 3, 2, 3] :=
    (in_context torus103 [5] [])
  have hr : V [6, 5, 4, 5] = V [6, 5, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus115 : V [3, 2, 3, 4, 3, 5] = V [5, 4, 5, 6] := by
  have h0 : V [4, 3, 4, 5, 4, 5] = V [5, 4, 5, 6] :=
    relation_split _ loop1 true 8 _ _ (by decide)
  have hl : V [4, 3, 4, 5, 4, 5] = V [3, 2, 3, 4, 3, 5] :=
    (in_context torus100 [] [5])
  have hr : V [5, 4, 5, 6] = V [5, 4, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus116 : V [5, 6, 5, 6, 7] = V [4, 5, 6, 5, 6] := by
  have h0 : V [4, 5, 6, 5, 6] = V [5, 6, 5, 6, 7] :=
    relation_split _ loop2 true 9 _ _ (by decide)
  have hl : V [4, 5, 6, 5, 6] = V [4, 5, 6, 5, 6] :=
    rfl
  have hr : V [5, 6, 5, 6, 7] = V [5, 6, 5, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus117 : V [6, 5, 6, 7, 6] = V [3, 2, 3, 4, 3] := by
  have h0 : V [6, 5, 6, 7, 6] = V [5, 4, 5, 6, 5] :=
    relation_split _ loop2 true 1 _ _ (by decide)
  have hl : V [6, 5, 6, 7, 6] = V [6, 5, 6, 7, 6] :=
    rfl
  have hr : V [5, 4, 5, 6, 5] = V [3, 2, 3, 4, 3] :=
    (in_context torus108 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus120 : V [6, 7, 6, 5, 6] = V [3, 4, 3, 2, 3] := by
  have h0 : V [6, 7, 6, 5, 6] = V [5, 6, 5, 4, 5] :=
    relation_split _ loop2 true 3 _ _ (by decide)
  have hl : V [6, 7, 6, 5, 6] = V [6, 7, 6, 5, 6] :=
    rfl
  have hr : V [5, 6, 5, 4, 5] = V [3, 4, 3, 2, 3] :=
    (in_context torus111 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus121 : V [7, 6, 5, 6, 5] = V [6, 5, 6, 5, 4] := by
  have h0 : V [7, 6, 5, 6, 5] = V [6, 5, 6, 5, 4] :=
    relation_split _ loop2 true 4 _ _ (by decide)
  have hl : V [7, 6, 5, 6, 5] = V [7, 6, 5, 6, 5] :=
    rfl
  have hr : V [6, 5, 6, 5, 4] = V [6, 5, 6, 5, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus122 : V [6, 3, 4, 3, 2, 3] = V [7, 6, 5, 6] := by
  have h0 : V [6, 5, 6, 5, 4, 5] = V [7, 6, 5, 6] :=
    relation_split _ loop2 true 5 _ _ (by decide)
  have hl : V [6, 5, 6, 5, 4, 5] = V [6, 3, 4, 3, 2, 3] :=
    (in_context torus111 [6] [])
  have hr : V [7, 6, 5, 6] = V [7, 6, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus125 : V [6, 7, 6, 7, 8] = V [5, 6, 7, 6, 7] := by
  have h0 : V [5, 6, 7, 6, 7] = V [6, 7, 6, 7, 8] :=
    relation_split _ loop3 true 9 _ _ (by decide)
  have hl : V [5, 6, 7, 6, 7] = V [5, 6, 7, 6, 7] :=
    rfl
  have hr : V [6, 7, 6, 7, 8] = V [6, 7, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus126 : V [7, 6, 7, 8, 7] = V [3, 2, 3, 4, 3] := by
  have h0 : V [7, 6, 7, 8, 7] = V [6, 5, 6, 7, 6] :=
    relation_split _ loop3 true 1 _ _ (by decide)
  have hl : V [7, 6, 7, 8, 7] = V [7, 6, 7, 8, 7] :=
    rfl
  have hr : V [6, 5, 6, 7, 6] = V [3, 2, 3, 4, 3] :=
    (in_context torus117 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus129 : V [7, 8, 7, 6, 7] = V [3, 4, 3, 2, 3] := by
  have h0 : V [7, 8, 7, 6, 7] = V [6, 7, 6, 5, 6] :=
    relation_split _ loop3 true 3 _ _ (by decide)
  have hl : V [7, 8, 7, 6, 7] = V [7, 8, 7, 6, 7] :=
    rfl
  have hr : V [6, 7, 6, 5, 6] = V [3, 4, 3, 2, 3] :=
    (in_context torus120 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus130 : V [8, 7, 6, 7, 6] = V [7, 6, 7, 6, 5] := by
  have h0 : V [8, 7, 6, 7, 6] = V [7, 6, 7, 6, 5] :=
    relation_split _ loop3 true 4 _ _ (by decide)
  have hl : V [8, 7, 6, 7, 6] = V [8, 7, 6, 7, 6] :=
    rfl
  have hr : V [7, 6, 7, 6, 5] = V [7, 6, 7, 6, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus131 : V [7, 3, 4, 3, 2, 3] = V [8, 7, 6, 7] := by
  have h0 : V [7, 6, 7, 6, 5, 6] = V [8, 7, 6, 7] :=
    relation_split _ loop3 true 5 _ _ (by decide)
  have hl : V [7, 6, 7, 6, 5, 6] = V [7, 3, 4, 3, 2, 3] :=
    (in_context torus120 [7] [])
  have hr : V [8, 7, 6, 7] = V [8, 7, 6, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus133 : V [3, 2, 3, 4, 3, 7] = V [7, 6, 7, 8] := by
  have h0 : V [6, 5, 6, 7, 6, 7] = V [7, 6, 7, 8] :=
    relation_split _ loop3 true 8 _ _ (by decide)
  have hl : V [6, 5, 6, 7, 6, 7] = V [3, 2, 3, 4, 3, 7] :=
    (in_context torus117 [] [7])
  have hr : V [7, 6, 7, 8] = V [7, 6, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus134 : V [7, 8, 7, 8, 2] = V [6, 7, 8, 7, 8] := by
  have h0 : V [6, 7, 8, 7, 8] = V [7, 8, 7, 8, 2] :=
    relation_split _ loop4 true 9 _ _ (by decide)
  have hl : V [6, 7, 8, 7, 8] = V [6, 7, 8, 7, 8] :=
    rfl
  have hr : V [7, 8, 7, 8, 2] = V [7, 8, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus135 : V [8, 7, 8, 2, 8] = V [3, 2, 3, 4, 3] := by
  have h0 : V [8, 7, 8, 2, 8] = V [7, 6, 7, 8, 7] :=
    relation_split _ loop4 true 1 _ _ (by decide)
  have hl : V [8, 7, 8, 2, 8] = V [8, 7, 8, 2, 8] :=
    rfl
  have hr : V [7, 6, 7, 8, 7] = V [3, 2, 3, 4, 3] :=
    (in_context torus126 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus138 : V [8, 2, 8, 7, 8] = V [3, 4, 3, 2, 3] := by
  have h0 : V [8, 2, 8, 7, 8] = V [7, 8, 7, 6, 7] :=
    relation_split _ loop4 true 3 _ _ (by decide)
  have hl : V [8, 2, 8, 7, 8] = V [8, 2, 8, 7, 8] :=
    rfl
  have hr : V [7, 8, 7, 6, 7] = V [3, 4, 3, 2, 3] :=
    (in_context torus129 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus139 : V [8, 7, 8, 7, 6] = V [2, 8, 7, 8, 7] := by
  have h0 : V [2, 8, 7, 8, 7] = V [8, 7, 8, 7, 6] :=
    relation_split _ loop4 true 4 _ _ (by decide)
  have hl : V [2, 8, 7, 8, 7] = V [2, 8, 7, 8, 7] :=
    rfl
  have hr : V [8, 7, 8, 7, 6] = V [8, 7, 8, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus142 : V [8, 2, 8, 2, 3] = V [7, 8, 2, 8, 2] := by
  have h0 : V [7, 8, 2, 8, 2] = V [8, 2, 8, 2, 3] :=
    relation_split _ loop5 true 9 _ _ (by decide)
  have hl : V [7, 8, 2, 8, 2] = V [7, 8, 2, 8, 2] :=
    rfl
  have hr : V [8, 2, 8, 2, 3] = V [8, 2, 8, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus143 : V [3, 2, 3, 4, 3] = V [2, 8, 2, 3, 2] := by
  have h0 : V [2, 8, 2, 3, 2] = V [8, 7, 8, 2, 8] :=
    relation_split _ loop5 true 1 _ _ (by decide)
  have hl : V [2, 8, 2, 3, 2] = V [2, 8, 2, 3, 2] :=
    rfl
  have hr : V [8, 7, 8, 2, 8] = V [3, 2, 3, 4, 3] :=
    (in_context torus135 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus145 : V [8, 2, 3, 2, 8] = V [2, 8, 7, 8, 2] := by
  have h0 : V [8, 2, 3, 2, 8] = V [2, 8, 7, 8, 2] :=
    relation_split _ loop5 true 2 _ _ (by decide)
  have hl : V [8, 2, 3, 2, 8] = V [8, 2, 3, 2, 8] :=
    rfl
  have hr : V [2, 8, 7, 8, 2] = V [2, 8, 7, 8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus146 : V [3, 4, 3, 2, 3] = V [2, 3, 2, 8, 2] := by
  have h0 : V [2, 3, 2, 8, 2] = V [8, 2, 8, 7, 8] :=
    relation_split _ loop5 true 3 _ _ (by decide)
  have hl : V [2, 3, 2, 8, 2] = V [2, 3, 2, 8, 2] :=
    rfl
  have hr : V [8, 2, 8, 7, 8] = V [3, 4, 3, 2, 3] :=
    (in_context torus138 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus151 : V [4, 3, 2, 3, 2] = V [3, 2, 3, 2, 8] := by
  have h0 : V [4, 3, 2, 3, 2] = V [3, 2, 3, 2, 8] :=
    relation_split _ loop6 true 4 _ _ (by decide)
  have hl : V [4, 3, 2, 3, 2] = V [4, 3, 2, 3, 2] :=
    rfl
  have hr : V [3, 2, 3, 2, 8] = V [3, 2, 3, 2, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus160 : V [3, 2, 3, 2, 3, 2] = V [2, 3, 2, 3, 2, 3] := by
  have h0 : V [2, 3, 2, 3, 2, 3] = V [3, 2, 3, 2, 3, 2] :=
    relation_split _ loop14 true 11 _ _ (by decide)
  have hl : V [2, 3, 2, 3, 2, 3] = V [2, 3, 2, 3, 2, 3] :=
    rfl
  have hr : V [3, 2, 3, 2, 3, 2] = V [3, 2, 3, 2, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus161 : V [4, 3, 4, 3, 4, 3] = V [3, 4, 3, 4, 3, 4] := by
  have h0 : V [3, 4, 3, 4, 3, 4] = V [4, 3, 4, 3, 4, 3] :=
    relation_split _ loop15 true 11 _ _ (by decide)
  have hl : V [3, 4, 3, 4, 3, 4] = V [3, 4, 3, 4, 3, 4] :=
    rfl
  have hr : V [4, 3, 4, 3, 4, 3] = V [4, 3, 4, 3, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus162 : V [5, 4, 5, 4, 5, 4] = V [4, 5, 4, 5, 4, 5] := by
  have h0 : V [4, 5, 4, 5, 4, 5] = V [5, 4, 5, 4, 5, 4] :=
    relation_split _ loop16 true 11 _ _ (by decide)
  have hl : V [4, 5, 4, 5, 4, 5] = V [4, 5, 4, 5, 4, 5] :=
    rfl
  have hr : V [5, 4, 5, 4, 5, 4] = V [5, 4, 5, 4, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus163 : V [6, 5, 6, 5, 6, 5] = V [5, 6, 5, 6, 5, 6] := by
  have h0 : V [5, 6, 5, 6, 5, 6] = V [6, 5, 6, 5, 6, 5] :=
    relation_split _ loop17 true 11 _ _ (by decide)
  have hl : V [5, 6, 5, 6, 5, 6] = V [5, 6, 5, 6, 5, 6] :=
    rfl
  have hr : V [6, 5, 6, 5, 6, 5] = V [6, 5, 6, 5, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus164 : V [7, 6, 7, 6, 7, 6] = V [6, 7, 6, 7, 6, 7] := by
  have h0 : V [6, 7, 6, 7, 6, 7] = V [7, 6, 7, 6, 7, 6] :=
    relation_split _ loop18 true 11 _ _ (by decide)
  have hl : V [6, 7, 6, 7, 6, 7] = V [6, 7, 6, 7, 6, 7] :=
    rfl
  have hr : V [7, 6, 7, 6, 7, 6] = V [7, 6, 7, 6, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus165 : V [8, 7, 8, 7, 8, 7] = V [7, 8, 7, 8, 7, 8] := by
  have h0 : V [7, 8, 7, 8, 7, 8] = V [8, 7, 8, 7, 8, 7] :=
    relation_split _ loop19 true 11 _ _ (by decide)
  have hl : V [7, 8, 7, 8, 7, 8] = V [7, 8, 7, 8, 7, 8] :=
    rfl
  have hr : V [8, 7, 8, 7, 8, 7] = V [8, 7, 8, 7, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus166 : V [8, 2, 8, 2, 8, 2] = V [2, 8, 2, 8, 2, 8] := by
  have h0 : V [8, 2, 8, 2, 8, 2] = V [2, 8, 2, 8, 2, 8] :=
    relation_split _ loop20 true 11 _ _ (by decide)
  have hl : V [8, 2, 8, 2, 8, 2] = V [8, 2, 8, 2, 8, 2] :=
    rfl
  have hr : V [2, 8, 2, 8, 2, 8] = V [2, 8, 2, 8, 2, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus168 : V [2, 8, 7, 6, 5, 3, 6] = V [4, 2, 5, 4, 5] := by
  have h0 : V [2, 8, 7, 6, 5, 3, 6] = V [4, 2, 5, 4, 5] :=
    relation_split _ loop21 false 0 _ _ (by decide)
  have hl : V [2, 8, 7, 6, 5, 3, 6] = V [2, 8, 7, 6, 5, 3, 6] :=
    rfl
  have hr : V [4, 2, 5, 4, 5] = V [4, 2, 5, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus170 : V [8, 2, 4, 2, 5, 4] = V [7, 6, 5, 3, 6, 5] := by
  have h0 : V [7, 6, 5, 3, 6, 5] = V [8, 2, 4, 2, 5, 4] :=
    relation_split _ loop21 false 2 _ _ (by decide)
  have hl : V [7, 6, 5, 3, 6, 5] = V [7, 6, 5, 3, 6, 5] :=
    rfl
  have hr : V [8, 2, 4, 2, 5, 4] = V [8, 2, 4, 2, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus173 : V [6, 5, 3, 6, 5, 4, 5] = V [7, 8, 2, 4, 2] := by
  have h0 : V [6, 5, 3, 6, 5, 4, 5] = V [7, 8, 2, 4, 2] :=
    relation_split _ loop21 false 3 _ _ (by decide)
  have hl : V [6, 5, 3, 6, 5, 4, 5] = V [6, 5, 3, 6, 5, 4, 5] :=
    rfl
  have hr : V [7, 8, 2, 4, 2] = V [7, 8, 2, 4, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus175 : V [5, 3, 6, 5, 4, 5, 2] = V [6, 7, 8, 2, 4] := by
  have h0 : V [5, 3, 6, 5, 4, 5, 2] = V [6, 7, 8, 2, 4] :=
    relation_split _ loop21 false 4 _ _ (by decide)
  have hl : V [5, 3, 6, 5, 4, 5, 2] = V [5, 3, 6, 5, 4, 5, 2] :=
    rfl
  have hr : V [6, 7, 8, 2, 4] = V [6, 7, 8, 2, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus176 : V [5, 6, 7, 8, 2, 4] = V [3, 6, 5, 4, 5, 2] := by
  have h0 : V [3, 6, 5, 4, 5, 2] = V [5, 6, 7, 8, 2, 4] :=
    relation_split _ loop21 false 5 _ _ (by decide)
  have hl : V [3, 6, 5, 4, 5, 2] = V [3, 6, 5, 4, 5, 2] :=
    rfl
  have hr : V [5, 6, 7, 8, 2, 4] = V [5, 6, 7, 8, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus177 : V [3, 6, 5, 4, 5, 2, 4] = V [5, 6, 7, 8, 2] := by
  have h0 : V [3, 6, 5, 4, 5, 2, 4] = V [5, 6, 7, 8, 2] :=
    relation_split _ loop21 false 5 _ _ (by decide)
  have hl : V [3, 6, 5, 4, 5, 2, 4] = V [3, 6, 5, 4, 5, 2, 4] :=
    rfl
  have hr : V [5, 6, 7, 8, 2] = V [5, 6, 7, 8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus184 : V [5, 4, 5, 6, 3, 5] = V [2, 4, 2, 8, 7, 6] := by
  have h0 : V [2, 4, 2, 8, 7, 6] = V [5, 4, 5, 6, 3, 5] :=
    relation_split _ loop21 false 10 _ _ (by decide)
  have hl : V [2, 4, 2, 8, 7, 6] = V [2, 4, 2, 8, 7, 6] :=
    rfl
  have hr : V [5, 4, 5, 6, 3, 5] = V [5, 4, 5, 6, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus185 : V [2, 4, 2, 8, 7, 6, 5] = V [5, 4, 5, 6, 3] := by
  have h0 : V [2, 4, 2, 8, 7, 6, 5] = V [5, 4, 5, 6, 3] :=
    relation_split _ loop21 false 10 _ _ (by decide)
  have hl : V [2, 4, 2, 8, 7, 6, 5] = V [2, 4, 2, 8, 7, 6, 5] :=
    rfl
  have hr : V [5, 4, 5, 6, 3] = V [5, 4, 5, 6, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus186 : V [4, 2, 8, 7, 6, 5] = V [2, 5, 4, 5, 6, 3] := by
  have h0 : V [4, 2, 8, 7, 6, 5] = V [2, 5, 4, 5, 6, 3] :=
    relation_split _ loop21 false 11 _ _ (by decide)
  have hl : V [4, 2, 8, 7, 6, 5] = V [4, 2, 8, 7, 6, 5] :=
    rfl
  have hr : V [2, 5, 4, 5, 6, 3] = V [2, 5, 4, 5, 6, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus187 : V [5, 3, 6, 5, 6, 7] = V [3, 2, 8, 7, 6, 4] := by
  have h0 : V [3, 2, 8, 7, 6, 4] = V [5, 3, 6, 5, 6, 7] :=
    relation_split _ loop22 false 0 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 6, 4] = V [3, 2, 8, 7, 6, 4] :=
    rfl
  have hr : V [5, 3, 6, 5, 6, 7] = V [5, 3, 6, 5, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus188 : V [3, 2, 8, 7, 6, 4, 7] = V [5, 3, 6, 5, 6] := by
  have h0 : V [3, 2, 8, 7, 6, 4, 7] = V [5, 3, 6, 5, 6] :=
    relation_split _ loop22 false 0 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 6, 4, 7] = V [3, 2, 8, 7, 6, 4, 7] :=
    rfl
  have hr : V [5, 3, 6, 5, 6] = V [5, 3, 6, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus191 : V [8, 7, 6, 4, 7, 6] = V [2, 3, 5, 3, 6, 5] := by
  have h0 : V [8, 7, 6, 4, 7, 6] = V [2, 3, 5, 3, 6, 5] :=
    relation_split _ loop22 false 2 _ _ (by decide)
  have hl : V [8, 7, 6, 4, 7, 6] = V [8, 7, 6, 4, 7, 6] :=
    rfl
  have hr : V [2, 3, 5, 3, 6, 5] = V [2, 3, 5, 3, 6, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus193 : V [7, 6, 4, 7, 6, 5, 6] = V [8, 2, 3, 5, 3] := by
  have h0 : V [7, 6, 4, 7, 6, 5, 6] = V [8, 2, 3, 5, 3] :=
    relation_split _ loop22 false 3 _ _ (by decide)
  have hl : V [7, 6, 4, 7, 6, 5, 6] = V [7, 6, 4, 7, 6, 5, 6] :=
    rfl
  have hr : V [8, 2, 3, 5, 3] = V [8, 2, 3, 5, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus195 : V [6, 4, 7, 6, 5, 6, 3] = V [7, 8, 2, 3, 5] := by
  have h0 : V [6, 4, 7, 6, 5, 6, 3] = V [7, 8, 2, 3, 5] :=
    relation_split _ loop22 false 4 _ _ (by decide)
  have hl : V [6, 4, 7, 6, 5, 6, 3] = V [6, 4, 7, 6, 5, 6, 3] :=
    rfl
  have hr : V [7, 8, 2, 3, 5] = V [7, 8, 2, 3, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus196 : V [6, 7, 8, 2, 3, 5] = V [4, 7, 6, 5, 6, 3] := by
  have h0 : V [4, 7, 6, 5, 6, 3] = V [6, 7, 8, 2, 3, 5] :=
    relation_split _ loop22 false 5 _ _ (by decide)
  have hl : V [4, 7, 6, 5, 6, 3] = V [4, 7, 6, 5, 6, 3] :=
    rfl
  have hr : V [6, 7, 8, 2, 3, 5] = V [6, 7, 8, 2, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus197 : V [4, 7, 6, 5, 6, 3, 5] = V [6, 7, 8, 2, 3] := by
  have h0 : V [4, 7, 6, 5, 6, 3, 5] = V [6, 7, 8, 2, 3] :=
    relation_split _ loop22 false 5 _ _ (by decide)
  have hl : V [4, 7, 6, 5, 6, 3, 5] = V [4, 7, 6, 5, 6, 3, 5] :=
    rfl
  have hr : V [6, 7, 8, 2, 3] = V [6, 7, 8, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus204 : V [6, 5, 6, 7, 4, 6] = V [3, 5, 3, 2, 8, 7] := by
  have h0 : V [3, 5, 3, 2, 8, 7] = V [6, 5, 6, 7, 4, 6] :=
    relation_split _ loop22 false 10 _ _ (by decide)
  have hl : V [3, 5, 3, 2, 8, 7] = V [3, 5, 3, 2, 8, 7] :=
    rfl
  have hr : V [6, 5, 6, 7, 4, 6] = V [6, 5, 6, 7, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus205 : V [3, 5, 3, 2, 8, 7, 6] = V [6, 5, 6, 7, 4] := by
  have h0 : V [3, 5, 3, 2, 8, 7, 6] = V [6, 5, 6, 7, 4] :=
    relation_split _ loop22 false 10 _ _ (by decide)
  have hl : V [3, 5, 3, 2, 8, 7, 6] = V [3, 5, 3, 2, 8, 7, 6] :=
    rfl
  have hr : V [6, 5, 6, 7, 4] = V [6, 5, 6, 7, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus206 : V [5, 3, 2, 8, 7, 6] = V [3, 6, 5, 6, 7, 4] := by
  have h0 : V [5, 3, 2, 8, 7, 6] = V [3, 6, 5, 6, 7, 4] :=
    relation_split _ loop22 false 11 _ _ (by decide)
  have hl : V [5, 3, 2, 8, 7, 6] = V [5, 3, 2, 8, 7, 6] :=
    rfl
  have hr : V [3, 6, 5, 6, 7, 4] = V [3, 6, 5, 6, 7, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus207 : V [6, 4, 7, 6, 7, 8] = V [4, 3, 2, 8, 7, 5] := by
  have h0 : V [4, 3, 2, 8, 7, 5] = V [6, 4, 7, 6, 7, 8] :=
    relation_split _ loop23 false 0 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 7, 5] = V [4, 3, 2, 8, 7, 5] :=
    rfl
  have hr : V [6, 4, 7, 6, 7, 8] = V [6, 4, 7, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus208 : V [4, 3, 2, 8, 7, 5, 8] = V [6, 4, 7, 6, 7] := by
  have h0 : V [4, 3, 2, 8, 7, 5, 8] = V [6, 4, 7, 6, 7] :=
    relation_split _ loop23 false 0 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 7, 5, 8] = V [4, 3, 2, 8, 7, 5, 8] :=
    rfl
  have hr : V [6, 4, 7, 6, 7] = V [6, 4, 7, 6, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus209 : V [4, 6, 4, 7, 6, 7] = V [3, 2, 8, 7, 5, 8] := by
  have h0 : V [3, 2, 8, 7, 5, 8] = V [4, 6, 4, 7, 6, 7] :=
    relation_split _ loop23 false 1 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 5, 8] = V [3, 2, 8, 7, 5, 8] :=
    rfl
  have hr : V [4, 6, 4, 7, 6, 7] = V [4, 6, 4, 7, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus211 : V [3, 4, 6, 4, 7, 6] = V [2, 8, 7, 5, 8, 7] := by
  have h0 : V [2, 8, 7, 5, 8, 7] = V [3, 4, 6, 4, 7, 6] :=
    relation_split _ loop23 false 2 _ _ (by decide)
  have hl : V [2, 8, 7, 5, 8, 7] = V [2, 8, 7, 5, 8, 7] :=
    rfl
  have hr : V [3, 4, 6, 4, 7, 6] = V [3, 4, 6, 4, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus215 : V [7, 5, 8, 7, 6, 7, 4] = V [8, 2, 3, 4, 6] := by
  have h0 : V [7, 5, 8, 7, 6, 7, 4] = V [8, 2, 3, 4, 6] :=
    relation_split _ loop23 false 4 _ _ (by decide)
  have hl : V [7, 5, 8, 7, 6, 7, 4] = V [7, 5, 8, 7, 6, 7, 4] :=
    rfl
  have hr : V [8, 2, 3, 4, 6] = V [8, 2, 3, 4, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus216 : V [7, 8, 2, 3, 4, 6] = V [5, 8, 7, 6, 7, 4] := by
  have h0 : V [5, 8, 7, 6, 7, 4] = V [7, 8, 2, 3, 4, 6] :=
    relation_split _ loop23 false 5 _ _ (by decide)
  have hl : V [5, 8, 7, 6, 7, 4] = V [5, 8, 7, 6, 7, 4] :=
    rfl
  have hr : V [7, 8, 2, 3, 4, 6] = V [7, 8, 2, 3, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus217 : V [5, 8, 7, 6, 7, 4, 6] = V [7, 8, 2, 3, 4] := by
  have h0 : V [5, 8, 7, 6, 7, 4, 6] = V [7, 8, 2, 3, 4] :=
    relation_split _ loop23 false 5 _ _ (by decide)
  have hl : V [5, 8, 7, 6, 7, 4, 6] = V [5, 8, 7, 6, 7, 4, 6] :=
    rfl
  have hr : V [7, 8, 2, 3, 4] = V [7, 8, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus218 : V [8, 7, 6, 7, 4, 6] = V [5, 7, 8, 2, 3, 4] := by
  have h0 : V [8, 7, 6, 7, 4, 6] = V [5, 7, 8, 2, 3, 4] :=
    relation_split _ loop23 false 6 _ _ (by decide)
  have hl : V [8, 7, 6, 7, 4, 6] = V [8, 7, 6, 7, 4, 6] :=
    rfl
  have hr : V [5, 7, 8, 2, 3, 4] = V [5, 7, 8, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus224 : V [7, 6, 7, 8, 5, 7] = V [4, 6, 4, 3, 2, 8] := by
  have h0 : V [4, 6, 4, 3, 2, 8] = V [7, 6, 7, 8, 5, 7] :=
    relation_split _ loop23 false 10 _ _ (by decide)
  have hl : V [4, 6, 4, 3, 2, 8] = V [4, 6, 4, 3, 2, 8] :=
    rfl
  have hr : V [7, 6, 7, 8, 5, 7] = V [7, 6, 7, 8, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus226 : V [6, 4, 3, 2, 8, 7] = V [4, 7, 6, 7, 8, 5] := by
  have h0 : V [6, 4, 3, 2, 8, 7] = V [4, 7, 6, 7, 8, 5] :=
    relation_split _ loop23 false 11 _ _ (by decide)
  have hl : V [6, 4, 3, 2, 8, 7] = V [6, 4, 3, 2, 8, 7] :=
    rfl
  have hr : V [4, 7, 6, 7, 8, 5] = V [4, 7, 6, 7, 8, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus227 : V [7, 5, 8, 7, 8, 2] = V [5, 4, 3, 2, 8, 6] := by
  have h0 : V [5, 4, 3, 2, 8, 6] = V [7, 5, 8, 7, 8, 2] :=
    relation_split _ loop24 false 0 _ _ (by decide)
  have hl : V [5, 4, 3, 2, 8, 6] = V [5, 4, 3, 2, 8, 6] :=
    rfl
  have hr : V [7, 5, 8, 7, 8, 2] = V [7, 5, 8, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus229 : V [5, 7, 5, 8, 7, 8] = V [4, 3, 2, 8, 6, 2] := by
  have h0 : V [4, 3, 2, 8, 6, 2] = V [5, 7, 5, 8, 7, 8] :=
    relation_split _ loop24 false 1 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 6, 2] = V [4, 3, 2, 8, 6, 2] :=
    rfl
  have hr : V [5, 7, 5, 8, 7, 8] = V [5, 7, 5, 8, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus231 : V [4, 5, 7, 5, 8, 7] = V [3, 2, 8, 6, 2, 8] := by
  have h0 : V [3, 2, 8, 6, 2, 8] = V [4, 5, 7, 5, 8, 7] :=
    relation_split _ loop24 false 2 _ _ (by decide)
  have hl : V [3, 2, 8, 6, 2, 8] = V [3, 2, 8, 6, 2, 8] :=
    rfl
  have hr : V [4, 5, 7, 5, 8, 7] = V [4, 5, 7, 5, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus235 : V [8, 6, 2, 8, 7, 8] = V [2, 3, 4, 5, 7, 5] := by
  have h0 : V [8, 6, 2, 8, 7, 8] = V [2, 3, 4, 5, 7, 5] :=
    relation_split _ loop24 false 4 _ _ (by decide)
  have hl : V [8, 6, 2, 8, 7, 8] = V [8, 6, 2, 8, 7, 8] :=
    rfl
  have hr : V [2, 3, 4, 5, 7, 5] = V [2, 3, 4, 5, 7, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus236 : V [8, 2, 3, 4, 5, 7] = V [6, 2, 8, 7, 8, 5] := by
  have h0 : V [6, 2, 8, 7, 8, 5] = V [8, 2, 3, 4, 5, 7] :=
    relation_split _ loop24 false 5 _ _ (by decide)
  have hl : V [6, 2, 8, 7, 8, 5] = V [6, 2, 8, 7, 8, 5] :=
    rfl
  have hr : V [8, 2, 3, 4, 5, 7] = V [8, 2, 3, 4, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus237 : V [6, 2, 8, 7, 8, 5, 7] = V [8, 2, 3, 4, 5] := by
  have h0 : V [6, 2, 8, 7, 8, 5, 7] = V [8, 2, 3, 4, 5] :=
    relation_split _ loop24 false 5 _ _ (by decide)
  have hl : V [6, 2, 8, 7, 8, 5, 7] = V [6, 2, 8, 7, 8, 5, 7] :=
    rfl
  have hr : V [8, 2, 3, 4, 5] = V [8, 2, 3, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus238 : V [6, 8, 2, 3, 4, 5] = V [2, 8, 7, 8, 5, 7] := by
  have h0 : V [2, 8, 7, 8, 5, 7] = V [6, 8, 2, 3, 4, 5] :=
    relation_split _ loop24 false 6 _ _ (by decide)
  have hl : V [2, 8, 7, 8, 5, 7] = V [2, 8, 7, 8, 5, 7] :=
    rfl
  have hr : V [6, 8, 2, 3, 4, 5] = V [6, 8, 2, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus241 : V [8, 2, 6, 8, 2, 3] = V [7, 8, 5, 7, 5, 4] := by
  have h0 : V [7, 8, 5, 7, 5, 4] = V [8, 2, 6, 8, 2, 3] :=
    relation_split _ loop24 false 8 _ _ (by decide)
  have hl : V [7, 8, 5, 7, 5, 4] = V [7, 8, 5, 7, 5, 4] :=
    rfl
  have hr : V [8, 2, 6, 8, 2, 3] = V [8, 2, 6, 8, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus244 : V [8, 7, 8, 2, 6, 8] = V [5, 7, 5, 4, 3, 2] := by
  have h0 : V [5, 7, 5, 4, 3, 2] = V [8, 7, 8, 2, 6, 8] :=
    relation_split _ loop24 false 10 _ _ (by decide)
  have hl : V [5, 7, 5, 4, 3, 2] = V [5, 7, 5, 4, 3, 2] :=
    rfl
  have hr : V [8, 7, 8, 2, 6, 8] = V [8, 7, 8, 2, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus246 : V [7, 5, 4, 3, 2, 8] = V [5, 8, 7, 8, 2, 6] := by
  have h0 : V [7, 5, 4, 3, 2, 8] = V [5, 8, 7, 8, 2, 6] :=
    relation_split _ loop24 false 11 _ _ (by decide)
  have hl : V [7, 5, 4, 3, 2, 8] = V [7, 5, 4, 3, 2, 8] :=
    rfl
  have hr : V [5, 8, 7, 8, 2, 6] = V [5, 8, 7, 8, 2, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus248 : V [6, 5, 4, 3, 2, 7, 3] = V [8, 6, 2, 8, 2] := by
  have h0 : V [6, 5, 4, 3, 2, 7, 3] = V [8, 6, 2, 8, 2] :=
    relation_split _ loop25 false 0 _ _ (by decide)
  have hl : V [6, 5, 4, 3, 2, 7, 3] = V [6, 5, 4, 3, 2, 7, 3] :=
    rfl
  have hr : V [8, 6, 2, 8, 2] = V [8, 6, 2, 8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus252 : V [4, 3, 2, 7, 3, 2, 8] = V [5, 6, 8, 6, 2] := by
  have h0 : V [4, 3, 2, 7, 3, 2, 8] = V [5, 6, 8, 6, 2] :=
    relation_split _ loop25 false 2 _ _ (by decide)
  have hl : V [4, 3, 2, 7, 3, 2, 8] = V [4, 3, 2, 7, 3, 2, 8] :=
    rfl
  have hr : V [5, 6, 8, 6, 2] = V [5, 6, 8, 6, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus255 : V [3, 4, 5, 6, 8, 6] = V [2, 7, 3, 2, 8, 2] := by
  have h0 : V [2, 7, 3, 2, 8, 2] = V [3, 4, 5, 6, 8, 6] :=
    relation_split _ loop25 false 4 _ _ (by decide)
  have hl : V [2, 7, 3, 2, 8, 2] = V [2, 7, 3, 2, 8, 2] :=
    rfl
  have hr : V [3, 4, 5, 6, 8, 6] = V [3, 4, 5, 6, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus256 : V [2, 7, 3, 2, 8, 2, 6] = V [3, 4, 5, 6, 8] := by
  have h0 : V [2, 7, 3, 2, 8, 2, 6] = V [3, 4, 5, 6, 8] :=
    relation_split _ loop25 false 4 _ _ (by decide)
  have hl : V [2, 7, 3, 2, 8, 2, 6] = V [2, 7, 3, 2, 8, 2, 6] :=
    rfl
  have hr : V [3, 4, 5, 6, 8] = V [3, 4, 5, 6, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus257 : V [7, 3, 2, 8, 2, 6] = V [2, 3, 4, 5, 6, 8] := by
  have h0 : V [7, 3, 2, 8, 2, 6] = V [2, 3, 4, 5, 6, 8] :=
    relation_split _ loop25 false 5 _ _ (by decide)
  have hl : V [7, 3, 2, 8, 2, 6] = V [7, 3, 2, 8, 2, 6] :=
    rfl
  have hr : V [2, 3, 4, 5, 6, 8] = V [2, 3, 4, 5, 6, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus259 : V [3, 2, 8, 2, 6, 8, 6] = V [7, 2, 3, 4, 5] := by
  have h0 : V [3, 2, 8, 2, 6, 8, 6] = V [7, 2, 3, 4, 5] :=
    relation_split _ loop25 false 6 _ _ (by decide)
  have hl : V [3, 2, 8, 2, 6, 8, 6] = V [3, 2, 8, 2, 6, 8, 6] :=
    rfl
  have hr : V [7, 2, 3, 4, 5] = V [7, 2, 3, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus261 : V [2, 8, 2, 6, 8, 6, 5] = V [3, 7, 2, 3, 4] := by
  have h0 : V [2, 8, 2, 6, 8, 6, 5] = V [3, 7, 2, 3, 4] :=
    relation_split _ loop25 false 7 _ _ (by decide)
  have hl : V [2, 8, 2, 6, 8, 6, 5] = V [2, 8, 2, 6, 8, 6, 5] :=
    rfl
  have hr : V [3, 7, 2, 3, 4] = V [3, 7, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus262 : V [8, 2, 6, 8, 6, 5] = V [2, 3, 7, 2, 3, 4] := by
  have h0 : V [8, 2, 6, 8, 6, 5] = V [2, 3, 7, 2, 3, 4] :=
    relation_split _ loop25 false 8 _ _ (by decide)
  have hl : V [8, 2, 6, 8, 6, 5] = V [8, 2, 6, 8, 6, 5] :=
    rfl
  have hr : V [2, 3, 7, 2, 3, 4] = V [2, 3, 7, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus265 : V [6, 8, 6, 5, 4, 3] = V [2, 8, 2, 3, 7, 2] := by
  have h0 : V [6, 8, 6, 5, 4, 3] = V [2, 8, 2, 3, 7, 2] :=
    relation_split _ loop25 false 10 _ _ (by decide)
  have hl : V [6, 8, 6, 5, 4, 3] = V [6, 8, 6, 5, 4, 3] :=
    rfl
  have hr : V [2, 8, 2, 3, 7, 2] = V [2, 8, 2, 3, 7, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus266 : V [8, 6, 5, 4, 3, 2] = V [6, 2, 8, 2, 3, 7] := by
  have h0 : V [8, 6, 5, 4, 3, 2] = V [6, 2, 8, 2, 3, 7] :=
    relation_split _ loop25 false 11 _ _ (by decide)
  have hl : V [8, 6, 5, 4, 3, 2] = V [8, 6, 5, 4, 3, 2] :=
    rfl
  have hr : V [6, 2, 8, 2, 3, 7] = V [6, 2, 8, 2, 3, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus267 : V [6, 2, 8, 2, 3, 7, 2] = V [8, 6, 5, 4, 3] := by
  have h0 : V [6, 2, 8, 2, 3, 7, 2] = V [8, 6, 5, 4, 3] :=
    relation_split _ loop25 true 1 _ _ (by decide)
  have hl : V [6, 2, 8, 2, 3, 7, 2] = V [6, 2, 8, 2, 3, 7, 2] :=
    rfl
  have hr : V [8, 6, 5, 4, 3] = V [8, 6, 5, 4, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus268 : V [7, 6, 5, 4, 3, 8] = V [2, 7, 3, 2, 3, 4] := by
  have h0 : V [7, 6, 5, 4, 3, 8] = V [2, 7, 3, 2, 3, 4] :=
    relation_split _ loop26 false 0 _ _ (by decide)
  have hl : V [7, 6, 5, 4, 3, 8] = V [7, 6, 5, 4, 3, 8] :=
    rfl
  have hr : V [2, 7, 3, 2, 3, 4] = V [2, 7, 3, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus271 : V [6, 7, 2, 7, 3, 2] = V [5, 4, 3, 8, 4, 3] := by
  have h0 : V [5, 4, 3, 8, 4, 3] = V [6, 7, 2, 7, 3, 2] :=
    relation_split _ loop26 false 2 _ _ (by decide)
  have hl : V [5, 4, 3, 8, 4, 3] = V [5, 4, 3, 8, 4, 3] :=
    rfl
  have hr : V [6, 7, 2, 7, 3, 2] = V [6, 7, 2, 7, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus274 : V [4, 3, 8, 4, 3, 2, 3] = V [5, 6, 7, 2, 7] := by
  have h0 : V [4, 3, 8, 4, 3, 2, 3] = V [5, 6, 7, 2, 7] :=
    relation_split _ loop26 false 3 _ _ (by decide)
  have hl : V [4, 3, 8, 4, 3, 2, 3] = V [4, 3, 8, 4, 3, 2, 3] :=
    rfl
  have hr : V [5, 6, 7, 2, 7] = V [5, 6, 7, 2, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus275 : V [4, 5, 6, 7, 2, 7] = V [3, 8, 4, 3, 2, 3] := by
  have h0 : V [3, 8, 4, 3, 2, 3] = V [4, 5, 6, 7, 2, 7] :=
    relation_split _ loop26 false 4 _ _ (by decide)
  have hl : V [3, 8, 4, 3, 2, 3] = V [3, 8, 4, 3, 2, 3] :=
    rfl
  have hr : V [4, 5, 6, 7, 2, 7] = V [4, 5, 6, 7, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus276 : V [3, 8, 4, 3, 2, 3, 7] = V [4, 5, 6, 7, 2] := by
  have h0 : V [3, 8, 4, 3, 2, 3, 7] = V [4, 5, 6, 7, 2] :=
    relation_split _ loop26 false 4 _ _ (by decide)
  have hl : V [3, 8, 4, 3, 2, 3, 7] = V [3, 8, 4, 3, 2, 3, 7] :=
    rfl
  have hr : V [4, 5, 6, 7, 2] = V [4, 5, 6, 7, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus278 : V [8, 3, 4, 5, 6, 7] = V [4, 3, 2, 3, 7, 2] := by
  have h0 : V [4, 3, 2, 3, 7, 2] = V [8, 3, 4, 5, 6, 7] :=
    relation_split _ loop26 false 6 _ _ (by decide)
  have hl : V [4, 3, 2, 3, 7, 2] = V [4, 3, 2, 3, 7, 2] :=
    rfl
  have hr : V [8, 3, 4, 5, 6, 7] = V [8, 3, 4, 5, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus279 : V [4, 3, 2, 3, 7, 2, 7] = V [8, 3, 4, 5, 6] := by
  have h0 : V [4, 3, 2, 3, 7, 2, 7] = V [8, 3, 4, 5, 6] :=
    relation_split _ loop26 false 6 _ _ (by decide)
  have hl : V [4, 3, 2, 3, 7, 2, 7] = V [4, 3, 2, 3, 7, 2, 7] :=
    rfl
  have hr : V [8, 3, 4, 5, 6] = V [8, 3, 4, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus281 : V [3, 2, 3, 7, 2, 7, 6] = V [4, 8, 3, 4, 5] := by
  have h0 : V [3, 2, 3, 7, 2, 7, 6] = V [4, 8, 3, 4, 5] :=
    relation_split _ loop26 false 7 _ _ (by decide)
  have hl : V [3, 2, 3, 7, 2, 7, 6] = V [3, 2, 3, 7, 2, 7, 6] :=
    rfl
  have hr : V [4, 8, 3, 4, 5] = V [4, 8, 3, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus282 : V [3, 4, 8, 3, 4, 5] = V [2, 3, 7, 2, 7, 6] := by
  have h0 : V [2, 3, 7, 2, 7, 6] = V [3, 4, 8, 3, 4, 5] :=
    relation_split _ loop26 false 8 _ _ (by decide)
  have hl : V [2, 3, 7, 2, 7, 6] = V [2, 3, 7, 2, 7, 6] :=
    rfl
  have hr : V [3, 4, 8, 3, 4, 5] = V [3, 4, 8, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus285 : V [7, 2, 7, 6, 5, 4] = V [3, 2, 3, 4, 8, 3] := by
  have h0 : V [7, 2, 7, 6, 5, 4] = V [3, 2, 3, 4, 8, 3] :=
    relation_split _ loop26 false 10 _ _ (by decide)
  have hl : V [7, 2, 7, 6, 5, 4] = V [7, 2, 7, 6, 5, 4] :=
    rfl
  have hr : V [3, 2, 3, 4, 8, 3] = V [3, 2, 3, 4, 8, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus287 : V [3, 2, 3, 4, 8, 3, 4] = V [7, 2, 7, 6, 5] := by
  have h0 : V [3, 2, 3, 4, 8, 3, 4] = V [7, 2, 7, 6, 5] :=
    relation_split _ loop26 true 2 _ _ (by decide)
  have hl : V [3, 2, 3, 4, 8, 3, 4] = V [3, 2, 3, 4, 8, 3, 4] :=
    rfl
  have hr : V [7, 2, 7, 6, 5] = V [7, 2, 7, 6, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus288 : V [8, 7, 6, 5, 4, 2] = V [3, 8, 4, 3, 4, 5] := by
  have h0 : V [8, 7, 6, 5, 4, 2] = V [3, 8, 4, 3, 4, 5] :=
    relation_split _ loop27 false 0 _ _ (by decide)
  have hl : V [8, 7, 6, 5, 4, 2] = V [8, 7, 6, 5, 4, 2] :=
    rfl
  have hr : V [3, 8, 4, 3, 4, 5] = V [3, 8, 4, 3, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus291 : V [7, 8, 3, 8, 4, 3] = V [6, 5, 4, 2, 5, 4] := by
  have h0 : V [6, 5, 4, 2, 5, 4] = V [7, 8, 3, 8, 4, 3] :=
    relation_split _ loop27 false 2 _ _ (by decide)
  have hl : V [6, 5, 4, 2, 5, 4] = V [6, 5, 4, 2, 5, 4] :=
    rfl
  have hr : V [7, 8, 3, 8, 4, 3] = V [7, 8, 3, 8, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus294 : V [5, 4, 2, 5, 4, 3, 4] = V [6, 7, 8, 3, 8] := by
  have h0 : V [5, 4, 2, 5, 4, 3, 4] = V [6, 7, 8, 3, 8] :=
    relation_split _ loop27 false 3 _ _ (by decide)
  have hl : V [5, 4, 2, 5, 4, 3, 4] = V [5, 4, 2, 5, 4, 3, 4] :=
    rfl
  have hr : V [6, 7, 8, 3, 8] = V [6, 7, 8, 3, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus295 : V [5, 6, 7, 8, 3, 8] = V [4, 2, 5, 4, 3, 4] := by
  have h0 : V [4, 2, 5, 4, 3, 4] = V [5, 6, 7, 8, 3, 8] :=
    relation_split _ loop27 false 4 _ _ (by decide)
  have hl : V [4, 2, 5, 4, 3, 4] = V [4, 2, 5, 4, 3, 4] :=
    rfl
  have hr : V [5, 6, 7, 8, 3, 8] = V [5, 6, 7, 8, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus296 : V [4, 2, 5, 4, 3, 4, 8] = V [5, 6, 7, 8, 3] := by
  have h0 : V [4, 2, 5, 4, 3, 4, 8] = V [5, 6, 7, 8, 3] :=
    relation_split _ loop27 false 4 _ _ (by decide)
  have hl : V [4, 2, 5, 4, 3, 4, 8] = V [4, 2, 5, 4, 3, 4, 8] :=
    rfl
  have hr : V [5, 6, 7, 8, 3] = V [5, 6, 7, 8, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus297 : V [4, 5, 6, 7, 8, 3] = V [2, 5, 4, 3, 4, 8] := by
  have h0 : V [2, 5, 4, 3, 4, 8] = V [4, 5, 6, 7, 8, 3] :=
    relation_split _ loop27 false 5 _ _ (by decide)
  have hl : V [2, 5, 4, 3, 4, 8] = V [2, 5, 4, 3, 4, 8] :=
    rfl
  have hr : V [4, 5, 6, 7, 8, 3] = V [4, 5, 6, 7, 8, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus298 : V [2, 5, 4, 3, 4, 8, 3] = V [4, 5, 6, 7, 8] := by
  have h0 : V [2, 5, 4, 3, 4, 8, 3] = V [4, 5, 6, 7, 8] :=
    relation_split _ loop27 false 5 _ _ (by decide)
  have hl : V [2, 5, 4, 3, 4, 8, 3] = V [2, 5, 4, 3, 4, 8, 3] :=
    rfl
  have hr : V [4, 5, 6, 7, 8] = V [4, 5, 6, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus299 : V [5, 4, 3, 4, 8, 3] = V [2, 4, 5, 6, 7, 8] := by
  have h0 : V [5, 4, 3, 4, 8, 3] = V [2, 4, 5, 6, 7, 8] :=
    relation_split _ loop27 false 6 _ _ (by decide)
  have hl : V [5, 4, 3, 4, 8, 3] = V [5, 4, 3, 4, 8, 3] :=
    rfl
  have hr : V [2, 4, 5, 6, 7, 8] = V [2, 4, 5, 6, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus305 : V [8, 3, 8, 7, 6, 5] = V [4, 3, 4, 5, 2, 4] := by
  have h0 : V [8, 3, 8, 7, 6, 5] = V [4, 3, 4, 5, 2, 4] :=
    relation_split _ loop27 false 10 _ _ (by decide)
  have hl : V [8, 3, 8, 7, 6, 5] = V [8, 3, 8, 7, 6, 5] :=
    rfl
  have hr : V [4, 3, 4, 5, 2, 4] = V [4, 3, 4, 5, 2, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus306 : V [8, 4, 3, 4, 5, 2] = V [3, 8, 7, 6, 5, 4] := by
  have h0 : V [3, 8, 7, 6, 5, 4] = V [8, 4, 3, 4, 5, 2] :=
    relation_split _ loop27 false 11 _ _ (by decide)
  have hl : V [3, 8, 7, 6, 5, 4] = V [3, 8, 7, 6, 5, 4] :=
    rfl
  have hr : V [8, 4, 3, 4, 5, 2] = V [8, 4, 3, 4, 5, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus307 : V [4, 3, 4, 5, 2, 4, 5] = V [8, 3, 8, 7, 6] := by
  have h0 : V [4, 3, 4, 5, 2, 4, 5] = V [8, 3, 8, 7, 6] :=
    relation_split _ loop27 true 2 _ _ (by decide)
  have hl : V [4, 3, 4, 5, 2, 4, 5] = V [4, 3, 4, 5, 2, 4, 5] :=
    rfl
  have hr : V [8, 3, 8, 7, 6] = V [8, 3, 8, 7, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1402 : V [3, 4, 5, 6, 7, 8, 2, 3, 12] = V [2, 8, 7, 6, 5, 4, 3, 2, 8] := by
  have h0 : V [2, 8, 7, 6, 5, 4, 3, 2, 8] = V [12, 7, 8, 2, 3, 4, 5, 6, 7] :=
    relation_split _ loop56 false 0 _ _ (by decide)
  have hl : V [2, 8, 7, 6, 5, 4, 3, 2, 8] = V [2, 8, 7, 6, 5, 4, 3, 2, 8] :=
    rfl
  have hr : V [12, 7, 8, 2, 3, 4, 5, 6, 7] = V [3, 4, 5, 6, 7, 8, 2, 3, 12] :=
    ((in_context torus78 [] [8, 2, 3, 4, 5, 6, 7]).trans ((in_context torus84 [3] [2, 3, 4, 5, 6, 7]).trans ((in_context torus48 [3, 4] [3, 4, 5, 6, 7]).trans ((in_context torus54 [3, 4, 5] [4, 5, 6, 7]).trans ((in_context torus60 [3, 4, 5, 6] [5, 6, 7]).trans ((in_context torus66 [3, 4, 5, 6, 7] [6, 7]).trans ((in_context torus72 [3, 4, 5, 6, 7, 8] [7]).trans (in_context torus78 [3, 4, 5, 6, 7, 8, 2] []))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1403 : V [2, 8, 7, 6, 5, 4, 3, 2, 8, 7] = V [3, 4, 5, 6, 7, 8, 2, 12] := by
  have h0 : V [2, 8, 7, 6, 5, 4, 3, 2, 8, 7] = V [12, 7, 8, 2, 3, 4, 5, 6] :=
    relation_split _ loop56 false 0 _ _ (by decide)
  have hl : V [2, 8, 7, 6, 5, 4, 3, 2, 8, 7] = V [2, 8, 7, 6, 5, 4, 3, 2, 8, 7] :=
    rfl
  have hr : V [12, 7, 8, 2, 3, 4, 5, 6] = V [3, 4, 5, 6, 7, 8, 2, 12] :=
    ((in_context torus78 [] [8, 2, 3, 4, 5, 6]).trans ((in_context torus84 [3] [2, 3, 4, 5, 6]).trans ((in_context torus48 [3, 4] [3, 4, 5, 6]).trans ((in_context torus54 [3, 4, 5] [4, 5, 6]).trans ((in_context torus60 [3, 4, 5, 6] [5, 6]).trans ((in_context torus66 [3, 4, 5, 6, 7] [6]).trans (in_context torus72 [3, 4, 5, 6, 7, 8] [])))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1404 : V [8, 7, 6, 5, 4, 3, 2, 8, 7] = V [2, 3, 4, 5, 6, 7, 8, 2, 12] := by
  have h0 : V [8, 7, 6, 5, 4, 3, 2, 8, 7] = V [2, 12, 7, 8, 2, 3, 4, 5, 6] :=
    relation_split _ loop56 false 1 _ _ (by decide)
  have hl : V [8, 7, 6, 5, 4, 3, 2, 8, 7] = V [8, 7, 6, 5, 4, 3, 2, 8, 7] :=
    rfl
  have hr : V [2, 12, 7, 8, 2, 3, 4, 5, 6] = V [2, 3, 4, 5, 6, 7, 8, 2, 12] :=
    ((in_context torus78 [2] [8, 2, 3, 4, 5, 6]).trans ((in_context torus84 [2, 3] [2, 3, 4, 5, 6]).trans ((in_context torus48 [2, 3, 4] [3, 4, 5, 6]).trans ((in_context torus54 [2, 3, 4, 5] [4, 5, 6]).trans ((in_context torus60 [2, 3, 4, 5, 6] [5, 6]).trans ((in_context torus66 [2, 3, 4, 5, 6, 7] [6]).trans (in_context torus72 [2, 3, 4, 5, 6, 7, 8] [])))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1405 : V [8, 2, 3, 4, 5, 6, 7, 8, 12] = V [7, 6, 5, 4, 3, 2, 8, 7, 6] := by
  have h0 : V [7, 6, 5, 4, 3, 2, 8, 7, 6] = V [8, 2, 12, 7, 8, 2, 3, 4, 5] :=
    relation_split _ loop56 false 2 _ _ (by decide)
  have hl : V [7, 6, 5, 4, 3, 2, 8, 7, 6] = V [7, 6, 5, 4, 3, 2, 8, 7, 6] :=
    rfl
  have hr : V [8, 2, 12, 7, 8, 2, 3, 4, 5] = V [8, 2, 3, 4, 5, 6, 7, 8, 12] :=
    ((in_context torus78 [8, 2] [8, 2, 3, 4, 5]).trans ((in_context torus84 [8, 2, 3] [2, 3, 4, 5]).trans ((in_context torus48 [8, 2, 3, 4] [3, 4, 5]).trans ((in_context torus54 [8, 2, 3, 4, 5] [4, 5]).trans ((in_context torus60 [8, 2, 3, 4, 5, 6] [5]).trans (in_context torus66 [8, 2, 3, 4, 5, 6, 7] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1408 : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4] = V [7, 8, 2, 3, 4, 5, 6, 12] := by
  have h0 : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4] = V [7, 8, 2, 12, 7, 8, 2, 3] :=
    relation_split _ loop56 false 3 _ _ (by decide)
  have hl : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4] = V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4] :=
    rfl
  have hr : V [7, 8, 2, 12, 7, 8, 2, 3] = V [7, 8, 2, 3, 4, 5, 6, 12] :=
    ((in_context torus78 [7, 8, 2] [8, 2, 3]).trans ((in_context torus84 [7, 8, 2, 3] [2, 3]).trans ((in_context torus48 [7, 8, 2, 3, 4] [3]).trans (in_context torus54 [7, 8, 2, 3, 4, 5] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1409 : V [6, 7, 8, 2, 3, 4, 5, 6, 12] = V [5, 4, 3, 2, 8, 7, 6, 5, 4] := by
  have h0 : V [5, 4, 3, 2, 8, 7, 6, 5, 4] = V [6, 7, 8, 2, 12, 7, 8, 2, 3] :=
    relation_split _ loop56 false 4 _ _ (by decide)
  have hl : V [5, 4, 3, 2, 8, 7, 6, 5, 4] = V [5, 4, 3, 2, 8, 7, 6, 5, 4] :=
    rfl
  have hr : V [6, 7, 8, 2, 12, 7, 8, 2, 3] = V [6, 7, 8, 2, 3, 4, 5, 6, 12] :=
    ((in_context torus78 [6, 7, 8, 2] [8, 2, 3]).trans ((in_context torus84 [6, 7, 8, 2, 3] [2, 3]).trans ((in_context torus48 [6, 7, 8, 2, 3, 4] [3]).trans (in_context torus54 [6, 7, 8, 2, 3, 4, 5] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1411 : V [5, 6, 7, 8, 2, 3, 4, 5, 12] = V [4, 3, 2, 8, 7, 6, 5, 4, 3] := by
  have h0 : V [4, 3, 2, 8, 7, 6, 5, 4, 3] = V [5, 6, 7, 8, 2, 12, 7, 8, 2] :=
    relation_split _ loop56 false 5 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 7, 6, 5, 4, 3] = V [4, 3, 2, 8, 7, 6, 5, 4, 3] :=
    rfl
  have hr : V [5, 6, 7, 8, 2, 12, 7, 8, 2] = V [5, 6, 7, 8, 2, 3, 4, 5, 12] :=
    ((in_context torus78 [5, 6, 7, 8, 2] [8, 2]).trans ((in_context torus84 [5, 6, 7, 8, 2, 3] [2]).trans (in_context torus48 [5, 6, 7, 8, 2, 3, 4] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1412 : V [4, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [5, 6, 7, 8, 2, 3, 4, 12] := by
  have h0 : V [4, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [5, 6, 7, 8, 2, 12, 7, 8] :=
    relation_split _ loop56 false 5 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [4, 3, 2, 8, 7, 6, 5, 4, 3, 2] :=
    rfl
  have hr : V [5, 6, 7, 8, 2, 12, 7, 8] = V [5, 6, 7, 8, 2, 3, 4, 12] :=
    ((in_context torus78 [5, 6, 7, 8, 2] [8]).trans (in_context torus84 [5, 6, 7, 8, 2, 3] []))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1413 : V [4, 5, 6, 7, 8, 2, 3, 4, 12] = V [3, 2, 8, 7, 6, 5, 4, 3, 2] := by
  have h0 : V [3, 2, 8, 7, 6, 5, 4, 3, 2] = V [4, 5, 6, 7, 8, 2, 12, 7, 8] :=
    relation_split _ loop56 false 6 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 6, 5, 4, 3, 2] = V [3, 2, 8, 7, 6, 5, 4, 3, 2] :=
    rfl
  have hr : V [4, 5, 6, 7, 8, 2, 12, 7, 8] = V [4, 5, 6, 7, 8, 2, 3, 4, 12] :=
    ((in_context torus78 [4, 5, 6, 7, 8, 2] [8]).trans (in_context torus84 [4, 5, 6, 7, 8, 2, 3] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1414 : V [3, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [4, 5, 6, 7, 8, 2, 3, 12] := by
  have h0 : V [3, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [4, 5, 6, 7, 8, 2, 12, 7] :=
    relation_split _ loop56 false 6 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [3, 2, 8, 7, 6, 5, 4, 3, 2, 8] :=
    rfl
  have hr : V [4, 5, 6, 7, 8, 2, 12, 7] = V [4, 5, 6, 7, 8, 2, 3, 12] :=
    (in_context torus78 [4, 5, 6, 7, 8, 2] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1416 : V [7, 6, 5, 4, 3, 2, 8, 7, 6, 11] = V [8, 2, 3, 4, 5, 6, 7, 8] := by
  have h0 : V [7, 6, 5, 4, 3, 2, 8, 7, 11, 2] = V [8, 2, 3, 4, 5, 6, 7, 8] :=
    relation_split _ loop56 false 9 _ _ (by decide)
  have hl : V [7, 6, 5, 4, 3, 2, 8, 7, 11, 2] = V [7, 6, 5, 4, 3, 2, 8, 7, 6, 11] :=
    (in_context torus47 [7, 6, 5, 4, 3, 2, 8, 7] [])
  have hr : V [8, 2, 3, 4, 5, 6, 7, 8] = V [8, 2, 3, 4, 5, 6, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1417 : V [7, 8, 2, 3, 4, 5, 6, 7, 8] = V [6, 5, 4, 3, 2, 8, 7, 6, 11] := by
  have h0 : V [6, 5, 4, 3, 2, 8, 7, 11, 2] = V [7, 8, 2, 3, 4, 5, 6, 7, 8] :=
    relation_split _ loop56 false 10 _ _ (by decide)
  have hl : V [6, 5, 4, 3, 2, 8, 7, 11, 2] = V [6, 5, 4, 3, 2, 8, 7, 6, 11] :=
    (in_context torus47 [6, 5, 4, 3, 2, 8, 7] [])
  have hr : V [7, 8, 2, 3, 4, 5, 6, 7, 8] = V [7, 8, 2, 3, 4, 5, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1418 : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 11] = V [7, 8, 2, 3, 4, 5, 6, 7] := by
  have h0 : V [6, 5, 4, 3, 2, 8, 7, 11, 2, 8] = V [7, 8, 2, 3, 4, 5, 6, 7] :=
    relation_split _ loop56 false 10 _ _ (by decide)
  have hl : V [6, 5, 4, 3, 2, 8, 7, 11, 2, 8] = V [6, 5, 4, 3, 2, 8, 7, 6, 5, 11] :=
    ((in_context torus47 [6, 5, 4, 3, 2, 8, 7] [8]).trans (in_context torus83 [6, 5, 4, 3, 2, 8, 7, 6] []))
  have hr : V [7, 8, 2, 3, 4, 5, 6, 7] = V [7, 8, 2, 3, 4, 5, 6, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1420 : V [5, 4, 3, 2, 8, 7, 6, 5, 4, 11] = V [6, 7, 8, 2, 3, 4, 5, 6] := by
  have h0 : V [5, 4, 3, 2, 8, 7, 11, 2, 8, 7] = V [6, 7, 8, 2, 3, 4, 5, 6] :=
    relation_split _ loop56 false 11 _ _ (by decide)
  have hl : V [5, 4, 3, 2, 8, 7, 11, 2, 8, 7] = V [5, 4, 3, 2, 8, 7, 6, 5, 4, 11] :=
    ((in_context torus47 [5, 4, 3, 2, 8, 7] [8, 7]).trans ((in_context torus83 [5, 4, 3, 2, 8, 7, 6] [7]).trans (in_context torus77 [5, 4, 3, 2, 8, 7, 6, 5] [])))
  have hr : V [6, 7, 8, 2, 3, 4, 5, 6] = V [6, 7, 8, 2, 3, 4, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1422 : V [4, 3, 2, 8, 7, 6, 5, 4, 3, 11] = V [5, 6, 7, 8, 2, 3, 4, 5] := by
  have h0 : V [4, 3, 2, 8, 7, 11, 2, 8, 7, 6] = V [5, 6, 7, 8, 2, 3, 4, 5] :=
    relation_split _ loop56 false 12 _ _ (by decide)
  have hl : V [4, 3, 2, 8, 7, 11, 2, 8, 7, 6] = V [4, 3, 2, 8, 7, 6, 5, 4, 3, 11] :=
    ((in_context torus47 [4, 3, 2, 8, 7] [8, 7, 6]).trans ((in_context torus83 [4, 3, 2, 8, 7, 6] [7, 6]).trans ((in_context torus77 [4, 3, 2, 8, 7, 6, 5] [6]).trans (in_context torus71 [4, 3, 2, 8, 7, 6, 5, 4] []))))
  have hr : V [5, 6, 7, 8, 2, 3, 4, 5] = V [5, 6, 7, 8, 2, 3, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1423 : V [4, 5, 6, 7, 8, 2, 3, 4, 5] = V [3, 2, 8, 7, 6, 5, 4, 3, 11] := by
  have h0 : V [3, 2, 8, 7, 11, 2, 8, 7, 6] = V [4, 5, 6, 7, 8, 2, 3, 4, 5] :=
    relation_split _ loop56 false 13 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 11, 2, 8, 7, 6] = V [3, 2, 8, 7, 6, 5, 4, 3, 11] :=
    ((in_context torus47 [3, 2, 8, 7] [8, 7, 6]).trans ((in_context torus83 [3, 2, 8, 7, 6] [7, 6]).trans ((in_context torus77 [3, 2, 8, 7, 6, 5] [6]).trans (in_context torus71 [3, 2, 8, 7, 6, 5, 4] []))))
  have hr : V [4, 5, 6, 7, 8, 2, 3, 4, 5] = V [4, 5, 6, 7, 8, 2, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1424 : V [3, 2, 8, 7, 6, 5, 4, 3, 2, 11] = V [4, 5, 6, 7, 8, 2, 3, 4] := by
  have h0 : V [3, 2, 8, 7, 11, 2, 8, 7, 6, 5] = V [4, 5, 6, 7, 8, 2, 3, 4] :=
    relation_split _ loop56 false 13 _ _ (by decide)
  have hl : V [3, 2, 8, 7, 11, 2, 8, 7, 6, 5] = V [3, 2, 8, 7, 6, 5, 4, 3, 2, 11] :=
    ((in_context torus47 [3, 2, 8, 7] [8, 7, 6, 5]).trans ((in_context torus83 [3, 2, 8, 7, 6] [7, 6, 5]).trans ((in_context torus77 [3, 2, 8, 7, 6, 5] [6, 5]).trans ((in_context torus71 [3, 2, 8, 7, 6, 5, 4] [5]).trans (in_context torus65 [3, 2, 8, 7, 6, 5, 4, 3] [])))))
  have hr : V [4, 5, 6, 7, 8, 2, 3, 4] = V [4, 5, 6, 7, 8, 2, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1426 : V [2, 8, 7, 6, 5, 4, 3, 2, 8, 11] = V [3, 4, 5, 6, 7, 8, 2, 3] := by
  have h0 : V [2, 8, 7, 11, 2, 8, 7, 6, 5, 4] = V [3, 4, 5, 6, 7, 8, 2, 3] :=
    relation_split _ loop56 false 14 _ _ (by decide)
  have hl : V [2, 8, 7, 11, 2, 8, 7, 6, 5, 4] = V [2, 8, 7, 6, 5, 4, 3, 2, 8, 11] :=
    ((in_context torus47 [2, 8, 7] [8, 7, 6, 5, 4]).trans ((in_context torus83 [2, 8, 7, 6] [7, 6, 5, 4]).trans ((in_context torus77 [2, 8, 7, 6, 5] [6, 5, 4]).trans ((in_context torus71 [2, 8, 7, 6, 5, 4] [5, 4]).trans ((in_context torus65 [2, 8, 7, 6, 5, 4, 3] [4]).trans (in_context torus59 [2, 8, 7, 6, 5, 4, 3, 2] []))))))
  have hr : V [3, 4, 5, 6, 7, 8, 2, 3] = V [3, 4, 5, 6, 7, 8, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1427 : V [8, 7, 6, 5, 4, 3, 2, 8, 11] = V [2, 3, 4, 5, 6, 7, 8, 2, 3] := by
  have h0 : V [8, 7, 11, 2, 8, 7, 6, 5, 4] = V [2, 3, 4, 5, 6, 7, 8, 2, 3] :=
    relation_split _ loop56 false 15 _ _ (by decide)
  have hl : V [8, 7, 11, 2, 8, 7, 6, 5, 4] = V [8, 7, 6, 5, 4, 3, 2, 8, 11] :=
    ((in_context torus47 [8, 7] [8, 7, 6, 5, 4]).trans ((in_context torus83 [8, 7, 6] [7, 6, 5, 4]).trans ((in_context torus77 [8, 7, 6, 5] [6, 5, 4]).trans ((in_context torus71 [8, 7, 6, 5, 4] [5, 4]).trans ((in_context torus65 [8, 7, 6, 5, 4, 3] [4]).trans (in_context torus59 [8, 7, 6, 5, 4, 3, 2] []))))))
  have hr : V [2, 3, 4, 5, 6, 7, 8, 2, 3] = V [2, 3, 4, 5, 6, 7, 8, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1428 : V [2, 8, 2] = V [0, 2, 3] := by
  have h0 : V [2, 8, 2] = V [0, 2, 3] :=
    relation_split _ loop63 false 0 _ _ (by decide)
  have hl : V [2, 8, 2] = V [2, 8, 2] :=
    rfl
  have hr : V [0, 2, 3] = V [0, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1429 : V [8, 2, 3] = V [2, 0, 2] := by
  have h0 : V [8, 2, 3] = V [2, 0, 2] :=
    relation_split _ loop63 false 1 _ _ (by decide)
  have hl : V [8, 2, 3] = V [8, 2, 3] :=
    rfl
  have hr : V [2, 0, 2] = V [2, 0, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1430 : V [8, 2, 0] = V [2, 3, 2] := by
  have h0 : V [2, 3, 2] = V [8, 2, 0] :=
    relation_split _ loop63 false 2 _ _ (by decide)
  have hl : V [2, 3, 2] = V [2, 3, 2] :=
    rfl
  have hr : V [8, 2, 0] = V [8, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1431 : V [2, 3, 2, 1] = V [8, 2] := by
  have h0 : V [2, 3, 2, 1] = V [8, 2] :=
    relation_split _ loop63 false 2 _ _ (by decide)
  have hl : V [2, 3, 2, 1] = V [2, 3, 2, 1] :=
    rfl
  have hr : V [8, 2] = V [8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1432 : V [3, 2, 1] = V [0, 2, 3] := by
  have h0 : V [3, 2, 1] = V [2, 8, 2] :=
    relation_split _ loop63 false 3 _ _ (by decide)
  have hl : V [3, 2, 1] = V [3, 2, 1] :=
    rfl
  have hr : V [2, 8, 2] = V [0, 2, 3] :=
    (in_context torus1428 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1433 : V [0, 2, 3, 2] = V [2, 8] := by
  have h0 : V [3, 2, 1, 2] = V [2, 8] :=
    relation_split _ loop63 false 3 _ _ (by decide)
  have hl : V [3, 2, 1, 2] = V [0, 2, 3, 2] :=
    (in_context torus1432 [] [2])
  have hr : V [2, 8] = V [2, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1434 : V [3, 2, 8] = V [2, 1, 2] := by
  have h0 : V [2, 1, 2] = V [3, 2, 8] :=
    relation_split _ loop63 false 4 _ _ (by decide)
  have hl : V [2, 1, 2] = V [2, 1, 2] :=
    rfl
  have hr : V [3, 2, 8] = V [3, 2, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1435 : V [2, 1, 2, 8] = V [3, 2] := by
  have h0 : V [2, 1, 2, 8] = V [3, 2] :=
    relation_split _ loop63 false 4 _ _ (by decide)
  have hl : V [2, 1, 2, 8] = V [2, 1, 2, 8] :=
    rfl
  have hr : V [3, 2] = V [3, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1436 : V [2, 3, 2] = V [1, 2, 8] := by
  have h0 : V [1, 2, 8] = V [2, 3, 2] :=
    relation_split _ loop63 false 5 _ _ (by decide)
  have hl : V [1, 2, 8] = V [1, 2, 8] :=
    rfl
  have hr : V [2, 3, 2] = V [2, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1437 : V [0, 2, 3, 0] = V [3, 2] := by
  have h0 : V [2, 8, 2, 0] = V [3, 2] :=
    relation_split _ loop63 true 3 _ _ (by decide)
  have hl : V [2, 8, 2, 0] = V [0, 2, 3, 0] :=
    (in_context torus1428 [] [0])
  have hr : V [3, 2] = V [3, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1438 : V [2, 0, 2, 3] = V [8, 2] := by
  have h0 : V [2, 0, 2, 3] = V [8, 2] :=
    relation_split _ loop63 true 5 _ _ (by decide)
  have hl : V [2, 0, 2, 3] = V [2, 0, 2, 3] :=
    rfl
  have hr : V [8, 2] = V [8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1439 : V [3, 2, 3] = V [0, 3, 4] := by
  have h0 : V [3, 2, 3] = V [0, 3, 4] :=
    relation_split _ loop64 false 0 _ _ (by decide)
  have hl : V [3, 2, 3] = V [3, 2, 3] :=
    rfl
  have hr : V [0, 3, 4] = V [0, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1440 : V [3, 0, 3] = V [2, 3, 4] := by
  have h0 : V [2, 3, 4] = V [3, 0, 3] :=
    relation_split _ loop64 false 1 _ _ (by decide)
  have hl : V [2, 3, 4] = V [2, 3, 4] :=
    rfl
  have hr : V [3, 0, 3] = V [3, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1441 : V [2, 3, 4, 3] = V [3, 0] := by
  have h0 : V [2, 3, 4, 3] = V [3, 0] :=
    relation_split _ loop64 false 1 _ _ (by decide)
  have hl : V [2, 3, 4, 3] = V [2, 3, 4, 3] :=
    rfl
  have hr : V [3, 0] = V [3, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1442 : V [3, 4, 3] = V [2, 3, 0] := by
  have h0 : V [3, 4, 3] = V [2, 3, 0] :=
    relation_split _ loop64 false 2 _ _ (by decide)
  have hl : V [3, 4, 3] = V [3, 4, 3] :=
    rfl
  have hr : V [2, 3, 0] = V [2, 3, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1443 : V [4, 3, 1] = V [0, 3, 4] := by
  have h0 : V [4, 3, 1] = V [3, 2, 3] :=
    relation_split _ loop64 false 3 _ _ (by decide)
  have hl : V [4, 3, 1] = V [4, 3, 1] :=
    rfl
  have hr : V [3, 2, 3] = V [0, 3, 4] :=
    (in_context torus1439 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1444 : V [4, 3, 2] = V [3, 1, 3] := by
  have h0 : V [3, 1, 3] = V [4, 3, 2] :=
    relation_split _ loop64 false 4 _ _ (by decide)
  have hl : V [3, 1, 3] = V [3, 1, 3] :=
    rfl
  have hr : V [4, 3, 2] = V [4, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1445 : V [3, 1, 3, 2] = V [4, 3] := by
  have h0 : V [3, 1, 3, 2] = V [4, 3] :=
    relation_split _ loop64 false 4 _ _ (by decide)
  have hl : V [3, 1, 3, 2] = V [3, 1, 3, 2] :=
    rfl
  have hr : V [4, 3] = V [4, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1446 : V [2, 3, 0] = V [1, 3, 2] := by
  have h0 : V [1, 3, 2] = V [3, 4, 3] :=
    relation_split _ loop64 false 5 _ _ (by decide)
  have hl : V [1, 3, 2] = V [1, 3, 2] :=
    rfl
  have hr : V [3, 4, 3] = V [2, 3, 0] :=
    (in_context torus1442 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1447 : V [0, 3, 4, 0] = V [4, 3] := by
  have h0 : V [3, 2, 3, 0] = V [4, 3] :=
    relation_split _ loop64 true 3 _ _ (by decide)
  have hl : V [3, 2, 3, 0] = V [0, 3, 4, 0] :=
    (in_context torus1439 [] [0])
  have hr : V [4, 3] = V [4, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1448 : V [4, 3, 4] = V [0, 4, 5] := by
  have h0 : V [4, 3, 4] = V [0, 4, 5] :=
    relation_split _ loop65 false 0 _ _ (by decide)
  have hl : V [4, 3, 4] = V [4, 3, 4] :=
    rfl
  have hr : V [0, 4, 5] = V [0, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1449 : V [4, 0, 4] = V [3, 4, 5] := by
  have h0 : V [3, 4, 5] = V [4, 0, 4] :=
    relation_split _ loop65 false 1 _ _ (by decide)
  have hl : V [3, 4, 5] = V [3, 4, 5] :=
    rfl
  have hr : V [4, 0, 4] = V [4, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1450 : V [3, 4, 5, 4] = V [4, 0] := by
  have h0 : V [3, 4, 5, 4] = V [4, 0] :=
    relation_split _ loop65 false 1 _ _ (by decide)
  have hl : V [3, 4, 5, 4] = V [3, 4, 5, 4] :=
    rfl
  have hr : V [4, 0] = V [4, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1451 : V [4, 5, 4] = V [3, 4, 0] := by
  have h0 : V [4, 5, 4] = V [3, 4, 0] :=
    relation_split _ loop65 false 2 _ _ (by decide)
  have hl : V [4, 5, 4] = V [4, 5, 4] :=
    rfl
  have hr : V [3, 4, 0] = V [3, 4, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1452 : V [5, 4, 1] = V [0, 4, 5] := by
  have h0 : V [5, 4, 1] = V [4, 3, 4] :=
    relation_split _ loop65 false 3 _ _ (by decide)
  have hl : V [5, 4, 1] = V [5, 4, 1] :=
    rfl
  have hr : V [4, 3, 4] = V [0, 4, 5] :=
    (in_context torus1448 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1453 : V [5, 4, 3] = V [4, 1, 4] := by
  have h0 : V [4, 1, 4] = V [5, 4, 3] :=
    relation_split _ loop65 false 4 _ _ (by decide)
  have hl : V [4, 1, 4] = V [4, 1, 4] :=
    rfl
  have hr : V [5, 4, 3] = V [5, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1454 : V [4, 1, 4, 3] = V [5, 4] := by
  have h0 : V [4, 1, 4, 3] = V [5, 4] :=
    relation_split _ loop65 false 4 _ _ (by decide)
  have hl : V [4, 1, 4, 3] = V [4, 1, 4, 3] :=
    rfl
  have hr : V [5, 4] = V [5, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1455 : V [3, 4, 0] = V [1, 4, 3] := by
  have h0 : V [1, 4, 3] = V [4, 5, 4] :=
    relation_split _ loop65 false 5 _ _ (by decide)
  have hl : V [1, 4, 3] = V [1, 4, 3] :=
    rfl
  have hr : V [4, 5, 4] = V [3, 4, 0] :=
    (in_context torus1451 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1457 : V [5, 4, 5] = V [0, 5, 6] := by
  have h0 : V [5, 4, 5] = V [0, 5, 6] :=
    relation_split _ loop66 false 0 _ _ (by decide)
  have hl : V [5, 4, 5] = V [5, 4, 5] :=
    rfl
  have hr : V [0, 5, 6] = V [0, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1458 : V [5, 0, 5] = V [4, 5, 6] := by
  have h0 : V [4, 5, 6] = V [5, 0, 5] :=
    relation_split _ loop66 false 1 _ _ (by decide)
  have hl : V [4, 5, 6] = V [4, 5, 6] :=
    rfl
  have hr : V [5, 0, 5] = V [5, 0, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1459 : V [4, 5, 6, 5] = V [5, 0] := by
  have h0 : V [4, 5, 6, 5] = V [5, 0] :=
    relation_split _ loop66 false 1 _ _ (by decide)
  have hl : V [4, 5, 6, 5] = V [4, 5, 6, 5] :=
    rfl
  have hr : V [5, 0] = V [5, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1460 : V [5, 6, 5] = V [4, 5, 0] := by
  have h0 : V [5, 6, 5] = V [4, 5, 0] :=
    relation_split _ loop66 false 2 _ _ (by decide)
  have hl : V [5, 6, 5] = V [5, 6, 5] :=
    rfl
  have hr : V [4, 5, 0] = V [4, 5, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1461 : V [6, 5, 1] = V [0, 5, 6] := by
  have h0 : V [6, 5, 1] = V [5, 4, 5] :=
    relation_split _ loop66 false 3 _ _ (by decide)
  have hl : V [6, 5, 1] = V [6, 5, 1] :=
    rfl
  have hr : V [5, 4, 5] = V [0, 5, 6] :=
    (in_context torus1457 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1462 : V [6, 5, 4] = V [5, 1, 5] := by
  have h0 : V [5, 1, 5] = V [6, 5, 4] :=
    relation_split _ loop66 false 4 _ _ (by decide)
  have hl : V [5, 1, 5] = V [5, 1, 5] :=
    rfl
  have hr : V [6, 5, 4] = V [6, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1463 : V [5, 1, 5, 4] = V [6, 5] := by
  have h0 : V [5, 1, 5, 4] = V [6, 5] :=
    relation_split _ loop66 false 4 _ _ (by decide)
  have hl : V [5, 1, 5, 4] = V [5, 1, 5, 4] :=
    rfl
  have hr : V [6, 5] = V [6, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1464 : V [4, 5, 0] = V [1, 5, 4] := by
  have h0 : V [1, 5, 4] = V [5, 6, 5] :=
    relation_split _ loop66 false 5 _ _ (by decide)
  have hl : V [1, 5, 4] = V [1, 5, 4] :=
    rfl
  have hr : V [5, 6, 5] = V [4, 5, 0] :=
    (in_context torus1460 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1465 : V [0, 5, 6, 0] = V [6, 5] := by
  have h0 : V [5, 4, 5, 0] = V [6, 5] :=
    relation_split _ loop66 true 3 _ _ (by decide)
  have hl : V [5, 4, 5, 0] = V [0, 5, 6, 0] :=
    (in_context torus1457 [] [0])
  have hr : V [6, 5] = V [6, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1466 : V [6, 5, 6] = V [0, 6, 7] := by
  have h0 : V [6, 5, 6] = V [0, 6, 7] :=
    relation_split _ loop67 false 0 _ _ (by decide)
  have hl : V [6, 5, 6] = V [6, 5, 6] :=
    rfl
  have hr : V [0, 6, 7] = V [0, 6, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1467 : V [6, 0, 6] = V [5, 6, 7] := by
  have h0 : V [5, 6, 7] = V [6, 0, 6] :=
    relation_split _ loop67 false 1 _ _ (by decide)
  have hl : V [5, 6, 7] = V [5, 6, 7] :=
    rfl
  have hr : V [6, 0, 6] = V [6, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1468 : V [5, 6, 7, 6] = V [6, 0] := by
  have h0 : V [5, 6, 7, 6] = V [6, 0] :=
    relation_split _ loop67 false 1 _ _ (by decide)
  have hl : V [5, 6, 7, 6] = V [5, 6, 7, 6] :=
    rfl
  have hr : V [6, 0] = V [6, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1469 : V [6, 7, 6] = V [5, 6, 0] := by
  have h0 : V [6, 7, 6] = V [5, 6, 0] :=
    relation_split _ loop67 false 2 _ _ (by decide)
  have hl : V [6, 7, 6] = V [6, 7, 6] :=
    rfl
  have hr : V [5, 6, 0] = V [5, 6, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1470 : V [7, 6, 1] = V [0, 6, 7] := by
  have h0 : V [7, 6, 1] = V [6, 5, 6] :=
    relation_split _ loop67 false 3 _ _ (by decide)
  have hl : V [7, 6, 1] = V [7, 6, 1] :=
    rfl
  have hr : V [6, 5, 6] = V [0, 6, 7] :=
    (in_context torus1466 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1471 : V [7, 6, 5] = V [6, 1, 6] := by
  have h0 : V [6, 1, 6] = V [7, 6, 5] :=
    relation_split _ loop67 false 4 _ _ (by decide)
  have hl : V [6, 1, 6] = V [6, 1, 6] :=
    rfl
  have hr : V [7, 6, 5] = V [7, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1472 : V [6, 1, 6, 5] = V [7, 6] := by
  have h0 : V [6, 1, 6, 5] = V [7, 6] :=
    relation_split _ loop67 false 4 _ _ (by decide)
  have hl : V [6, 1, 6, 5] = V [6, 1, 6, 5] :=
    rfl
  have hr : V [7, 6] = V [7, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1473 : V [5, 6, 0] = V [1, 6, 5] := by
  have h0 : V [1, 6, 5] = V [6, 7, 6] :=
    relation_split _ loop67 false 5 _ _ (by decide)
  have hl : V [1, 6, 5] = V [1, 6, 5] :=
    rfl
  have hr : V [6, 7, 6] = V [5, 6, 0] :=
    (in_context torus1469 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1474 : V [0, 6, 7, 0] = V [7, 6] := by
  have h0 : V [6, 5, 6, 0] = V [7, 6] :=
    relation_split _ loop67 true 3 _ _ (by decide)
  have hl : V [6, 5, 6, 0] = V [0, 6, 7, 0] :=
    (in_context torus1466 [] [0])
  have hr : V [7, 6] = V [7, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1475 : V [7, 6, 7] = V [0, 7, 8] := by
  have h0 : V [7, 6, 7] = V [0, 7, 8] :=
    relation_split _ loop68 false 0 _ _ (by decide)
  have hl : V [7, 6, 7] = V [7, 6, 7] :=
    rfl
  have hr : V [0, 7, 8] = V [0, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1476 : V [7, 0, 7] = V [6, 7, 8] := by
  have h0 : V [6, 7, 8] = V [7, 0, 7] :=
    relation_split _ loop68 false 1 _ _ (by decide)
  have hl : V [6, 7, 8] = V [6, 7, 8] :=
    rfl
  have hr : V [7, 0, 7] = V [7, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1477 : V [6, 7, 8, 7] = V [7, 0] := by
  have h0 : V [6, 7, 8, 7] = V [7, 0] :=
    relation_split _ loop68 false 1 _ _ (by decide)
  have hl : V [6, 7, 8, 7] = V [6, 7, 8, 7] :=
    rfl
  have hr : V [7, 0] = V [7, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1478 : V [7, 8, 7] = V [6, 7, 0] := by
  have h0 : V [7, 8, 7] = V [6, 7, 0] :=
    relation_split _ loop68 false 2 _ _ (by decide)
  have hl : V [7, 8, 7] = V [7, 8, 7] :=
    rfl
  have hr : V [6, 7, 0] = V [6, 7, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1479 : V [8, 7, 1] = V [0, 7, 8] := by
  have h0 : V [8, 7, 1] = V [7, 6, 7] :=
    relation_split _ loop68 false 3 _ _ (by decide)
  have hl : V [8, 7, 1] = V [8, 7, 1] :=
    rfl
  have hr : V [7, 6, 7] = V [0, 7, 8] :=
    (in_context torus1475 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1480 : V [8, 7, 6] = V [7, 1, 7] := by
  have h0 : V [7, 1, 7] = V [8, 7, 6] :=
    relation_split _ loop68 false 4 _ _ (by decide)
  have hl : V [7, 1, 7] = V [7, 1, 7] :=
    rfl
  have hr : V [8, 7, 6] = V [8, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1481 : V [7, 1, 7, 6] = V [8, 7] := by
  have h0 : V [7, 1, 7, 6] = V [8, 7] :=
    relation_split _ loop68 false 4 _ _ (by decide)
  have hl : V [7, 1, 7, 6] = V [7, 1, 7, 6] :=
    rfl
  have hr : V [8, 7] = V [8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1482 : V [6, 7, 0] = V [1, 7, 6] := by
  have h0 : V [1, 7, 6] = V [7, 8, 7] :=
    relation_split _ loop68 false 5 _ _ (by decide)
  have hl : V [1, 7, 6] = V [1, 7, 6] :=
    rfl
  have hr : V [7, 8, 7] = V [6, 7, 0] :=
    (in_context torus1478 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1483 : V [0, 7, 8, 0] = V [8, 7] := by
  have h0 : V [7, 6, 7, 0] = V [8, 7] :=
    relation_split _ loop68 true 3 _ _ (by decide)
  have hl : V [7, 6, 7, 0] = V [0, 7, 8, 0] :=
    (in_context torus1475 [] [0])
  have hr : V [8, 7] = V [8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1484 : V [8, 7, 8] = V [0, 8, 2] := by
  have h0 : V [8, 7, 8] = V [0, 8, 2] :=
    relation_split _ loop69 false 0 _ _ (by decide)
  have hl : V [8, 7, 8] = V [8, 7, 8] :=
    rfl
  have hr : V [0, 8, 2] = V [0, 8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1485 : V [8, 0, 8] = V [7, 8, 2] := by
  have h0 : V [7, 8, 2] = V [8, 0, 8] :=
    relation_split _ loop69 false 1 _ _ (by decide)
  have hl : V [7, 8, 2] = V [7, 8, 2] :=
    rfl
  have hr : V [8, 0, 8] = V [8, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1486 : V [7, 8, 2, 8] = V [8, 0] := by
  have h0 : V [7, 8, 2, 8] = V [8, 0] :=
    relation_split _ loop69 false 1 _ _ (by decide)
  have hl : V [7, 8, 2, 8] = V [7, 8, 2, 8] :=
    rfl
  have hr : V [8, 0] = V [8, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1487 : V [8, 2, 8] = V [7, 8, 0] := by
  have h0 : V [8, 2, 8] = V [7, 8, 0] :=
    relation_split _ loop69 false 2 _ _ (by decide)
  have hl : V [8, 2, 8] = V [8, 2, 8] :=
    rfl
  have hr : V [7, 8, 0] = V [7, 8, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1488 : V [2, 8, 1] = V [0, 8, 2] := by
  have h0 : V [2, 8, 1] = V [8, 7, 8] :=
    relation_split _ loop69 false 3 _ _ (by decide)
  have hl : V [2, 8, 1] = V [2, 8, 1] :=
    rfl
  have hr : V [8, 7, 8] = V [0, 8, 2] :=
    (in_context torus1484 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1489 : V [8, 1, 8] = V [2, 8, 7] := by
  have h0 : V [8, 1, 8] = V [2, 8, 7] :=
    relation_split _ loop69 false 4 _ _ (by decide)
  have hl : V [8, 1, 8] = V [8, 1, 8] :=
    rfl
  have hr : V [2, 8, 7] = V [2, 8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1490 : V [7, 8, 0] = V [1, 8, 7] := by
  have h0 : V [1, 8, 7] = V [8, 2, 8] :=
    relation_split _ loop69 false 5 _ _ (by decide)
  have hl : V [1, 8, 7] = V [1, 8, 7] :=
    rfl
  have hr : V [8, 2, 8] = V [7, 8, 0] :=
    (in_context torus1487 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1491 : V [2, 0, 8, 2] = V [8, 1] := by
  have h0 : V [2, 8, 7, 8] = V [8, 1] :=
    relation_split _ loop69 true 2 _ _ (by decide)
  have hl : V [2, 8, 7, 8] = V [2, 0, 8, 2] :=
    (in_context torus1484 [2] [])
  have hr : V [8, 1] = V [8, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1492 : V [3, 0, 2, 3] = V [2, 1] := by
  have h0 : V [2, 1] = V [3, 0, 2, 3] :=
    overlap torus3 torus1432 [3] [2, 1] (by decide)
  have hl : V [2, 1] = V [2, 1] :=
    rfl
  have hr : V [3, 0, 2, 3] = V [3, 0, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1494 : V [8, 1, 2, 8] = V [2, 0] := by
  have h0 : V [2, 0, 2, 2] = V [8, 1, 2, 8] :=
    overlap torus1429 torus1436 [8] [2] (by decide)
  have hl : V [2, 0, 2, 2] = V [2, 0] :=
    (in_context torus2 [2, 0] [])
  have hr : V [8, 1, 2, 8] = V [8, 1, 2, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1495 : V [4, 0, 3, 4] = V [3, 1] := by
  have h0 : V [3, 1] = V [4, 0, 3, 4] :=
    overlap torus4 torus1443 [4] [3, 1] (by decide)
  have hl : V [3, 1] = V [3, 1] :=
    rfl
  have hr : V [4, 0, 3, 4] = V [4, 0, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1496 : V [5, 0, 4, 5] = V [4, 1] := by
  have h0 : V [4, 1] = V [5, 0, 4, 5] :=
    overlap torus5 torus1452 [5] [4, 1] (by decide)
  have hl : V [4, 1] = V [4, 1] :=
    rfl
  have hr : V [5, 0, 4, 5] = V [5, 0, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1497 : V [6, 0, 5, 6] = V [5, 1] := by
  have h0 : V [5, 1] = V [6, 0, 5, 6] :=
    overlap torus6 torus1461 [6] [5, 1] (by decide)
  have hl : V [5, 1] = V [5, 1] :=
    rfl
  have hr : V [6, 0, 5, 6] = V [6, 0, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1498 : V [7, 0, 6, 7] = V [6, 1] := by
  have h0 : V [6, 1] = V [7, 0, 6, 7] :=
    overlap torus7 torus1470 [7] [6, 1] (by decide)
  have hl : V [6, 1] = V [6, 1] :=
    rfl
  have hr : V [7, 0, 6, 7] = V [7, 0, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1499 : V [8, 0, 7, 8] = V [7, 1] := by
  have h0 : V [7, 1] = V [8, 0, 7, 8] :=
    overlap torus8 torus1479 [8] [7, 1] (by decide)
  have hl : V [7, 1] = V [7, 1] :=
    rfl
  have hr : V [8, 0, 7, 8] = V [8, 0, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1500 : V [3, 0, 2] = V [2, 1, 3] := by
  have h0 : V [2, 1, 2, 2, 3] = V [3, 2, 2, 0, 2] :=
    overlap torus1434 torus1429 [3, 2] [2, 3] (by decide)
  have hl : V [2, 1, 2, 2, 3] = V [2, 1, 3] :=
    (in_context torus2 [2, 1] [3])
  have hr : V [3, 2, 2, 0, 2] = V [3, 0, 2] :=
    (in_context torus2 [3] [0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1501 : V [8, 1, 2] = V [2, 0, 8] := by
  have h0 : V [2, 0, 2, 2, 8] = V [8, 2, 2, 1, 2] :=
    overlap torus1429 torus1434 [8, 2] [2, 8] (by decide)
  have hl : V [2, 0, 2, 2, 8] = V [2, 0, 8] :=
    (in_context torus2 [2, 0] [8])
  have hr : V [8, 2, 2, 1, 2] = V [8, 1, 2] :=
    (in_context torus2 [8] [1, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1503 : V [5, 0, 4] = V [4, 1, 5] := by
  have h0 : V [5, 0, 4] = V [4, 5, 5, 1, 5] :=
    overlap torus1459 torus1462 [4, 5] [4] (by decide)
  have hl : V [5, 0, 4] = V [5, 0, 4] :=
    rfl
  have hr : V [4, 5, 5, 1, 5] = V [4, 1, 5] :=
    (in_context torus5 [4] [1, 5])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1505 : V [7, 0, 6] = V [6, 1, 7] := by
  have h0 : V [7, 0, 6] = V [6, 7, 7, 1, 7] :=
    overlap torus1477 torus1480 [6, 7] [6] (by decide)
  have hl : V [7, 0, 6] = V [7, 0, 6] :=
    rfl
  have hr : V [6, 7, 7, 1, 7] = V [6, 1, 7] :=
    (in_context torus7 [6] [1, 7])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1506 : V [8, 0, 7] = V [7, 1, 8] := by
  have h0 : V [7, 1, 8] = V [8, 0, 7] :=
    overlap torus1499 torus8 [8, 0, 7] [8] (by decide)
  have hl : V [7, 1, 8] = V [7, 1, 8] :=
    rfl
  have hr : V [8, 0, 7] = V [8, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1508 : V [4, 1, 5, 4] = V [5, 0] := by
  have h0 : V [4, 1, 4, 4, 5, 4] = V [5, 4, 4, 0] :=
    overlap torus1453 torus1450 [5, 4] [4, 5, 4] (by decide)
  have hl : V [4, 1, 4, 4, 5, 4] = V [4, 1, 5, 4] :=
    (in_context torus4 [4, 1] [5, 4])
  have hr : V [5, 4, 4, 0] = V [5, 0] :=
    (in_context torus4 [5] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1509 : V [5, 1, 6, 5] = V [6, 0] := by
  have h0 : V [5, 1, 5, 5, 6, 5] = V [6, 5, 5, 0] :=
    overlap torus1462 torus1459 [6, 5] [5, 6, 5] (by decide)
  have hl : V [5, 1, 5, 5, 6, 5] = V [5, 1, 6, 5] :=
    (in_context torus5 [5, 1] [6, 5])
  have hr : V [6, 5, 5, 0] = V [6, 0] :=
    (in_context torus5 [6] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1510 : V [6, 1, 7, 6] = V [7, 0] := by
  have h0 : V [6, 1, 6, 6, 7, 6] = V [7, 6, 6, 0] :=
    overlap torus1471 torus1468 [7, 6] [6, 7, 6] (by decide)
  have hl : V [6, 1, 6, 6, 7, 6] = V [6, 1, 7, 6] :=
    (in_context torus6 [6, 1] [7, 6])
  have hr : V [7, 6, 6, 0] = V [7, 0] :=
    (in_context torus6 [7] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1511 : V [7, 1, 8, 7] = V [8, 0] := by
  have h0 : V [7, 1, 7, 7, 8, 7] = V [8, 7, 7, 0] :=
    overlap torus1480 torus1477 [8, 7] [7, 8, 7] (by decide)
  have hl : V [7, 1, 7, 7, 8, 7] = V [7, 1, 8, 7] :=
    (in_context torus7 [7, 1] [8, 7])
  have hr : V [8, 7, 7, 0] = V [8, 0] :=
    (in_context torus7 [8] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1512 : V [2, 0, 2, 0, 3, 4] = V [8, 3] := by
  have h0 : V [8, 2, 2, 3] = V [2, 0, 2, 0, 3, 4] :=
    overlap torus1438 torus1439 [2, 0, 2] [2, 3] (by decide)
  have hl : V [8, 2, 2, 3] = V [8, 3] :=
    (in_context torus2 [8] [3])
  have hr : V [2, 0, 2, 0, 3, 4] = V [2, 0, 2, 0, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1513 : V [2, 1, 2, 1, 8, 7] = V [3, 8] := by
  have h0 : V [3, 2, 2, 8] = V [2, 1, 2, 7, 8, 0] :=
    overlap torus1435 torus1487 [2, 1, 2] [2, 8] (by decide)
  have hl : V [3, 2, 2, 8] = V [3, 8] :=
    (in_context torus2 [3] [8])
  have hr : V [2, 1, 2, 7, 8, 0] = V [2, 1, 2, 1, 8, 7] :=
    (in_context torus1490 [2, 1, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1515 : V [0, 3, 4, 2, 8] = V [3, 1, 2] := by
  have h0 : V [3, 2, 3, 2, 8] = V [4, 3, 1, 2, 8] :=
    inclusion torus151 torus1436 [4, 3] [] (by decide)
  have hl : V [3, 2, 3, 2, 8] = V [3, 1, 2] :=
    ((in_context torus1436 [3] [8]).trans (in_context torus8 [3, 1, 2] []))
  have hr : V [4, 3, 1, 2, 8] = V [0, 3, 4, 2, 8] :=
    (in_context torus1443 [] [2, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1516 : V [1, 2, 8, 3, 4] = V [2, 0, 3] := by
  have h0 : V [2, 0, 2, 2, 3] = V [8, 2, 0, 3, 4] :=
    overlap torus1429 torus1439 [8, 2] [2, 3] (by decide)
  have hl : V [2, 0, 2, 2, 3] = V [2, 0, 3] :=
    (in_context torus2 [2, 0] [3])
  have hr : V [8, 2, 0, 3, 4] = V [1, 2, 8, 3, 4] :=
    ((in_context torus1430 [] [3, 4]).trans (in_context torus1436 [] [3, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1517 : V [0, 2, 0, 3, 4] = V [2, 8, 3] := by
  have h0 : V [2, 8, 3] = V [0, 2, 0, 3, 4] :=
    overlap torus1433 torus1439 [0, 2] [3] (by decide)
  have hl : V [2, 8, 3] = V [2, 8, 3] :=
    rfl
  have hr : V [0, 2, 0, 3, 4] = V [0, 2, 0, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1518 : V [1, 3, 2, 4, 5] = V [3, 0, 4] := by
  have h0 : V [2, 3, 4, 3, 4] = V [2, 3, 0, 4, 5] :=
    inclusion torus99 torus1442 [] [4, 5] (by decide)
  have hl : V [2, 3, 4, 3, 4] = V [3, 0, 4] :=
    (in_context torus1441 [] [4])
  have hr : V [2, 3, 0, 4, 5] = V [1, 3, 2, 4, 5] :=
    (in_context torus1446 [] [4, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1519 : V [3, 1, 3, 8, 2] = V [4, 2, 1] := by
  have h0 : V [4, 3, 3, 2, 1] = V [3, 1, 3, 8, 2] :=
    overlap torus1445 torus1431 [3, 1, 3] [3, 2, 1] (by decide)
  have hl : V [4, 3, 3, 2, 1] = V [4, 2, 1] :=
    (in_context torus3 [4] [2, 1])
  have hr : V [3, 1, 3, 8, 2] = V [3, 1, 3, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1520 : V [3, 1, 2, 1, 2] = V [4, 3, 8] := by
  have h0 : V [4, 3, 8] = V [3, 1, 2, 1, 2] :=
    overlap torus1445 torus1434 [3, 1] [8] (by decide)
  have hl : V [4, 3, 8] = V [4, 3, 8] :=
    rfl
  have hr : V [3, 1, 2, 1, 2] = V [3, 1, 2, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1521 : V [1, 4, 3, 5, 6] = V [4, 0, 5] := by
  have h0 : V [3, 4, 5, 4, 5] = V [3, 4, 0, 5, 6] :=
    inclusion torus107 torus1451 [] [5, 6] (by decide)
  have hl : V [3, 4, 5, 4, 5] = V [4, 0, 5] :=
    (in_context torus1450 [] [5])
  have hr : V [3, 4, 0, 5, 6] = V [1, 4, 3, 5, 6] :=
    (in_context torus1455 [] [5, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1523 : V [1, 5, 4, 6, 7] = V [5, 0, 6] := by
  have h0 : V [4, 5, 6, 5, 6] = V [4, 5, 0, 6, 7] :=
    inclusion torus116 torus1460 [] [6, 7] (by decide)
  have hl : V [4, 5, 6, 5, 6] = V [5, 0, 6] :=
    (in_context torus1459 [] [6])
  have hr : V [4, 5, 0, 6, 7] = V [1, 5, 4, 6, 7] :=
    (in_context torus1464 [] [6, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1524 : V [5, 1, 4, 1, 4] = V [6, 5, 3] := by
  have h0 : V [6, 5, 3] = V [5, 1, 4, 1, 4] :=
    overlap torus1463 torus1453 [5, 1] [3] (by decide)
  have hl : V [6, 5, 3] = V [6, 5, 3] :=
    rfl
  have hr : V [5, 1, 4, 1, 4] = V [5, 1, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1525 : V [1, 6, 5, 7, 8] = V [6, 0, 7] := by
  have h0 : V [5, 6, 7, 6, 7] = V [5, 6, 0, 7, 8] :=
    inclusion torus125 torus1469 [] [7, 8] (by decide)
  have hl : V [5, 6, 7, 6, 7] = V [6, 0, 7] :=
    (in_context torus1468 [] [7])
  have hr : V [5, 6, 0, 7, 8] = V [1, 6, 5, 7, 8] :=
    (in_context torus1473 [] [7, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1527 : V [1, 7, 6, 8, 2] = V [7, 0, 8] := by
  have h0 : V [6, 7, 8, 7, 8] = V [6, 7, 0, 8, 2] :=
    inclusion torus134 torus1478 [] [8, 2] (by decide)
  have hl : V [6, 7, 8, 7, 8] = V [7, 0, 8] :=
    (in_context torus1477 [] [8])
  have hr : V [6, 7, 0, 8, 2] = V [1, 7, 6, 8, 2] :=
    (in_context torus1482 [] [8, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1528 : V [7, 1, 6, 1, 6] = V [8, 7, 5] := by
  have h0 : V [8, 7, 5] = V [7, 1, 6, 1, 6] :=
    overlap torus1481 torus1471 [7, 1] [5] (by decide)
  have hl : V [8, 7, 5] = V [8, 7, 5] :=
    rfl
  have hr : V [7, 1, 6, 1, 6] = V [7, 1, 6, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1529 : V [8, 7, 2, 0, 2] = V [0, 8, 3] := by
  have h0 : V [0, 8, 2, 2, 3] = V [8, 7, 2, 0, 2] :=
    overlap torus1484 torus1429 [8, 7] [2, 3] (by decide)
  have hl : V [0, 8, 2, 2, 3] = V [0, 8, 3] :=
    (in_context torus2 [0, 8] [3])
  have hr : V [8, 7, 2, 0, 2] = V [8, 7, 2, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1531 : V [0, 2, 3, 8, 7] = V [2, 1, 8] := by
  have h0 : V [2, 1, 2, 2, 8] = V [3, 2, 7, 8, 0] :=
    overlap torus1434 torus1487 [3, 2] [2, 8] (by decide)
  have hl : V [2, 1, 2, 2, 8] = V [2, 1, 8] :=
    (in_context torus2 [2, 1] [8])
  have hr : V [3, 2, 7, 8, 0] = V [0, 2, 3, 8, 7] :=
    ((in_context torus1490 [3, 2] []).trans (in_context torus1432 [] [8, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1538 : V [6, 1, 6, 1, 6] = V [7, 0, 5] := by
  have h0 : V [7, 0, 5] = V [6, 1, 6, 1, 6] :=
    overlap torus1510 torus1471 [6, 1] [5] (by decide)
  have hl : V [7, 0, 5] = V [7, 0, 5] :=
    rfl
  have hr : V [6, 1, 6, 1, 6] = V [6, 1, 6, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1540 : V [2, 1, 2, 7, 8] = V [3, 8, 1] := by
  have h0 : V [3, 8, 1] = V [2, 1, 2, 1, 0, 7, 8] :=
    overlap torus1513 torus1479 [2, 1, 2, 1] [1] (by decide)
  have hl : V [3, 8, 1] = V [3, 8, 1] :=
    rfl
  have hr : V [2, 1, 2, 1, 0, 7, 8] = V [2, 1, 2, 7, 8] :=
    (in_context torus1 [2, 1, 2] [7, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1541 : V [3, 1, 2, 8] = V [0, 3, 4, 2] := by
  have h0 : V [3, 2, 3, 2, 8, 8] = V [4, 3, 2, 2, 1, 2] :=
    overlap torus151 torus1434 [4, 3, 2] [8] (by decide)
  have hl : V [3, 2, 3, 2, 8, 8] = V [3, 1, 2, 8] :=
    ((in_context torus1434 [3, 2] [8]).trans (in_context torus2 [3] [1, 2, 8]))
  have hr : V [4, 3, 2, 2, 1, 2] = V [0, 3, 4, 2] :=
    ((in_context torus2 [4, 3] [1, 2]).trans (in_context torus1443 [] [2]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1543 : V [3, 0, 8, 2] = V [2, 1, 2, 1] := by
  have h0 : V [3, 2, 2, 8, 7, 8] = V [2, 1, 2, 3, 4, 3, 2, 3] :=
    overlap torus1435 torus138 [2, 1, 2] [2, 8, 7, 8] (by decide)
  have hl : V [3, 2, 2, 8, 7, 8] = V [3, 0, 8, 2] :=
    ((in_context torus2 [3] [8, 7, 8]).trans (in_context torus1484 [3] []))
  have hr : V [2, 1, 2, 3, 4, 3, 2, 3] = V [2, 1, 2, 1] :=
    ((in_context torus146 [2, 1, 2] []).trans ((in_context torus2 [2, 1] [3, 2, 8, 2]).trans ((in_context torus1434 [2, 1] [2]).trans (in_context torus2 [2, 1, 2, 1] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1544 : V [2, 0, 3, 4] = V [1, 2, 8, 3] := by
  have h0 : V [1, 2, 8, 3] = V [2, 0, 3, 4] :=
    overlap torus1436 torus1439 [2] [3] (by decide)
  have hl : V [1, 2, 8, 3] = V [1, 2, 8, 3] :=
    rfl
  have hr : V [2, 0, 3, 4] = V [2, 0, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1545 : V [2, 8, 3, 0] = V [0, 2, 4, 3] := by
  have h0 : V [0, 2, 3, 3, 4, 3] = V [2, 8, 3, 0] :=
    overlap torus1428 torus1441 [2, 8] [3, 4, 3] (by decide)
  have hl : V [0, 2, 3, 3, 4, 3] = V [0, 2, 4, 3] :=
    (in_context torus3 [0, 2] [4, 3])
  have hr : V [2, 8, 3, 0] = V [2, 8, 3, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1546 : V [5, 1, 4, 3] = V [0, 5, 6, 4] := by
  have h0 : V [6, 5, 4, 5, 4, 3] = V [5, 3, 4, 3, 3, 0] :=
    overlap torus113 torus1441 [5, 3, 4, 3] [4, 3] (by decide)
  have hl : V [6, 5, 4, 5, 4, 3] = V [0, 5, 6, 4] :=
    ((in_context torus112 [] [3]).trans ((in_context torus3 [5, 4, 5, 4] []).trans (in_context torus1457 [] [4])))
  have hr : V [5, 3, 4, 3, 3, 0] = V [5, 1, 4, 3] :=
    ((in_context torus3 [5, 3, 4] [0]).trans (in_context torus1455 [5] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1547 : V [5, 1, 5, 1, 4] = V [6, 4, 3] := by
  have h0 : V [6, 0, 1, 4, 3] = V [5, 1, 6, 0, 5, 6, 4] :=
    overlap torus1509 torus1546 [5, 1, 6] [1, 4, 3] (by decide)
  have hl : V [6, 0, 1, 4, 3] = V [6, 4, 3] :=
    (in_context torus0 [6] [4, 3])
  have hr : V [5, 1, 6, 0, 5, 6, 4] = V [5, 1, 5, 1, 4] :=
    (in_context torus1497 [5, 1] [4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1549 : V [8, 2, 4, 3] = V [2, 0, 3, 0] := by
  have h0 : V [8, 2, 4, 3] = V [2, 0, 3, 0] :=
    overlap torus1438 torus1441 [2, 0] [4, 3] (by decide)
  have hl : V [8, 2, 4, 3] = V [8, 2, 4, 3] :=
    rfl
  have hr : V [2, 0, 3, 0] = V [2, 0, 3, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1550 : V [3, 0, 4, 5] = V [1, 3, 2, 4] := by
  have h0 : V [3, 0, 4, 5] = V [2, 2, 3, 4, 3, 4] :=
    overlap torus1441 torus99 [2] [4, 5] (by decide)
  have hl : V [3, 0, 4, 5] = V [3, 0, 4, 5] :=
    rfl
  have hr : V [2, 2, 3, 4, 3, 4] = V [1, 3, 2, 4] :=
    ((in_context torus2 [] [3, 4, 3, 4]).trans ((in_context torus1442 [] [4]).trans (in_context torus1446 [] [4])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1553 : V [4, 2, 1, 2] = V [3, 1, 3, 8] := by
  have h0 : V [3, 1, 3, 8] = V [4, 2, 1, 2] :=
    overlap torus1444 torus1434 [4] [8] (by decide)
  have hl : V [3, 1, 3, 8] = V [3, 1, 3, 8] :=
    rfl
  have hr : V [4, 2, 1, 2] = V [4, 2, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1554 : V [4, 1, 3, 2] = V [0, 4, 5, 3] := by
  have h0 : V [4, 3, 4, 3, 2, 2] = V [5, 4, 3, 3, 1, 3] :=
    overlap torus104 torus1444 [5, 4, 3] [2] (by decide)
  have hl : V [4, 3, 4, 3, 2, 2] = V [4, 1, 3, 2] :=
    ((in_context torus1442 [4] [2, 2]).trans ((in_context torus2 [4, 2, 3, 0] []).trans (in_context torus1446 [4] [])))
  have hr : V [5, 4, 3, 3, 1, 3] = V [0, 4, 5, 3] :=
    ((in_context torus3 [5, 4] [1, 3]).trans (in_context torus1452 [] [3]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1555 : V [4, 1, 4, 1, 3] = V [5, 3, 2] := by
  have h0 : V [5, 0, 1, 3, 2] = V [4, 1, 5, 0, 4, 5, 3] :=
    overlap torus1508 torus1554 [4, 1, 5] [1, 3, 2] (by decide)
  have hl : V [5, 0, 1, 3, 2] = V [5, 3, 2] :=
    (in_context torus0 [5] [3, 2])
  have hr : V [4, 1, 5, 0, 4, 5, 3] = V [4, 1, 4, 1, 3] :=
    (in_context torus1496 [4, 1] [3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1557 : V [8, 1, 3, 2] = V [2, 0, 2, 0] := by
  have h0 : V [2, 0, 2, 0] = V [8, 1, 3, 2] :=
    overlap torus1429 torus1446 [8] [0] (by decide)
  have hl : V [2, 0, 2, 0] = V [2, 0, 2, 0] :=
    rfl
  have hr : V [8, 1, 3, 2] = V [8, 1, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1558 : V [1, 8, 7, 2, 0] = V [8, 3, 2] := by
  have h0 : V [8, 0, 1, 3, 2] = V [7, 8, 2, 2, 0, 2, 0] :=
    overlap torus1486 torus1557 [7, 8, 2] [1, 3, 2] (by decide)
  have hl : V [8, 0, 1, 3, 2] = V [8, 3, 2] :=
    (in_context torus0 [8] [3, 2])
  have hr : V [7, 8, 2, 2, 0, 2, 0] = V [1, 8, 7, 2, 0] :=
    ((in_context torus2 [7, 8] [0, 2, 0]).trans (in_context torus1490 [] [2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1559 : V [3, 2, 4, 0] = V [0, 3, 5, 4] := by
  have h0 : V [0, 3, 4, 4, 5, 4] = V [3, 2, 4, 0] :=
    overlap torus1439 torus1450 [3, 2] [4, 5, 4] (by decide)
  have hl : V [0, 3, 4, 4, 5, 4] = V [0, 3, 5, 4] :=
    (in_context torus4 [0, 3] [5, 4])
  have hr : V [3, 2, 4, 0] = V [3, 2, 4, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1561 : V [4, 0, 5, 6] = V [1, 4, 3, 5] := by
  have h0 : V [4, 0, 5, 6] = V [3, 3, 4, 5, 4, 5] :=
    overlap torus1450 torus107 [3] [5, 6] (by decide)
  have hl : V [4, 0, 5, 6] = V [4, 0, 5, 6] :=
    rfl
  have hr : V [3, 3, 4, 5, 4, 5] = V [1, 4, 3, 5] :=
    ((in_context torus3 [] [4, 5, 4, 5]).trans ((in_context torus1451 [] [5]).trans (in_context torus1455 [] [5])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1562 : V [5, 0, 3, 4] = V [4, 1, 4, 1] := by
  have h0 : V [4, 1, 4, 4, 5, 4, 3, 4] = V [5, 4, 4, 3, 2, 3] :=
    overlap torus1453 torus102 [5, 4] [4, 5, 4, 3, 4] (by decide)
  have hl : V [4, 1, 4, 4, 5, 4, 3, 4] = V [4, 1, 4, 1] :=
    ((in_context torus4 [4, 1] [5, 4, 3, 4]).trans ((in_context torus1453 [4, 1] [4]).trans (in_context torus4 [4, 1, 4, 1] [])))
  have hr : V [5, 4, 4, 3, 2, 3] = V [5, 0, 3, 4] :=
    ((in_context torus4 [5] [3, 2, 3]).trans (in_context torus1439 [5] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1563 : V [5, 3, 1, 3] = V [4, 1, 4, 2] := by
  have h0 : V [4, 1, 4, 2] = V [5, 3, 1, 3] :=
    overlap torus1453 torus1444 [5] [2] (by decide)
  have hl : V [4, 1, 4, 2] = V [4, 1, 4, 2] :=
    rfl
  have hr : V [5, 3, 1, 3] = V [5, 3, 1, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1564 : V [4, 3, 5, 0] = V [0, 4, 6, 5] := by
  have h0 : V [0, 4, 5, 5, 6, 5] = V [4, 3, 5, 0] :=
    overlap torus1448 torus1459 [4, 3] [5, 6, 5] (by decide)
  have hl : V [0, 4, 5, 5, 6, 5] = V [0, 4, 6, 5] :=
    (in_context torus5 [0, 4] [6, 5])
  have hr : V [4, 3, 5, 0] = V [4, 3, 5, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1566 : V [5, 0, 6, 7] = V [1, 5, 4, 6] := by
  have h0 : V [5, 0, 6, 7] = V [4, 4, 5, 6, 5, 6] :=
    overlap torus1459 torus116 [4] [6, 7] (by decide)
  have hl : V [5, 0, 6, 7] = V [5, 0, 6, 7] :=
    rfl
  have hr : V [4, 4, 5, 6, 5, 6] = V [1, 5, 4, 6] :=
    ((in_context torus4 [] [5, 6, 5, 6]).trans ((in_context torus1460 [] [6]).trans (in_context torus1464 [] [6])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1567 : V [6, 0, 4, 5] = V [5, 1, 5, 1] := by
  have h0 : V [5, 1, 5, 3, 4, 3, 2, 3] = V [6, 5, 5, 4, 3, 4] :=
    overlap torus1462 torus105 [6, 5] [3, 4, 3, 2, 3] (by decide)
  have hl : V [5, 1, 5, 3, 4, 3, 2, 3] = V [5, 1, 5, 1] :=
    ((in_context torus113 [5, 1] []).trans ((in_context torus1462 [5, 1] [5]).trans (in_context torus5 [5, 1, 5, 1] [])))
  have hr : V [6, 5, 5, 4, 3, 4] = V [6, 0, 4, 5] :=
    ((in_context torus5 [6] [4, 3, 4]).trans (in_context torus1448 [6] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1568 : V [6, 4, 1, 4] = V [5, 1, 5, 3] := by
  have h0 : V [5, 1, 5, 3] = V [6, 4, 1, 4] :=
    overlap torus1462 torus1453 [6] [3] (by decide)
  have hl : V [5, 1, 5, 3] = V [5, 1, 5, 3] :=
    rfl
  have hr : V [6, 4, 1, 4] = V [6, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1569 : V [6, 1, 5, 4] = V [0, 6, 7, 5] := by
  have h0 : V [6, 5, 6, 5, 4, 4] = V [7, 6, 5, 5, 1, 5] :=
    overlap torus121 torus1462 [7, 6, 5] [4] (by decide)
  have hl : V [6, 5, 6, 5, 4, 4] = V [6, 1, 5, 4] :=
    ((in_context torus1460 [6] [4, 4]).trans ((in_context torus4 [6, 4, 5, 0] []).trans (in_context torus1464 [6] [])))
  have hr : V [7, 6, 5, 5, 1, 5] = V [0, 6, 7, 5] :=
    ((in_context torus5 [7, 6] [1, 5]).trans (in_context torus1470 [] [5]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1570 : V [6, 1, 6, 1, 5] = V [7, 5, 4] := by
  have h0 : V [7, 0, 1, 5, 4] = V [6, 1, 7, 0, 6, 7, 5] :=
    overlap torus1510 torus1569 [6, 1, 7] [1, 5, 4] (by decide)
  have hl : V [7, 0, 1, 5, 4] = V [7, 5, 4] :=
    (in_context torus0 [7] [5, 4])
  have hr : V [6, 1, 7, 0, 6, 7, 5] = V [6, 1, 6, 1, 5] :=
    (in_context torus1498 [6, 1] [5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1572 : V [5, 4, 6, 0] = V [0, 5, 7, 6] := by
  have h0 : V [0, 5, 6, 6, 7, 6] = V [5, 4, 6, 0] :=
    overlap torus1457 torus1468 [5, 4] [6, 7, 6] (by decide)
  have hl : V [0, 5, 6, 6, 7, 6] = V [0, 5, 7, 6] :=
    (in_context torus6 [0, 5] [7, 6])
  have hr : V [5, 4, 6, 0] = V [5, 4, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1573 : V [5, 0, 6, 0] = V [4, 5, 7, 6] := by
  have h0 : V [4, 5, 6, 6, 7, 6] = V [5, 0, 6, 0] :=
    overlap torus1458 torus1468 [5, 0] [6, 7, 6] (by decide)
  have hl : V [4, 5, 6, 6, 7, 6] = V [4, 5, 7, 6] :=
    (in_context torus6 [4, 5] [7, 6])
  have hr : V [5, 0, 6, 0] = V [5, 0, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1574 : V [6, 0, 7, 8] = V [1, 6, 5, 7] := by
  have h0 : V [6, 0, 7, 8] = V [5, 5, 6, 7, 6, 7] :=
    overlap torus1468 torus125 [5] [7, 8] (by decide)
  have hl : V [6, 0, 7, 8] = V [6, 0, 7, 8] :=
    rfl
  have hr : V [5, 5, 6, 7, 6, 7] = V [1, 6, 5, 7] :=
    ((in_context torus5 [] [6, 7, 6, 7]).trans ((in_context torus1469 [] [7]).trans (in_context torus1473 [] [7])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1576 : V [7, 5, 1, 5] = V [6, 1, 6, 4] := by
  have h0 : V [6, 1, 6, 4] = V [7, 5, 1, 5] :=
    overlap torus1471 torus1462 [7] [4] (by decide)
  have hl : V [6, 1, 6, 4] = V [6, 1, 6, 4] :=
    rfl
  have hr : V [7, 5, 1, 5] = V [7, 5, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1577 : V [7, 1, 6, 5] = V [0, 7, 8, 6] := by
  have h0 : V [7, 6, 7, 6, 5, 5] = V [8, 7, 6, 6, 1, 6] :=
    overlap torus130 torus1471 [8, 7, 6] [5] (by decide)
  have hl : V [7, 6, 7, 6, 5, 5] = V [7, 1, 6, 5] :=
    ((in_context torus1469 [7] [5, 5]).trans ((in_context torus5 [7, 5, 6, 0] []).trans (in_context torus1473 [7] [])))
  have hr : V [8, 7, 6, 6, 1, 6] = V [0, 7, 8, 6] :=
    ((in_context torus6 [8, 7] [1, 6]).trans (in_context torus1479 [] [6]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1578 : V [7, 1, 7, 1, 6] = V [8, 6, 5] := by
  have h0 : V [8, 0, 1, 6, 5] = V [7, 1, 8, 0, 7, 8, 6] :=
    overlap torus1511 torus1577 [7, 1, 8] [1, 6, 5] (by decide)
  have hl : V [8, 0, 1, 6, 5] = V [8, 6, 5] :=
    (in_context torus0 [8] [6, 5])
  have hr : V [7, 1, 8, 0, 7, 8, 6] = V [7, 1, 7, 1, 6] :=
    (in_context torus1499 [7, 1] [6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1579 : V [7, 1, 7, 5, 6] = V [8, 6, 1] := by
  have h0 : V [8, 6, 5, 5, 1] = V [7, 1, 7, 1, 0, 5, 6] :=
    overlap torus1578 torus1461 [7, 1, 7, 1] [5, 1] (by decide)
  have hl : V [8, 6, 5, 5, 1] = V [8, 6, 1] :=
    (in_context torus5 [8, 6] [1])
  have hr : V [7, 1, 7, 1, 0, 5, 6] = V [7, 1, 7, 5, 6] :=
    (in_context torus1 [7, 1, 7] [5, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1580 : V [6, 5, 7, 0] = V [0, 6, 8, 7] := by
  have h0 : V [0, 6, 7, 7, 8, 7] = V [6, 5, 7, 0] :=
    overlap torus1466 torus1477 [6, 5] [7, 8, 7] (by decide)
  have hl : V [0, 6, 7, 7, 8, 7] = V [0, 6, 8, 7] :=
    (in_context torus7 [0, 6] [8, 7])
  have hr : V [6, 5, 7, 0] = V [6, 5, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1581 : V [6, 0, 7, 0] = V [5, 6, 8, 7] := by
  have h0 : V [5, 6, 7, 7, 8, 7] = V [6, 0, 7, 0] :=
    overlap torus1467 torus1477 [6, 0] [7, 8, 7] (by decide)
  have hl : V [5, 6, 7, 7, 8, 7] = V [5, 6, 8, 7] :=
    (in_context torus7 [5, 6] [8, 7])
  have hr : V [6, 0, 7, 0] = V [6, 0, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1582 : V [7, 0, 8, 2] = V [1, 7, 6, 8] := by
  have h0 : V [7, 0, 8, 2] = V [6, 6, 7, 8, 7, 8] :=
    overlap torus1477 torus134 [6] [8, 2] (by decide)
  have hl : V [7, 0, 8, 2] = V [7, 0, 8, 2] :=
    rfl
  have hr : V [6, 6, 7, 8, 7, 8] = V [1, 7, 6, 8] :=
    ((in_context torus6 [] [7, 8, 7, 8]).trans ((in_context torus1478 [] [8]).trans (in_context torus1482 [] [8])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1583 : V [8, 0, 6, 7] = V [7, 1, 7, 1] := by
  have h0 : V [7, 1, 7, 3, 4, 3, 2, 3] = V [8, 7, 7, 6, 5, 6] :=
    overlap torus1480 torus122 [8, 7] [3, 4, 3, 2, 3] (by decide)
  have hl : V [7, 1, 7, 3, 4, 3, 2, 3] = V [7, 1, 7, 1] :=
    ((in_context torus131 [7, 1] []).trans ((in_context torus1480 [7, 1] [7]).trans (in_context torus7 [7, 1, 7, 1] [])))
  have hr : V [8, 7, 7, 6, 5, 6] = V [8, 0, 6, 7] :=
    ((in_context torus7 [8] [6, 5, 6]).trans (in_context torus1466 [8] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1584 : V [8, 6, 1, 6] = V [7, 1, 7, 5] := by
  have h0 : V [7, 1, 7, 5] = V [8, 6, 1, 6] :=
    overlap torus1480 torus1471 [8] [5] (by decide)
  have hl : V [7, 1, 7, 5] = V [7, 1, 7, 5] :=
    rfl
  have hr : V [8, 6, 1, 6] = V [8, 6, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1585 : V [8, 1, 7, 6] = V [0, 8, 2, 7] := by
  have h0 : V [0, 8, 2, 7] = V [8, 6, 7, 0] :=
    overlap torus1484 torus1478 [8] [7] (by decide)
  have hl : V [0, 8, 2, 7] = V [0, 8, 2, 7] :=
    rfl
  have hr : V [8, 6, 7, 0] = V [8, 1, 7, 6] :=
    (in_context torus1482 [8] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1586 : V [8, 0, 2, 3] = V [1, 8, 7, 2] := by
  have h0 : V [8, 0, 2, 3] = V [7, 8, 2, 2, 0, 2] :=
    overlap torus1486 torus1429 [7, 8, 2] [2, 3] (by decide)
  have hl : V [8, 0, 2, 3] = V [8, 0, 2, 3] :=
    rfl
  have hr : V [7, 8, 2, 2, 0, 2] = V [1, 8, 7, 2] :=
    ((in_context torus2 [7, 8] [0, 2]).trans (in_context torus1490 [] [2]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1587 : V [8, 0, 2, 0] = V [7, 8, 3, 2] := by
  have h0 : V [8, 0, 2, 0] = V [7, 8, 2, 2, 3, 2] :=
    overlap torus1486 torus1430 [7, 8, 2] [2, 0] (by decide)
  have hl : V [8, 0, 2, 0] = V [8, 0, 2, 0] :=
    rfl
  have hr : V [7, 8, 2, 2, 3, 2] = V [7, 8, 3, 2] :=
    (in_context torus2 [7, 8] [3, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1588 : V [7, 6, 8, 0] = V [0, 7, 2, 8] := by
  have h0 : V [0, 7, 8, 8, 2, 8] = V [7, 6, 8, 0] :=
    overlap torus1475 torus1486 [7, 6] [8, 2, 8] (by decide)
  have hl : V [0, 7, 8, 8, 2, 8] = V [0, 7, 2, 8] :=
    (in_context torus8 [0, 7] [2, 8])
  have hr : V [7, 6, 8, 0] = V [7, 6, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1589 : V [7, 0, 8, 0] = V [6, 7, 2, 8] := by
  have h0 : V [6, 7, 8, 8, 2, 8] = V [7, 0, 8, 0] :=
    overlap torus1476 torus1486 [7, 0] [8, 2, 8] (by decide)
  have hl : V [6, 7, 8, 8, 2, 8] = V [6, 7, 2, 8] :=
    (in_context torus8 [6, 7] [2, 8])
  have hr : V [7, 0, 8, 0] = V [7, 0, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1590 : V [2, 1, 8, 7] = V [0, 2, 3, 8] := by
  have h0 : V [0, 2, 3, 8] = V [2, 7, 8, 0] :=
    overlap torus1428 torus1487 [2] [8] (by decide)
  have hl : V [0, 2, 3, 8] = V [0, 2, 3, 8] :=
    rfl
  have hr : V [2, 7, 8, 0] = V [2, 1, 8, 7] :=
    (in_context torus1490 [2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1591 : V [2, 3, 8, 1] = V [1, 2, 7, 8] := by
  have h0 : V [1, 2, 8, 0, 8, 2] = V [2, 3, 8, 1] :=
    overlap torus1436 torus1491 [2, 3] [0, 8, 2] (by decide)
  have hl : V [1, 2, 8, 0, 8, 2] = V [1, 2, 7, 8] :=
    ((in_context torus1485 [1, 2] [2]).trans (in_context torus2 [1, 2, 7, 8] []))
  have hr : V [2, 3, 8, 1] = V [2, 3, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1592 : V [3, 4, 2, 1] = V [1, 3, 8, 2] := by
  have h0 : V [2, 3, 0, 0, 2, 3] = V [3, 4, 2, 1] :=
    overlap torus1442 torus1492 [3, 4] [0, 2, 3] (by decide)
  have hl : V [2, 3, 0, 0, 2, 3] = V [1, 3, 8, 2] :=
    ((in_context torus1446 [] [0, 2, 3]).trans (in_context torus1438 [1, 3] []))
  have hr : V [3, 4, 2, 1] = V [3, 4, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1593 : V [8, 7, 2, 0] = V [0, 8, 3, 2] := by
  have h0 : V [0, 8, 2, 1, 2, 8] = V [8, 7, 2, 0] :=
    overlap torus1484 torus1494 [8, 7] [1, 2, 8] (by decide)
  have hl : V [0, 8, 2, 1, 2, 8] = V [0, 8, 3, 2] :=
    (in_context torus1435 [0, 8] [])
  have hr : V [8, 7, 2, 0] = V [8, 7, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1594 : V [4, 5, 3, 1] = V [1, 4, 2, 3] := by
  have h0 : V [3, 4, 0, 0, 3, 4] = V [4, 5, 3, 1] :=
    overlap torus1451 torus1495 [4, 5] [0, 3, 4] (by decide)
  have hl : V [3, 4, 0, 0, 3, 4] = V [1, 4, 2, 3] :=
    ((in_context torus1455 [] [0, 3, 4]).trans ((in_context torus1440 [1, 4] [4]).trans (in_context torus4 [1, 4, 2, 3] [])))
  have hr : V [4, 5, 3, 1] = V [4, 5, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1595 : V [5, 6, 4, 1] = V [1, 5, 3, 4] := by
  have h0 : V [4, 5, 0, 0, 4, 5] = V [5, 6, 4, 1] :=
    overlap torus1460 torus1496 [5, 6] [0, 4, 5] (by decide)
  have hl : V [4, 5, 0, 0, 4, 5] = V [1, 5, 3, 4] :=
    ((in_context torus1464 [] [0, 4, 5]).trans ((in_context torus1449 [1, 5] [5]).trans (in_context torus5 [1, 5, 3, 4] [])))
  have hr : V [5, 6, 4, 1] = V [5, 6, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1596 : V [6, 7, 5, 1] = V [1, 6, 4, 5] := by
  have h0 : V [5, 6, 0, 0, 5, 6] = V [6, 7, 5, 1] :=
    overlap torus1469 torus1497 [6, 7] [0, 5, 6] (by decide)
  have hl : V [5, 6, 0, 0, 5, 6] = V [1, 6, 4, 5] :=
    ((in_context torus1473 [] [0, 5, 6]).trans ((in_context torus1458 [1, 6] [6]).trans (in_context torus6 [1, 6, 4, 5] [])))
  have hr : V [6, 7, 5, 1] = V [6, 7, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1597 : V [7, 8, 6, 1] = V [1, 7, 5, 6] := by
  have h0 : V [6, 7, 0, 0, 6, 7] = V [7, 8, 6, 1] :=
    overlap torus1478 torus1498 [7, 8] [0, 6, 7] (by decide)
  have hl : V [6, 7, 0, 0, 6, 7] = V [1, 7, 5, 6] :=
    ((in_context torus1482 [] [0, 6, 7]).trans ((in_context torus1467 [1, 7] [7]).trans (in_context torus7 [1, 7, 5, 6] [])))
  have hr : V [7, 8, 6, 1] = V [7, 8, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1598 : V [8, 2, 7, 1] = V [1, 8, 6, 7] := by
  have h0 : V [7, 8, 0, 0, 7, 8] = V [8, 2, 7, 1] :=
    overlap torus1487 torus1499 [8, 2] [0, 7, 8] (by decide)
  have hl : V [7, 8, 0, 0, 7, 8] = V [1, 8, 6, 7] :=
    ((in_context torus1490 [] [0, 7, 8]).trans ((in_context torus1476 [1, 8] [8]).trans (in_context torus8 [1, 8, 6, 7] [])))
  have hr : V [8, 2, 7, 1] = V [8, 2, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1599 : V [8, 1, 7, 1] = V [2, 8, 6, 7] := by
  have h0 : V [2, 8, 7, 0, 7, 8] = V [8, 1, 7, 1] :=
    overlap torus1489 torus1499 [8, 1] [0, 7, 8] (by decide)
  have hl : V [2, 8, 7, 0, 7, 8] = V [2, 8, 6, 7] :=
    ((in_context torus1476 [2, 8] [8]).trans (in_context torus8 [2, 8, 6, 7] []))
  have hr : V [8, 1, 7, 1] = V [8, 1, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1603 : V [4, 3, 5, 6] = V [0, 4, 0, 5] := by
  have h0 : V [4, 3, 5, 6] = V [0, 4, 0, 5] :=
    overlap torus0 torus1521 [0] [4, 3, 5, 6] (by decide)
  have hl : V [4, 3, 5, 6] = V [4, 3, 5, 6] :=
    rfl
  have hr : V [0, 4, 0, 5] = V [0, 4, 0, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1605 : V [5, 4, 6, 7] = V [0, 5, 0, 6] := by
  have h0 : V [5, 4, 6, 7] = V [0, 5, 0, 6] :=
    overlap torus0 torus1523 [0] [5, 4, 6, 7] (by decide)
  have hl : V [5, 4, 6, 7] = V [5, 4, 6, 7] :=
    rfl
  have hr : V [0, 5, 0, 6] = V [0, 5, 0, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1606 : V [6, 5, 3, 4] = V [5, 1, 4, 1] := by
  have h0 : V [6, 5, 3, 4] = V [5, 1, 4, 1] :=
    overlap torus1524 torus4 [5, 1, 4, 1] [4] (by decide)
  have hl : V [6, 5, 3, 4] = V [6, 5, 3, 4] :=
    rfl
  have hr : V [5, 1, 4, 1] = V [5, 1, 4, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1607 : V [6, 5, 7, 8] = V [0, 6, 0, 7] := by
  have h0 : V [6, 5, 7, 8] = V [0, 6, 0, 7] :=
    overlap torus0 torus1525 [0] [6, 5, 7, 8] (by decide)
  have hl : V [6, 5, 7, 8] = V [6, 5, 7, 8] :=
    rfl
  have hr : V [0, 6, 0, 7] = V [0, 6, 0, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1609 : V [7, 6, 8, 2] = V [0, 7, 0, 8] := by
  have h0 : V [7, 6, 8, 2] = V [0, 7, 0, 8] :=
    overlap torus0 torus1527 [0] [7, 6, 8, 2] (by decide)
  have hl : V [7, 6, 8, 2] = V [7, 6, 8, 2] :=
    rfl
  have hr : V [0, 7, 0, 8] = V [0, 7, 0, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1610 : V [8, 7, 5, 6] = V [7, 1, 6, 1] := by
  have h0 : V [8, 7, 5, 6] = V [7, 1, 6, 1] :=
    overlap torus1528 torus6 [7, 1, 6, 1] [6] (by decide)
  have hl : V [8, 7, 5, 6] = V [8, 7, 5, 6] :=
    rfl
  have hr : V [7, 1, 6, 1] = V [7, 1, 6, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1611 : V [2, 3, 8, 7] = V [1, 2, 1, 8] := by
  have h0 : V [2, 3, 8, 7] = V [1, 2, 1, 8] :=
    overlap torus1 torus1531 [1] [2, 3, 8, 7] (by decide)
  have hl : V [2, 3, 8, 7] = V [2, 3, 8, 7] :=
    rfl
  have hr : V [1, 2, 1, 8] = V [1, 2, 1, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1612 : V [3, 2, 7, 8] = V [2, 1, 8, 1] := by
  have h0 : V [2, 1, 8, 1] = V [0, 2, 3, 0, 7, 8] :=
    overlap torus1531 torus1479 [0, 2, 3] [1] (by decide)
  have hl : V [2, 1, 8, 1] = V [2, 1, 8, 1] :=
    rfl
  have hr : V [0, 2, 3, 0, 7, 8] = V [3, 2, 7, 8] :=
    (in_context torus1437 [] [7, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1613 : V [5, 6, 4, 3] = V [1, 5, 1, 4] := by
  have h0 : V [1, 5, 1, 4] = V [5, 6, 4, 3] :=
    overlap torus5 torus1547 [5] [1, 5, 1, 4] (by decide)
  have hl : V [1, 5, 1, 4] = V [1, 5, 1, 4] :=
    rfl
  have hr : V [5, 6, 4, 3] = V [5, 6, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1614 : V [4, 5, 3, 2] = V [1, 4, 1, 3] := by
  have h0 : V [1, 4, 1, 3] = V [4, 5, 3, 2] :=
    overlap torus4 torus1555 [4] [1, 4, 1, 3] (by decide)
  have hl : V [1, 4, 1, 3] = V [1, 4, 1, 3] :=
    rfl
  have hr : V [4, 5, 3, 2] = V [4, 5, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1615 : V [6, 7, 5, 4] = V [1, 6, 1, 5] := by
  have h0 : V [1, 6, 1, 5] = V [6, 7, 5, 4] :=
    overlap torus6 torus1570 [6] [1, 6, 1, 5] (by decide)
  have hl : V [1, 6, 1, 5] = V [1, 6, 1, 5] :=
    rfl
  have hr : V [6, 7, 5, 4] = V [6, 7, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1616 : V [7, 8, 6, 5] = V [1, 7, 1, 6] := by
  have h0 : V [1, 7, 1, 6] = V [7, 8, 6, 5] :=
    overlap torus7 torus1578 [7] [1, 7, 1, 6] (by decide)
  have hl : V [1, 7, 1, 6] = V [1, 7, 1, 6] :=
    rfl
  have hr : V [7, 8, 6, 5] = V [7, 8, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1617 : V [8, 7, 2, 3] = V [0, 8, 0, 2] := by
  have h0 : V [8, 7, 2, 3] = V [0, 7, 1, 8, 7, 2] :=
    overlap torus1483 torus1586 [0, 7] [2, 3] (by decide)
  have hl : V [8, 7, 2, 3] = V [8, 7, 2, 3] :=
    rfl
  have hr : V [0, 7, 1, 8, 7, 2] = V [0, 8, 0, 2] :=
    (in_context torus1511 [0] [2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1619 : V [2, 0, 2, 4, 3] = V [8, 3, 0] := by
  have h0 : V [2, 0, 2, 4, 3] = V [8, 3, 0] :=
    overlap torus1429 torus1441 [8] [4, 3] (by decide)
  have hl : V [2, 0, 2, 4, 3] = V [2, 0, 2, 4, 3] :=
    rfl
  have hr : V [8, 3, 0] = V [8, 3, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1620 : V [0, 8, 2, 7, 6] = V [8, 1, 7] := by
  have h0 : V [2, 8, 7, 8, 7] = V [8, 7, 7, 1, 7] :=
    inclusion torus139 torus1480 [8, 7] [] (by decide)
  have hl : V [2, 8, 7, 8, 7] = V [0, 8, 2, 7, 6] :=
    ((in_context torus1478 [2, 8] []).trans ((in_context torus1482 [2, 8] []).trans (in_context torus1488 [] [7, 6])))
  have hr : V [8, 7, 7, 1, 7] = V [8, 1, 7] :=
    (in_context torus7 [8] [1, 7])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1621 : V [8, 2, 7, 6] = V [1, 8, 1, 7] := by
  have h0 : V [8, 2, 7, 6] = V [1, 8, 1, 7] :=
    overlap torus1 torus1620 [1] [8, 2, 7, 6] (by decide)
  have hl : V [8, 2, 7, 6] = V [8, 2, 7, 6] :=
    rfl
  have hr : V [1, 8, 1, 7] = V [1, 8, 1, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1623 : V [5, 1, 2, 4, 2, 7, 1, 7] = V [3, 5] := by
  have h0 : V [6, 5, 5, 6, 3, 5] = V [5, 1, 2, 4, 2, 8, 7, 6] :=
    overlap torus1463 torus184 [5, 1] [5, 6, 3, 5] (by decide)
  have hl : V [6, 5, 5, 6, 3, 5] = V [3, 5] :=
    ((in_context torus5 [6] [6, 3, 5]).trans (in_context torus6 [] [3, 5]))
  have hr : V [5, 1, 2, 4, 2, 8, 7, 6] = V [5, 1, 2, 4, 2, 7, 1, 7] :=
    (in_context torus1480 [5, 1, 2, 4, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1624 : V [6, 1, 3, 5, 2, 1, 2, 7] = V [4, 6] := by
  have h0 : V [7, 6, 6, 7, 4, 6] = V [6, 1, 3, 5, 3, 2, 8, 7] :=
    overlap torus1472 torus204 [6, 1] [6, 7, 4, 6] (by decide)
  have hl : V [7, 6, 6, 7, 4, 6] = V [4, 6] :=
    ((in_context torus6 [7] [7, 4, 6]).trans (in_context torus7 [] [4, 6]))
  have hr : V [6, 1, 3, 5, 3, 2, 8, 7] = V [6, 1, 3, 5, 2, 1, 2, 7] :=
    (in_context torus1434 [6, 1, 3, 5] [7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1625 : V [7, 1, 4, 6, 3, 1, 3, 8] = V [5, 7] := by
  have h0 : V [8, 7, 7, 8, 5, 7] = V [7, 1, 4, 6, 4, 3, 2, 8] :=
    overlap torus1481 torus224 [7, 1] [7, 8, 5, 7] (by decide)
  have hl : V [8, 7, 7, 8, 5, 7] = V [5, 7] :=
    ((in_context torus7 [8] [8, 5, 7]).trans (in_context torus8 [] [5, 7]))
  have hr : V [7, 1, 4, 6, 4, 3, 2, 8] = V [7, 1, 4, 6, 3, 1, 3, 8] :=
    (in_context torus1444 [7, 1, 4, 6] [8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1626 : V [8, 1, 5, 7, 4, 1, 4, 2] = V [6, 8] := by
  have h0 : V [2, 8, 7, 7, 8, 2, 6, 8] = V [8, 1, 5, 7, 5, 4, 3, 2] :=
    overlap torus1489 torus244 [8, 1] [7, 8, 2, 6, 8] (by decide)
  have hl : V [2, 8, 7, 7, 8, 2, 6, 8] = V [6, 8] :=
    ((in_context torus7 [2, 8] [8, 2, 6, 8]).trans ((in_context torus8 [2] [2, 6, 8]).trans (in_context torus2 [] [6, 8])))
  have hr : V [8, 1, 5, 7, 5, 4, 3, 2] = V [8, 1, 5, 7, 4, 1, 4, 2] :=
    (in_context torus1453 [8, 1, 5, 7] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1627 : V [5, 1, 5, 3, 2, 7, 2, 1] = V [8, 6] := by
  have h0 : V [8, 6, 2, 8, 2, 0, 2, 3] = V [6, 5, 4, 3, 2, 7, 2, 1] :=
    overlap torus248 torus1492 [6, 5, 4, 3, 2, 7] [0, 2, 3] (by decide)
  have hl : V [8, 6, 2, 8, 2, 0, 2, 3] = V [8, 6] :=
    ((in_context torus1428 [8, 6] [0, 2, 3]).trans ((in_context torus1437 [8, 6] [2, 3]).trans ((in_context torus2 [8, 6, 3] [3]).trans (in_context torus3 [8, 6] []))))
  have hr : V [6, 5, 4, 3, 2, 7, 2, 1] = V [5, 1, 5, 3, 2, 7, 2, 1] :=
    (in_context torus1462 [] [3, 2, 7, 2, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1628 : V [2, 7, 1, 7, 5, 3, 5, 1] = V [4, 2] := by
  have h0 : V [4, 2, 5, 4, 5, 0, 5, 6] = V [2, 8, 7, 6, 5, 3, 5, 1] :=
    overlap torus168 torus1497 [2, 8, 7, 6, 5, 3] [0, 5, 6] (by decide)
  have hl : V [4, 2, 5, 4, 5, 0, 5, 6] = V [4, 2] :=
    ((in_context torus1457 [4, 2] [0, 5, 6]).trans ((in_context torus1465 [4, 2] [5, 6]).trans ((in_context torus5 [4, 2, 6] [6]).trans (in_context torus6 [4, 2] []))))
  have hr : V [2, 8, 7, 6, 5, 3, 5, 1] = V [2, 7, 1, 7, 5, 3, 5, 1] :=
    (in_context torus1480 [2] [5, 3, 5, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1629 : V [2, 1, 2, 7, 6, 4, 6, 1] = V [5, 3] := by
  have h0 : V [5, 3, 6, 5, 6, 0, 6, 7] = V [3, 2, 8, 7, 6, 4, 6, 1] :=
    overlap torus188 torus1498 [3, 2, 8, 7, 6, 4] [0, 6, 7] (by decide)
  have hl : V [5, 3, 6, 5, 6, 0, 6, 7] = V [5, 3] :=
    ((in_context torus1466 [5, 3] [0, 6, 7]).trans ((in_context torus1474 [5, 3] [6, 7]).trans ((in_context torus6 [5, 3, 7] [7]).trans (in_context torus7 [5, 3] []))))
  have hr : V [3, 2, 8, 7, 6, 4, 6, 1] = V [2, 1, 2, 7, 6, 4, 6, 1] :=
    (in_context torus1434 [] [7, 6, 4, 6, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1630 : V [3, 1, 3, 8, 7, 5, 7, 1] = V [6, 4] := by
  have h0 : V [6, 4, 7, 6, 7, 0, 7, 8] = V [4, 3, 2, 8, 7, 5, 7, 1] :=
    overlap torus208 torus1499 [4, 3, 2, 8, 7, 5] [0, 7, 8] (by decide)
  have hl : V [6, 4, 7, 6, 7, 0, 7, 8] = V [6, 4] :=
    ((in_context torus1475 [6, 4] [0, 7, 8]).trans ((in_context torus1483 [6, 4] [7, 8]).trans ((in_context torus7 [6, 4, 8] [8]).trans (in_context torus8 [6, 4] []))))
  have hr : V [4, 3, 2, 8, 7, 5, 7, 1] = V [3, 1, 3, 8, 7, 5, 7, 1] :=
    (in_context torus1444 [] [8, 7, 5, 7, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1631 : V [2, 1, 6, 8, 5, 1, 5, 3] = V [7, 2] := by
  have h0 : V [7, 2, 3, 4, 5, 4, 1, 4] = V [3, 2, 8, 2, 6, 8, 5, 1, 5, 3] :=
    overlap torus259 torus1568 [3, 2, 8, 2, 6, 8] [4, 1, 4] (by decide)
  have hl : V [7, 2, 3, 4, 5, 4, 1, 4] = V [7, 2] :=
    ((in_context torus1450 [7, 2] [1, 4]).trans ((in_context torus0 [7, 2, 4] [4]).trans (in_context torus4 [7, 2] [])))
  have hr : V [3, 2, 8, 2, 6, 8, 5, 1, 5, 3] = V [2, 1, 6, 8, 5, 1, 5, 3] :=
    ((in_context torus1434 [] [2, 6, 8, 5, 1, 5, 3]).trans (in_context torus2 [2, 1] [6, 8, 5, 1, 5, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1632 : V [3, 1, 7, 2, 6, 1, 6, 4] = V [8, 3] := by
  have h0 : V [8, 3, 4, 5, 6, 5, 1, 5] = V [4, 3, 2, 3, 7, 2, 6, 1, 6, 4] :=
    overlap torus279 torus1576 [4, 3, 2, 3, 7, 2] [5, 1, 5] (by decide)
  have hl : V [8, 3, 4, 5, 6, 5, 1, 5] = V [8, 3] :=
    ((in_context torus1459 [8, 3] [1, 5]).trans ((in_context torus0 [8, 3, 5] [5]).trans (in_context torus5 [8, 3] [])))
  have hr : V [4, 3, 2, 3, 7, 2, 6, 1, 6, 4] = V [3, 1, 7, 2, 6, 1, 6, 4] :=
    ((in_context torus1444 [] [3, 7, 2, 6, 1, 6, 4]).trans (in_context torus3 [3, 1] [7, 2, 6, 1, 6, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1634 : V [7, 1, 4, 6, 4, 3, 8, 1] = V [5, 8] := by
  have h0 : V [5, 7, 7, 8] = V [7, 1, 4, 6, 3, 1, 3, 0, 8, 2] :=
    overlap torus1625 torus1484 [7, 1, 4, 6, 3, 1, 3] [7, 8] (by decide)
  have hl : V [5, 7, 7, 8] = V [5, 8] :=
    (in_context torus7 [5] [8])
  have hr : V [7, 1, 4, 6, 3, 1, 3, 0, 8, 2] = V [7, 1, 4, 6, 4, 3, 8, 1] :=
    ((in_context torus1543 [7, 1, 4, 6, 3, 1] []).trans (in_context torus1520 [7, 1, 4, 6] [1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1638 : V [0, 2, 7, 2, 3, 4, 5] = V [6, 8, 6] := by
  have h0 : V [2, 8, 8, 2, 6, 8, 6] = V [0, 2, 7, 2, 3, 4, 5] :=
    overlap torus1433 torus259 [0, 2] [8, 2, 6, 8, 6] (by decide)
  have hl : V [2, 8, 8, 2, 6, 8, 6] = V [6, 8, 6] :=
    ((in_context torus8 [2] [2, 6, 8, 6]).trans (in_context torus2 [] [6, 8, 6]))
  have hr : V [0, 2, 7, 2, 3, 4, 5] = V [0, 2, 7, 2, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1643 : V [2, 4, 2, 7, 1, 7, 5] = V [0, 5, 3] := by
  have h0 : V [5, 4, 5, 6, 3] = V [2, 4, 2, 8, 6, 1, 6] :=
    inclusion torus185 torus1471 [2, 4, 2, 8] [] (by decide)
  have hl : V [5, 4, 5, 6, 3] = V [0, 5, 3] :=
    ((in_context torus1457 [] [6, 3]).trans (in_context torus6 [0, 5] [3]))
  have hr : V [2, 4, 2, 8, 6, 1, 6] = V [2, 4, 2, 7, 1, 7, 5] :=
    (in_context torus1584 [2, 4, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1645 : V [3, 5, 3, 2, 7, 1, 7] = V [0, 6, 4] := by
  have h0 : V [6, 5, 6, 7, 4] = V [3, 5, 3, 2, 7, 1, 7] :=
    inclusion torus205 torus1480 [3, 5, 3, 2] [] (by decide)
  have hl : V [6, 5, 6, 7, 4] = V [0, 6, 4] :=
    ((in_context torus1466 [] [7, 4]).trans (in_context torus7 [0, 6] [4]))
  have hr : V [3, 5, 3, 2, 7, 1, 7] = V [3, 5, 3, 2, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1647 : V [5, 1, 2, 4, 2, 7, 1] = V [3, 5, 7] := by
  have h0 : V [3, 5, 7] = V [5, 1, 2, 4, 2, 7, 1] :=
    overlap torus1623 torus7 [5, 1, 2, 4, 2, 7, 1] [7] (by decide)
  have hl : V [3, 5, 7] = V [3, 5, 7] :=
    rfl
  have hr : V [5, 1, 2, 4, 2, 7, 1] = V [5, 1, 2, 4, 2, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1648 : V [5, 1, 2, 4, 2, 8, 6] = V [3, 6, 0] := by
  have h0 : V [3, 5, 1, 6, 5] = V [5, 1, 2, 4, 2, 7, 1, 0, 7, 8, 6] :=
    overlap torus1623 torus1577 [5, 1, 2, 4, 2, 7, 1] [1, 6, 5] (by decide)
  have hl : V [3, 5, 1, 6, 5] = V [3, 6, 0] :=
    (in_context torus1509 [3] [])
  have hr : V [5, 1, 2, 4, 2, 7, 1, 0, 7, 8, 6] = V [5, 1, 2, 4, 2, 8, 6] :=
    ((in_context torus1 [5, 1, 2, 4, 2, 7] [7, 8, 6]).trans (in_context torus7 [5, 1, 2, 4, 2] [8, 6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1649 : V [6, 1, 3, 5, 3, 2, 7] = V [4, 7, 0] := by
  have h0 : V [4, 6, 1, 7, 6] = V [6, 1, 3, 5, 2, 1, 2, 8, 7] :=
    overlap torus1624 torus1481 [6, 1, 3, 5, 2, 1, 2] [1, 7, 6] (by decide)
  have hl : V [4, 6, 1, 7, 6] = V [4, 7, 0] :=
    (in_context torus1510 [4] [])
  have hr : V [6, 1, 3, 5, 2, 1, 2, 8, 7] = V [6, 1, 3, 5, 3, 2, 7] :=
    (in_context torus1435 [6, 1, 3, 5] [7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1650 : V [6, 1, 3, 5, 3, 8, 1] = V [4, 6, 8] := by
  have h0 : V [4, 6, 8] = V [6, 1, 3, 5, 3, 8, 1] :=
    overlap torus1624 torus1540 [6, 1, 3, 5] [8] (by decide)
  have hl : V [4, 6, 8] = V [4, 6, 8] :=
    rfl
  have hr : V [6, 1, 3, 5, 3, 8, 1] = V [6, 1, 3, 5, 3, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1651 : V [7, 1, 4, 6, 4, 2, 1] = V [5, 7, 2] := by
  have h0 : V [5, 7, 2] = V [7, 1, 4, 6, 4, 2, 1] :=
    overlap torus1625 torus1519 [7, 1, 4, 6] [2] (by decide)
  have hl : V [5, 7, 2] = V [5, 7, 2] :=
    rfl
  have hr : V [7, 1, 4, 6, 4, 2, 1] = V [7, 1, 4, 6, 4, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1652 : V [8, 1, 5, 7, 4, 1, 4] = V [6, 8, 2] := by
  have h0 : V [6, 8, 2] = V [8, 1, 5, 7, 4, 1, 4] :=
    overlap torus1626 torus2 [8, 1, 5, 7, 4, 1, 4] [2] (by decide)
  have hl : V [6, 8, 2] = V [6, 8, 2] :=
    rfl
  have hr : V [8, 1, 5, 7, 4, 1, 4] = V [8, 1, 5, 7, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1653 : V [8, 1, 5, 7, 5, 4, 2] = V [6, 2, 0] := by
  have h0 : V [6, 8, 1, 2, 8] = V [8, 1, 5, 7, 4, 1, 4, 3, 2] :=
    overlap torus1626 torus1435 [8, 1, 5, 7, 4, 1, 4] [1, 2, 8] (by decide)
  have hl : V [6, 8, 1, 2, 8] = V [6, 2, 0] :=
    (in_context torus1494 [6] [])
  have hr : V [8, 1, 5, 7, 4, 1, 4, 3, 2] = V [8, 1, 5, 7, 5, 4, 2] :=
    (in_context torus1454 [8, 1, 5, 7] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1655 : V [5, 1, 5, 3, 2, 7, 2] = V [8, 6, 0] := by
  have h0 : V [8, 6, 0] = V [5, 1, 5, 3, 2, 7, 2] :=
    overlap torus1627 torus1 [5, 1, 5, 3, 2, 7, 2] [0] (by decide)
  have hl : V [8, 6, 0] = V [8, 6, 0] :=
    rfl
  have hr : V [5, 1, 5, 3, 2, 7, 2] = V [5, 1, 5, 3, 2, 7, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1656 : V [2, 7, 1, 7, 5, 3, 5] = V [4, 2, 0] := by
  have h0 : V [4, 2, 0] = V [2, 7, 1, 7, 5, 3, 5] :=
    overlap torus1628 torus1 [2, 7, 1, 7, 5, 3, 5] [0] (by decide)
  have hl : V [4, 2, 0] = V [4, 2, 0] :=
    rfl
  have hr : V [2, 7, 1, 7, 5, 3, 5] = V [2, 7, 1, 7, 5, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1661 : V [7, 1, 4, 6, 4, 3, 8] = V [5, 8, 0] := by
  have h0 : V [5, 8, 0] = V [7, 1, 4, 6, 4, 3, 8] :=
    overlap torus1634 torus1 [7, 1, 4, 6, 4, 3, 8] [0] (by decide)
  have hl : V [5, 8, 0] = V [5, 8, 0] :=
    rfl
  have hr : V [7, 1, 4, 6, 4, 3, 8] = V [7, 1, 4, 6, 4, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1662 : V [0, 2, 7, 2, 3, 5, 0] = V [6, 8, 5] := by
  have h0 : V [6, 8, 6, 6, 5] = V [0, 2, 7, 2, 3, 4, 4, 5, 0] :=
    overlap torus1638 torus1460 [0, 2, 7, 2, 3, 4] [6, 5] (by decide)
  have hl : V [6, 8, 6, 6, 5] = V [6, 8, 5] :=
    (in_context torus6 [6, 8] [5])
  have hr : V [0, 2, 7, 2, 3, 4, 4, 5, 0] = V [0, 2, 7, 2, 3, 5, 0] :=
    (in_context torus4 [0, 2, 7, 2, 3] [5, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1664 : V [0, 2, 7, 2, 3, 4] = V [6, 8, 6, 5] := by
  have h0 : V [2, 8, 8, 2, 6, 8, 6, 5] = V [0, 2, 3, 3, 7, 2, 3, 4] :=
    overlap torus1433 torus261 [0, 2, 3] [8, 2, 6, 8, 6, 5] (by decide)
  have hl : V [2, 8, 8, 2, 6, 8, 6, 5] = V [6, 8, 6, 5] :=
    ((in_context torus8 [2] [2, 6, 8, 6, 5]).trans (in_context torus2 [] [6, 8, 6, 5]))
  have hr : V [0, 2, 3, 3, 7, 2, 3, 4] = V [0, 2, 7, 2, 3, 4] :=
    (in_context torus3 [0, 2] [7, 2, 3, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1665 : V [2, 7, 2, 3, 4, 5] = V [1, 6, 8, 6] := by
  have h0 : V [1, 2, 8, 8, 2, 6, 8, 6] = V [2, 7, 2, 3, 4, 5] :=
    overlap torus1436 torus259 [2] [8, 2, 6, 8, 6] (by decide)
  have hl : V [1, 2, 8, 8, 2, 6, 8, 6] = V [1, 6, 8, 6] :=
    ((in_context torus8 [1, 2] [2, 6, 8, 6]).trans (in_context torus2 [1] [6, 8, 6]))
  have hr : V [2, 7, 2, 3, 4, 5] = V [2, 7, 2, 3, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1668 : V [8, 5, 1, 5, 3, 2] = V [6, 0, 2, 7] := by
  have h0 : V [6, 2, 8, 2, 3, 7] = V [8, 6, 5, 3, 1, 3] :=
    inclusion torus266 torus1444 [8, 6, 5] [] (by decide)
  have hl : V [6, 2, 8, 2, 3, 7] = V [6, 0, 2, 7] :=
    ((in_context torus1428 [6] [3, 7]).trans (in_context torus3 [6, 0, 2] [7]))
  have hr : V [8, 6, 5, 3, 1, 3] = V [8, 5, 1, 5, 3, 2] :=
    ((in_context torus1563 [8, 6] []).trans (in_context torus1568 [8] [2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1670 : V [6, 8, 5, 1, 5, 3] = V [0, 2, 7, 2] := by
  have h0 : V [2, 8, 2, 3, 7, 2] = V [6, 8, 6, 4, 1, 4] :=
    inclusion torus265 torus1453 [6, 8, 6] [] (by decide)
  have hl : V [2, 8, 2, 3, 7, 2] = V [0, 2, 7, 2] :=
    ((in_context torus1428 [] [3, 7, 2]).trans (in_context torus3 [0, 2] [7, 2]))
  have hr : V [6, 8, 6, 4, 1, 4] = V [6, 8, 5, 1, 5, 3] :=
    (in_context torus1568 [6, 8] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1671 : V [6, 1, 6, 4, 3, 8] = V [2, 7, 0, 3] := by
  have h0 : V [2, 7, 3, 2, 3, 4] = V [7, 6, 4, 1, 4, 8] :=
    inclusion torus268 torus1453 [7, 6] [8] (by decide)
  have hl : V [2, 7, 3, 2, 3, 4] = V [2, 7, 0, 3] :=
    ((in_context torus1439 [2, 7] [4]).trans (in_context torus4 [2, 7, 0, 3] []))
  have hr : V [7, 6, 4, 1, 4, 8] = V [6, 1, 6, 4, 3, 8] :=
    ((in_context torus1568 [7] [8]).trans (in_context torus1576 [] [3, 8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1672 : V [2, 0, 2, 1, 4, 3] = V [8, 2, 4, 0] := by
  have h0 : V [8, 2, 4, 0] = V [2, 0, 2, 1, 4, 3] :=
    overlap torus1438 torus1455 [2, 0, 2] [4, 0] (by decide)
  have hl : V [8, 2, 4, 0] = V [8, 2, 4, 0] :=
    rfl
  have hr : V [2, 0, 2, 1, 4, 3] = V [2, 0, 2, 1, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1674 : V [0, 3, 8, 3, 5, 0] = V [7, 2, 7, 5] := by
  have h0 : V [7, 2, 7, 6, 5, 5, 6, 5] = V [3, 2, 3, 4, 8, 3, 5, 0] :=
    overlap torus287 torus1459 [3, 2, 3, 4, 8, 3] [5, 6, 5] (by decide)
  have hl : V [7, 2, 7, 6, 5, 5, 6, 5] = V [7, 2, 7, 5] :=
    ((in_context torus5 [7, 2, 7, 6] [6, 5]).trans (in_context torus6 [7, 2, 7] [5]))
  have hr : V [3, 2, 3, 4, 8, 3, 5, 0] = V [0, 3, 8, 3, 5, 0] :=
    ((in_context torus1439 [] [4, 8, 3, 5, 0]).trans (in_context torus4 [0, 3] [8, 3, 5, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1675 : V [0, 3, 8, 3, 4, 5, 6] = V [7, 2, 7] := by
  have h0 : V [7, 2, 7, 5, 5] = V [0, 3, 8, 3, 4, 5, 6] :=
    overlap torus1674 torus1458 [0, 3, 8, 3] [5] (by decide)
  have hl : V [7, 2, 7, 5, 5] = V [7, 2, 7] :=
    (in_context torus5 [7, 2, 7] [])
  have hr : V [0, 3, 8, 3, 4, 5, 6] = V [0, 3, 8, 3, 4, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1677 : V [7, 2, 6, 1, 6, 4] = V [0, 3, 8, 3] := by
  have h0 : V [3, 2, 3, 4, 8, 3] = V [7, 2, 7, 5, 1, 5] :=
    inclusion torus285 torus1462 [7, 2, 7] [] (by decide)
  have hl : V [3, 2, 3, 4, 8, 3] = V [0, 3, 8, 3] :=
    ((in_context torus1439 [] [4, 8, 3]).trans (in_context torus4 [0, 3] [8, 3]))
  have hr : V [7, 2, 7, 5, 1, 5] = V [7, 2, 6, 1, 6, 4] :=
    (in_context torus1576 [7, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1678 : V [7, 1, 7, 5, 4, 2] = V [3, 8, 0, 4] := by
  have h0 : V [3, 8, 4, 3, 4, 5] = V [8, 7, 5, 1, 5, 2] :=
    inclusion torus288 torus1462 [8, 7] [2] (by decide)
  have hl : V [3, 8, 4, 3, 4, 5] = V [3, 8, 0, 4] :=
    ((in_context torus1448 [3, 8] [5]).trans (in_context torus5 [3, 8, 0, 4] []))
  have hr : V [8, 7, 5, 1, 5, 2] = V [7, 1, 7, 5, 4, 2] :=
    ((in_context torus1576 [8] [2]).trans (in_context torus1584 [] [4, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1680 : V [0, 4, 2, 4, 6, 0] = V [8, 3, 8, 6] := by
  have h0 : V [8, 3, 8, 7, 6, 6, 7, 6] = V [4, 3, 4, 5, 2, 4, 6, 0] :=
    overlap torus307 torus1468 [4, 3, 4, 5, 2, 4] [6, 7, 6] (by decide)
  have hl : V [8, 3, 8, 7, 6, 6, 7, 6] = V [8, 3, 8, 6] :=
    ((in_context torus6 [8, 3, 8, 7] [7, 6]).trans (in_context torus7 [8, 3, 8] [6]))
  have hr : V [4, 3, 4, 5, 2, 4, 6, 0] = V [0, 4, 2, 4, 6, 0] :=
    ((in_context torus1448 [] [5, 2, 4, 6, 0]).trans (in_context torus5 [0, 4] [2, 4, 6, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1681 : V [0, 4, 2, 4, 5, 6, 7] = V [8, 3, 8] := by
  have h0 : V [8, 3, 8, 6, 6] = V [0, 4, 2, 4, 5, 6, 7] :=
    overlap torus1680 torus1467 [0, 4, 2, 4] [6] (by decide)
  have hl : V [8, 3, 8, 6, 6] = V [8, 3, 8] :=
    (in_context torus6 [8, 3, 8] [])
  have hr : V [0, 4, 2, 4, 5, 6, 7] = V [0, 4, 2, 4, 5, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1682 : V [0, 4, 2, 4, 5, 7, 0] = V [8, 3, 7] := by
  have h0 : V [8, 3, 8, 8, 7] = V [0, 4, 2, 4, 5, 6, 6, 7, 0] :=
    overlap torus1681 torus1478 [0, 4, 2, 4, 5, 6] [8, 7] (by decide)
  have hl : V [8, 3, 8, 8, 7] = V [8, 3, 7] :=
    (in_context torus8 [8, 3] [7])
  have hr : V [0, 4, 2, 4, 5, 6, 6, 7, 0] = V [0, 4, 2, 4, 5, 7, 0] :=
    (in_context torus6 [0, 4, 2, 4, 5] [7, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1683 : V [4, 2, 7, 1, 7, 5] = V [2, 0, 5, 3] := by
  have h0 : V [2, 5, 4, 5, 6, 3] = V [4, 2, 8, 6, 1, 6] :=
    inclusion torus186 torus1471 [4, 2, 8] [] (by decide)
  have hl : V [2, 5, 4, 5, 6, 3] = V [2, 0, 5, 3] :=
    ((in_context torus1457 [2] [6, 3]).trans (in_context torus6 [2, 0, 5] [3]))
  have hr : V [4, 2, 8, 6, 1, 6] = V [4, 2, 7, 1, 7, 5] :=
    (in_context torus1584 [4, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1684 : V [8, 3, 7, 1, 7, 5] = V [0, 4, 2, 4] := by
  have h0 : V [4, 3, 4, 5, 2, 4] = V [8, 3, 8, 6, 1, 6] :=
    inclusion torus305 torus1471 [8, 3, 8] [] (by decide)
  have hl : V [4, 3, 4, 5, 2, 4] = V [0, 4, 2, 4] :=
    ((in_context torus1448 [] [5, 2, 4]).trans (in_context torus5 [0, 4] [2, 4]))
  have hr : V [8, 3, 8, 6, 1, 6] = V [8, 3, 7, 1, 7, 5] :=
    (in_context torus1584 [8, 3] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1687 : V [5, 3, 2, 7, 1, 7] = V [3, 0, 6, 4] := by
  have h0 : V [3, 6, 5, 6, 7, 4] = V [5, 3, 2, 7, 1, 7] :=
    inclusion torus206 torus1480 [5, 3, 2] [] (by decide)
  have hl : V [3, 6, 5, 6, 7, 4] = V [3, 0, 6, 4] :=
    ((in_context torus1466 [3] [7, 4]).trans (in_context torus7 [3, 0, 6] [4]))
  have hr : V [5, 3, 2, 7, 1, 7] = V [5, 3, 2, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1709 : V [2, 1, 2, 1, 7, 1] = V [3, 8, 6, 7] := by
  have h0 : V [3, 8, 6, 7] = V [2, 1, 2, 1, 8, 0, 7, 8] :=
    overlap torus1513 torus1475 [2, 1, 2, 1, 8] [6, 7] (by decide)
  have hl : V [3, 8, 6, 7] = V [3, 8, 6, 7] :=
    rfl
  have hr : V [2, 1, 2, 1, 8, 0, 7, 8] = V [2, 1, 2, 1, 7, 1] :=
    (in_context torus1499 [2, 1, 2, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1711 : V [1, 3, 2, 4, 6, 5] = V [3, 0, 5, 0] := by
  have h0 : V [3, 0, 4, 1, 5, 4] = V [1, 3, 2, 4, 6, 5] :=
    overlap torus1518 torus1463 [1, 3, 2, 4] [1, 5, 4] (by decide)
  have hl : V [3, 0, 4, 1, 5, 4] = V [3, 0, 5, 0] :=
    (in_context torus1508 [3, 0] [])
  have hr : V [1, 3, 2, 4, 6, 5] = V [1, 3, 2, 4, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1714 : V [1, 4, 3, 5, 7, 6] = V [4, 0, 6, 0] := by
  have h0 : V [4, 0, 5, 1, 6, 5] = V [1, 4, 3, 5, 7, 6] :=
    overlap torus1521 torus1472 [1, 4, 3, 5] [1, 6, 5] (by decide)
  have hl : V [4, 0, 5, 1, 6, 5] = V [4, 0, 6, 0] :=
    (in_context torus1509 [4, 0] [])
  have hr : V [1, 4, 3, 5, 7, 6] = V [1, 4, 3, 5, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1722 : V [0, 2, 3, 7, 1, 7] = V [2, 1, 8, 6] := by
  have h0 : V [2, 1, 8, 6] = V [0, 2, 3, 7, 1, 7] :=
    overlap torus1531 torus1480 [0, 2, 3] [6] (by decide)
  have hl : V [2, 1, 8, 6] = V [2, 1, 8, 6] :=
    rfl
  have hr : V [0, 2, 3, 7, 1, 7] = V [0, 2, 3, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1726 : V [5, 1, 5, 1, 3, 1] = V [6, 4, 2, 3] := by
  have h0 : V [6, 4, 3, 0, 3, 4] = V [5, 1, 5, 1, 3, 1] :=
    overlap torus1547 torus1495 [5, 1, 5, 1] [0, 3, 4] (by decide)
  have hl : V [6, 4, 3, 0, 3, 4] = V [6, 4, 2, 3] :=
    ((in_context torus1440 [6, 4] [4]).trans (in_context torus4 [6, 4, 2, 3] []))
  have hr : V [5, 1, 5, 1, 3, 1] = V [5, 1, 5, 1, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1731 : V [7, 1, 7, 1, 5, 1] = V [8, 6, 4, 5] := by
  have h0 : V [8, 6, 5, 0, 5, 6] = V [7, 1, 7, 1, 5, 1] :=
    overlap torus1578 torus1497 [7, 1, 7, 1] [0, 5, 6] (by decide)
  have hl : V [8, 6, 5, 0, 5, 6] = V [8, 6, 4, 5] :=
    ((in_context torus1458 [8, 6] [6]).trans (in_context torus6 [8, 6, 4, 5] []))
  have hr : V [7, 1, 7, 1, 5, 1] = V [7, 1, 7, 1, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1732 : V [5, 1, 2, 4, 2, 7] = V [3, 5, 7, 0] := by
  have h0 : V [3, 5, 6, 7, 8, 7] = V [5, 1, 2, 4, 2, 7, 1, 3, 2, 3, 4, 3] :=
    overlap torus1623 torus126 [5, 1, 2, 4, 2, 7, 1] [6, 7, 8, 7] (by decide)
  have hl : V [3, 5, 6, 7, 8, 7] = V [3, 5, 7, 0] :=
    (in_context torus1477 [3, 5] [])
  have hr : V [5, 1, 2, 4, 2, 7, 1, 3, 2, 3, 4, 3] = V [5, 1, 2, 4, 2, 7] :=
    ((in_context torus143 [5, 1, 2, 4, 2, 7, 1] []).trans ((in_context torus1428 [5, 1, 2, 4, 2, 7, 1] [3, 2]).trans ((in_context torus1 [5, 1, 2, 4, 2, 7] [2, 3, 3, 2]).trans ((in_context torus3 [5, 1, 2, 4, 2, 7, 2] [2]).trans (in_context torus2 [5, 1, 2, 4, 2, 7] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1733 : V [6, 1, 3, 5, 3, 8] = V [4, 6, 8, 0] := by
  have h0 : V [4, 6, 8, 0] = V [6, 1, 3, 5, 2, 1, 2, 1, 8, 7] :=
    overlap torus1624 torus1490 [6, 1, 3, 5, 2, 1, 2] [8, 0] (by decide)
  have hl : V [4, 6, 8, 0] = V [4, 6, 8, 0] :=
    rfl
  have hr : V [6, 1, 3, 5, 2, 1, 2, 1, 8, 7] = V [6, 1, 3, 5, 3, 8] :=
    (in_context torus1513 [6, 1, 3, 5] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1734 : V [7, 1, 4, 6, 4, 2] = V [5, 7, 2, 0] := by
  have h0 : V [5, 7, 2, 0] = V [7, 1, 4, 6, 3, 1, 3, 2, 3, 2] :=
    overlap torus1625 torus1430 [7, 1, 4, 6, 3, 1, 3] [2, 0] (by decide)
  have hl : V [5, 7, 2, 0] = V [5, 7, 2, 0] :=
    rfl
  have hr : V [7, 1, 4, 6, 3, 1, 3, 2, 3, 2] = V [7, 1, 4, 6, 4, 2] :=
    ((in_context torus1445 [7, 1, 4, 6] [3, 2]).trans (in_context torus3 [7, 1, 4, 6, 4] [2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1736 : V [2, 0, 2, 4, 6, 4] = V [7, 5, 7, 1] := by
  have h0 : V [8, 3, 0, 1, 3, 8, 7, 5, 7, 1] = V [2, 0, 2, 4, 6, 4] :=
    overlap torus1619 torus1630 [2, 0, 2, 4] [1, 3, 8, 7, 5, 7, 1] (by decide)
  have hl : V [8, 3, 0, 1, 3, 8, 7, 5, 7, 1] = V [7, 5, 7, 1] :=
    ((in_context torus0 [8, 3] [3, 8, 7, 5, 7, 1]).trans ((in_context torus3 [8] [8, 7, 5, 7, 1]).trans (in_context torus8 [] [7, 5, 7, 1])))
  have hr : V [2, 0, 2, 4, 6, 4] = V [2, 0, 2, 4, 6, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1741 : V [2, 4, 2, 7, 1, 7] = V [0, 5, 3, 5] := by
  have h0 : V [0, 5, 3, 5] = V [2, 4, 2, 7, 1, 7] :=
    overlap torus1643 torus5 [2, 4, 2, 7, 1, 7] [5] (by decide)
  have hl : V [0, 5, 3, 5] = V [0, 5, 3, 5] :=
    rfl
  have hr : V [2, 4, 2, 7, 1, 7] = V [2, 4, 2, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1743 : V [8, 1, 5, 7, 5, 4] = V [6, 2, 0, 2] := by
  have h0 : V [6, 8, 2, 3] = V [8, 1, 5, 7, 5, 4] :=
    overlap torus1652 torus1454 [8, 1, 5, 7] [3] (by decide)
  have hl : V [6, 8, 2, 3] = V [6, 2, 0, 2] :=
    (in_context torus1429 [6] [])
  have hr : V [8, 1, 5, 7, 5, 4] = V [8, 1, 5, 7, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1744 : V [5, 1, 5, 3, 2, 7] = V [8, 6, 0, 2] := by
  have h0 : V [8, 6, 0, 2] = V [5, 1, 5, 3, 2, 7] :=
    overlap torus1655 torus2 [5, 1, 5, 3, 2, 7] [2] (by decide)
  have hl : V [8, 6, 0, 2] = V [8, 6, 0, 2] :=
    rfl
  have hr : V [5, 1, 5, 3, 2, 7] = V [5, 1, 5, 3, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1745 : V [2, 7, 1, 7, 5, 3] = V [4, 2, 0, 5] := by
  have h0 : V [4, 2, 0, 5] = V [2, 7, 1, 7, 5, 3] :=
    overlap torus1656 torus5 [2, 7, 1, 7, 5, 3] [5] (by decide)
  have hl : V [4, 2, 0, 5] = V [4, 2, 0, 5] :=
    rfl
  have hr : V [2, 7, 1, 7, 5, 3] = V [2, 7, 1, 7, 5, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1746 : V [6, 8, 2, 4, 2, 0, 5] = V [1, 6, 3] := by
  have h0 : V [6, 8, 7, 1, 7, 5, 3] = V [8, 1, 5, 7, 4, 1, 4, 4, 2, 0, 5] :=
    overlap torus1626 torus1745 [8, 1, 5, 7, 4, 1, 4] [7, 1, 7, 5, 3] (by decide)
  have hl : V [6, 8, 7, 1, 7, 5, 3] = V [1, 6, 3] :=
    ((in_context torus1479 [6] [7, 5, 3]).trans ((in_context torus1574 [] [7, 5, 3]).trans ((in_context torus7 [1, 6, 5] [5, 3]).trans (in_context torus5 [1, 6] [3]))))
  have hr : V [8, 1, 5, 7, 4, 1, 4, 4, 2, 0, 5] = V [6, 8, 2, 4, 2, 0, 5] :=
    (in_context torus1652 [] [4, 2, 0, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1747 : V [6, 8, 2, 4, 2, 0] = V [1, 6, 3, 5] := by
  have h0 : V [6, 8, 7, 1, 7, 5, 3, 5] = V [8, 1, 5, 7, 4, 1, 4, 4, 2, 0] :=
    overlap torus1626 torus1656 [8, 1, 5, 7, 4, 1, 4] [7, 1, 7, 5, 3, 5] (by decide)
  have hl : V [6, 8, 7, 1, 7, 5, 3, 5] = V [1, 6, 3, 5] :=
    ((in_context torus1479 [6] [7, 5, 3, 5]).trans ((in_context torus1574 [] [7, 5, 3, 5]).trans ((in_context torus7 [1, 6, 5] [5, 3, 5]).trans (in_context torus5 [1, 6] [3, 5]))))
  have hr : V [8, 1, 5, 7, 4, 1, 4, 4, 2, 0] = V [6, 8, 2, 4, 2, 0] :=
    (in_context torus1652 [] [4, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1748 : V [0, 2, 7, 2, 3, 5] = V [6, 8, 5, 1] := by
  have h0 : V [6, 8, 5, 1] = V [0, 2, 7, 2, 3, 5] :=
    overlap torus1662 torus0 [0, 2, 7, 2, 3, 5] [1] (by decide)
  have hl : V [6, 8, 5, 1] = V [6, 8, 5, 1] :=
    rfl
  have hr : V [0, 2, 7, 2, 3, 5] = V [0, 2, 7, 2, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1749 : V [0, 6, 2, 7, 0, 3] = V [6, 4, 3, 8] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 6, 4, 3, 8] = V [6, 5, 6, 7, 2, 7, 0, 3] :=
    overlap torus117 torus1671 [6, 5, 6, 7] [1, 6, 4, 3, 8] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 6, 4, 3, 8] = V [6, 4, 3, 8] :=
    ((in_context torus143 [] [1, 6, 4, 3, 8]).trans ((in_context torus1428 [] [3, 2, 1, 6, 4, 3, 8]).trans ((in_context torus3 [0, 2] [2, 1, 6, 4, 3, 8]).trans ((in_context torus2 [0] [1, 6, 4, 3, 8]).trans (in_context torus0 [] [6, 4, 3, 8])))))
  have hr : V [6, 5, 6, 7, 2, 7, 0, 3] = V [0, 6, 2, 7, 0, 3] :=
    ((in_context torus1466 [] [7, 2, 7, 0, 3]).trans (in_context torus7 [0, 6] [2, 7, 0, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1752 : V [0, 7, 3, 8, 0, 4] = V [7, 5, 4, 2] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 7, 5, 4, 2] = V [7, 6, 7, 8, 3, 8, 0, 4] :=
    overlap torus126 torus1678 [7, 6, 7, 8] [1, 7, 5, 4, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 7, 5, 4, 2] = V [7, 5, 4, 2] :=
    ((in_context torus143 [] [1, 7, 5, 4, 2]).trans ((in_context torus1428 [] [3, 2, 1, 7, 5, 4, 2]).trans ((in_context torus3 [0, 2] [2, 1, 7, 5, 4, 2]).trans ((in_context torus2 [0] [1, 7, 5, 4, 2]).trans (in_context torus0 [] [7, 5, 4, 2])))))
  have hr : V [7, 6, 7, 8, 3, 8, 0, 4] = V [0, 7, 3, 8, 0, 4] :=
    ((in_context torus1475 [] [8, 3, 8, 0, 4]).trans (in_context torus8 [0, 7] [3, 8, 0, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1754 : V [0, 4, 2, 4, 5, 7] = V [8, 3, 7, 1] := by
  have h0 : V [8, 3, 7, 1] = V [0, 4, 2, 4, 5, 7] :=
    overlap torus1682 torus0 [0, 4, 2, 4, 5, 7] [1] (by decide)
  have hl : V [8, 3, 7, 1] = V [8, 3, 7, 1] :=
    rfl
  have hr : V [0, 4, 2, 4, 5, 7] = V [0, 4, 2, 4, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1758 : V [8, 5, 1, 5, 3] = V [6, 0, 2, 7, 2] := by
  have h0 : V [8, 6, 5, 4, 3] = V [6, 0, 2, 3, 3, 7, 2] :=
    inclusion torus267 torus1428 [6] [3, 7, 2] (by decide)
  have hl : V [8, 6, 5, 4, 3] = V [8, 5, 1, 5, 3] :=
    (in_context torus1462 [8] [3])
  have hr : V [6, 0, 2, 3, 3, 7, 2] = V [6, 0, 2, 7, 2] :=
    (in_context torus3 [6, 0, 2] [7, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1762 : V [5, 6, 8, 6, 0] = V [3, 1, 3, 7, 2] := by
  have h0 : V [5, 6, 8, 6, 2, 2, 0] = V [4, 3, 2, 7, 3, 2, 2, 3, 2] :=
    overlap torus252 torus1430 [4, 3, 2, 7, 3, 2] [2, 0] (by decide)
  have hl : V [5, 6, 8, 6, 2, 2, 0] = V [5, 6, 8, 6, 0] :=
    (in_context torus2 [5, 6, 8, 6] [0])
  have hr : V [4, 3, 2, 7, 3, 2, 2, 3, 2] = V [3, 1, 3, 7, 2] :=
    ((in_context torus2 [4, 3, 2, 7, 3] [3, 2]).trans ((in_context torus3 [4, 3, 2, 7] [2]).trans (in_context torus1444 [] [7, 2])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1764 : V [3, 4, 5, 6, 8] = V [2, 7, 2, 1, 6] := by
  have h0 : V [3, 4, 5, 6, 8] = V [2, 7, 2, 1, 2, 2, 6] :=
    inclusion torus256 torus1434 [2, 7] [2, 6] (by decide)
  have hl : V [3, 4, 5, 6, 8] = V [3, 4, 5, 6, 8] :=
    rfl
  have hr : V [2, 7, 2, 1, 2, 2, 6] = V [2, 7, 2, 1, 6] :=
    (in_context torus2 [2, 7, 2, 1] [6])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1767 : V [7, 2, 3, 4, 5] = V [2, 1, 6, 8, 6] := by
  have h0 : V [7, 2, 3, 4, 5] = V [2, 1, 2, 2, 6, 8, 6] :=
    inclusion torus259 torus1434 [] [2, 6, 8, 6] (by decide)
  have hl : V [7, 2, 3, 4, 5] = V [7, 2, 3, 4, 5] :=
    rfl
  have hr : V [2, 1, 2, 2, 6, 8, 6] = V [2, 1, 6, 8, 6] :=
    (in_context torus2 [2, 1] [6, 8, 6])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1768 : V [7, 2, 1, 6, 8, 6] = V [2, 3, 4, 5] := by
  have h0 : V [2, 3, 4, 5] = V [7, 2, 1, 6, 8, 6] :=
    overlap torus7 torus1767 [7] [2, 3, 4, 5] (by decide)
  have hl : V [2, 3, 4, 5] = V [2, 3, 4, 5] :=
    rfl
  have hr : V [7, 2, 1, 6, 8, 6] = V [7, 2, 1, 6, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1772 : V [7, 2, 6, 1, 6] = V [0, 3, 8, 3, 4] := by
  have h0 : V [7, 2, 7, 6, 5] = V [0, 3, 4, 4, 8, 3, 4] :=
    inclusion torus287 torus1439 [] [4, 8, 3, 4] (by decide)
  have hl : V [7, 2, 7, 6, 5] = V [7, 2, 6, 1, 6] :=
    (in_context torus1471 [7, 2] [])
  have hr : V [0, 3, 4, 4, 8, 3, 4] = V [0, 3, 8, 3, 4] :=
    (in_context torus4 [0, 3] [8, 3, 4])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1773 : V [7, 0, 3, 8, 3, 4] = V [2, 6, 1, 6] := by
  have h0 : V [2, 6, 1, 6] = V [7, 0, 3, 8, 3, 4] :=
    overlap torus7 torus1772 [7] [2, 6, 1, 6] (by decide)
  have hl : V [2, 6, 1, 6] = V [2, 6, 1, 6] :=
    rfl
  have hr : V [7, 0, 3, 8, 3, 4] = V [7, 0, 3, 8, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1777 : V [6, 7, 2, 7, 0] = V [4, 1, 4, 8, 3] := by
  have h0 : V [5, 4, 3, 8, 4, 3, 3, 4, 3] = V [6, 7, 2, 7, 3, 3, 0] :=
    overlap torus271 torus1441 [6, 7, 2, 7, 3] [3, 4, 3] (by decide)
  have hl : V [5, 4, 3, 8, 4, 3, 3, 4, 3] = V [4, 1, 4, 8, 3] :=
    ((in_context torus3 [5, 4, 3, 8, 4] [4, 3]).trans ((in_context torus4 [5, 4, 3, 8] [3]).trans (in_context torus1453 [] [8, 3])))
  have hr : V [6, 7, 2, 7, 3, 3, 0] = V [6, 7, 2, 7, 0] :=
    (in_context torus3 [6, 7, 2, 7] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1778 : V [5, 1, 5, 3, 8, 3] = V [7, 2, 7, 0] := by
  have h0 : V [7, 2, 7, 0] = V [6, 4, 1, 4, 8, 3] :=
    overlap torus6 torus1777 [6] [7, 2, 7, 0] (by decide)
  have hl : V [7, 2, 7, 0] = V [7, 2, 7, 0] :=
    rfl
  have hr : V [6, 4, 1, 4, 8, 3] = V [5, 1, 5, 3, 8, 3] :=
    (in_context torus1568 [] [8, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1781 : V [5, 6, 7, 2, 7] = V [4, 3, 8, 3, 1] := by
  have h0 : V [5, 6, 7, 2, 7] = V [4, 3, 8, 3, 1, 3, 3] :=
    inclusion torus274 torus1444 [4, 3, 8] [3] (by decide)
  have hl : V [5, 6, 7, 2, 7] = V [5, 6, 7, 2, 7] :=
    rfl
  have hr : V [4, 3, 8, 3, 1, 3, 3] = V [4, 3, 8, 3, 1] :=
    (in_context torus3 [4, 3, 8, 3, 1] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1782 : V [6, 4, 3, 8, 3, 1] = V [0, 6, 2, 7] := by
  have h0 : V [0, 6, 7, 7, 2, 7] = V [6, 4, 3, 8, 3, 1] :=
    overlap torus1466 torus1781 [6] [7, 2, 7] (by decide)
  have hl : V [0, 6, 7, 7, 2, 7] = V [0, 6, 2, 7] :=
    (in_context torus7 [0, 6] [2, 7])
  have hr : V [6, 4, 3, 8, 3, 1] = V [6, 4, 3, 8, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1783 : V [4, 5, 6, 7, 2] = V [3, 8, 3, 1, 7] := by
  have h0 : V [4, 5, 6, 7, 2] = V [3, 8, 3, 1, 3, 3, 7] :=
    inclusion torus276 torus1444 [3, 8] [3, 7] (by decide)
  have hl : V [4, 5, 6, 7, 2] = V [4, 5, 6, 7, 2] :=
    rfl
  have hr : V [3, 8, 3, 1, 3, 3, 7] = V [3, 8, 3, 1, 7] :=
    (in_context torus3 [3, 8, 3, 1] [7])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1785 : V [8, 3, 4, 5, 6] = V [3, 1, 7, 2, 7] := by
  have h0 : V [8, 3, 4, 5, 6] = V [3, 1, 3, 3, 7, 2, 7] :=
    inclusion torus279 torus1444 [] [3, 7, 2, 7] (by decide)
  have hl : V [8, 3, 4, 5, 6] = V [8, 3, 4, 5, 6] :=
    rfl
  have hr : V [3, 1, 3, 3, 7, 2, 7] = V [3, 1, 7, 2, 7] :=
    (in_context torus3 [3, 1] [7, 2, 7])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1786 : V [8, 3, 1, 7, 2, 7] = V [3, 4, 5, 6] := by
  have h0 : V [3, 4, 5, 6] = V [8, 3, 1, 7, 2, 7] :=
    overlap torus8 torus1785 [8] [3, 4, 5, 6] (by decide)
  have hl : V [3, 4, 5, 6] = V [3, 4, 5, 6] :=
    rfl
  have hr : V [8, 3, 1, 7, 2, 7] = V [8, 3, 1, 7, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1789 : V [8, 3, 7, 1, 7] = V [0, 4, 2, 4, 5] := by
  have h0 : V [8, 3, 8, 7, 6] = V [0, 4, 5, 5, 2, 4, 5] :=
    inclusion torus307 torus1448 [] [5, 2, 4, 5] (by decide)
  have hl : V [8, 3, 8, 7, 6] = V [8, 3, 7, 1, 7] :=
    (in_context torus1480 [8, 3] [])
  have hr : V [0, 4, 5, 5, 2, 4, 5] = V [0, 4, 2, 4, 5] :=
    (in_context torus5 [0, 4] [2, 4, 5])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1790 : V [8, 0, 4, 2, 4, 5] = V [3, 7, 1, 7] := by
  have h0 : V [3, 7, 1, 7] = V [8, 0, 4, 2, 4, 5] :=
    overlap torus8 torus1789 [8] [3, 7, 1, 7] (by decide)
  have hl : V [3, 7, 1, 7] = V [3, 7, 1, 7] :=
    rfl
  have hr : V [8, 0, 4, 2, 4, 5] = V [8, 0, 4, 2, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1791 : V [8, 0, 4, 2, 5, 0] = V [3, 8, 7, 5] := by
  have h0 : V [3, 7, 1, 7, 6, 5] = V [8, 0, 4, 2, 4, 4, 5, 0] :=
    overlap torus1790 torus1460 [8, 0, 4, 2, 4] [6, 5] (by decide)
  have hl : V [3, 7, 1, 7, 6, 5] = V [3, 8, 7, 5] :=
    (in_context torus1481 [3] [5])
  have hr : V [8, 0, 4, 2, 4, 4, 5, 0] = V [8, 0, 4, 2, 5, 0] :=
    (in_context torus4 [8, 0, 4, 2] [5, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1792 : V [1, 8, 3, 8, 7, 5] = V [4, 2, 5, 0] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 4, 2, 5, 0] = V [8, 2, 8, 7, 3, 8, 7, 5] :=
    overlap torus138 torus1791 [8, 2, 8, 7] [0, 4, 2, 5, 0] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 4, 2, 5, 0] = V [4, 2, 5, 0] :=
    ((in_context torus146 [] [0, 4, 2, 5, 0]).trans ((in_context torus1436 [] [8, 2, 0, 4, 2, 5, 0]).trans ((in_context torus8 [1, 2] [2, 0, 4, 2, 5, 0]).trans ((in_context torus2 [1] [0, 4, 2, 5, 0]).trans (in_context torus1 [] [4, 2, 5, 0])))))
  have hr : V [8, 2, 8, 7, 3, 8, 7, 5] = V [1, 8, 3, 8, 7, 5] :=
    ((in_context torus1487 [] [7, 3, 8, 7, 5]).trans ((in_context torus1490 [] [7, 3, 8, 7, 5]).trans (in_context torus7 [1, 8] [3, 8, 7, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1796 : V [7, 8, 3, 8, 0] = V [5, 1, 5, 2, 4] := by
  have h0 : V [6, 5, 4, 2, 5, 4, 4, 5, 4] = V [7, 8, 3, 8, 4, 4, 0] :=
    overlap torus291 torus1450 [7, 8, 3, 8, 4] [4, 5, 4] (by decide)
  have hl : V [6, 5, 4, 2, 5, 4, 4, 5, 4] = V [5, 1, 5, 2, 4] :=
    ((in_context torus4 [6, 5, 4, 2, 5] [5, 4]).trans ((in_context torus5 [6, 5, 4, 2] [4]).trans (in_context torus1462 [] [2, 4])))
  have hr : V [7, 8, 3, 8, 4, 4, 0] = V [7, 8, 3, 8, 0] :=
    (in_context torus4 [7, 8, 3, 8] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1801 : V [6, 7, 8, 3, 8] = V [5, 4, 2, 4, 1] := by
  have h0 : V [6, 7, 8, 3, 8] = V [5, 4, 2, 4, 1, 4, 4] :=
    inclusion torus294 torus1453 [5, 4, 2] [4] (by decide)
  have hl : V [6, 7, 8, 3, 8] = V [6, 7, 8, 3, 8] :=
    rfl
  have hr : V [5, 4, 2, 4, 1, 4, 4] = V [5, 4, 2, 4, 1] :=
    (in_context torus4 [5, 4, 2, 4, 1] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1802 : V [7, 5, 4, 2, 4, 1] = V [0, 7, 3, 8] := by
  have h0 : V [0, 7, 8, 8, 3, 8] = V [7, 5, 4, 2, 4, 1] :=
    overlap torus1475 torus1801 [7] [8, 3, 8] (by decide)
  have hl : V [0, 7, 8, 8, 3, 8] = V [0, 7, 3, 8] :=
    (in_context torus8 [0, 7] [3, 8])
  have hr : V [7, 5, 4, 2, 4, 1] = V [7, 5, 4, 2, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1803 : V [5, 6, 7, 8, 3] = V [4, 2, 4, 1, 8] := by
  have h0 : V [5, 6, 7, 8, 3] = V [4, 2, 4, 1, 4, 4, 8] :=
    inclusion torus296 torus1453 [4, 2] [4, 8] (by decide)
  have hl : V [5, 6, 7, 8, 3] = V [5, 6, 7, 8, 3] :=
    rfl
  have hr : V [4, 2, 4, 1, 4, 4, 8] = V [4, 2, 4, 1, 8] :=
    (in_context torus4 [4, 2, 4, 1] [8])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1805 : V [4, 5, 6, 7, 8] = V [2, 4, 1, 8, 3] := by
  have h0 : V [4, 5, 6, 7, 8] = V [2, 4, 1, 4, 4, 8, 3] :=
    inclusion torus298 torus1453 [2] [4, 8, 3] (by decide)
  have hl : V [4, 5, 6, 7, 8] = V [4, 5, 6, 7, 8] :=
    rfl
  have hr : V [2, 4, 1, 4, 4, 8, 3] = V [2, 4, 1, 8, 3] :=
    (in_context torus4 [2, 4, 1] [8, 3])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1810 : V [5, 2, 4, 1, 8] = V [0, 5, 7, 8, 3] := by
  have h0 : V [0, 5, 6, 6, 7, 8, 3] = V [5, 2, 5, 4, 3, 4, 8] :=
    overlap torus1457 torus297 [5] [6, 7, 8, 3] (by decide)
  have hl : V [0, 5, 6, 6, 7, 8, 3] = V [0, 5, 7, 8, 3] :=
    (in_context torus6 [0, 5] [7, 8, 3])
  have hr : V [5, 2, 5, 4, 3, 4, 8] = V [5, 2, 4, 1, 8] :=
    ((in_context torus1453 [5, 2] [4, 8]).trans (in_context torus4 [5, 2, 4, 1] [8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1813 : V [8, 2, 4, 2, 0] = V [6, 1, 6, 3, 5] := by
  have h0 : V [7, 6, 5, 3, 6, 5, 5, 6, 5] = V [8, 2, 4, 2, 5, 5, 0] :=
    overlap torus170 torus1459 [8, 2, 4, 2, 5] [5, 6, 5] (by decide)
  have hl : V [7, 6, 5, 3, 6, 5, 5, 6, 5] = V [6, 1, 6, 3, 5] :=
    ((in_context torus5 [7, 6, 5, 3, 6] [6, 5]).trans ((in_context torus6 [7, 6, 5, 3] [5]).trans (in_context torus1471 [] [3, 5])))
  have hr : V [8, 2, 4, 2, 5, 5, 0] = V [8, 2, 4, 2, 0] :=
    (in_context torus5 [8, 2, 4, 2] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1820 : V [6, 7, 8, 2, 4] = V [5, 3, 5, 1, 2] := by
  have h0 : V [6, 7, 8, 2, 4] = V [5, 3, 5, 1, 5, 5, 2] :=
    inclusion torus175 torus1462 [5, 3] [5, 2] (by decide)
  have hl : V [6, 7, 8, 2, 4] = V [6, 7, 8, 2, 4] :=
    rfl
  have hr : V [5, 3, 5, 1, 5, 5, 2] = V [5, 3, 5, 1, 2] :=
    (in_context torus5 [5, 3, 5, 1] [2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1821 : V [7, 1, 7, 5, 3, 5, 1, 2] = V [2, 4] := by
  have h0 : V [8, 7, 7, 8, 2, 4] = V [7, 1, 7, 5, 3, 5, 1, 2] :=
    overlap torus1481 torus1820 [7, 1, 7] [7, 8, 2, 4] (by decide)
  have hl : V [8, 7, 7, 8, 2, 4] = V [2, 4] :=
    ((in_context torus7 [8] [8, 2, 4]).trans (in_context torus8 [] [2, 4]))
  have hr : V [7, 1, 7, 5, 3, 5, 1, 2] = V [7, 1, 7, 5, 3, 5, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1823 : V [5, 6, 7, 8, 2] = V [3, 5, 1, 2, 4] := by
  have h0 : V [5, 6, 7, 8, 2] = V [3, 5, 1, 5, 5, 2, 4] :=
    inclusion torus177 torus1462 [3] [5, 2, 4] (by decide)
  have hl : V [5, 6, 7, 8, 2] = V [5, 6, 7, 8, 2] :=
    rfl
  have hr : V [3, 5, 1, 5, 5, 2, 4] = V [3, 5, 1, 2, 4] :=
    (in_context torus5 [3, 5, 1] [2, 4])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1824 : V [6, 1, 6, 3, 5, 1, 2, 4] = V [8, 2] := by
  have h0 : V [7, 6, 6, 7, 8, 2] = V [6, 1, 6, 3, 5, 1, 2, 4] :=
    overlap torus1472 torus1823 [6, 1, 6] [6, 7, 8, 2] (by decide)
  have hl : V [7, 6, 6, 7, 8, 2] = V [8, 2] :=
    ((in_context torus6 [7] [7, 8, 2]).trans (in_context torus7 [] [8, 2]))
  have hr : V [6, 1, 6, 3, 5, 1, 2, 4] = V [6, 1, 6, 3, 5, 1, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1826 : V [6, 3, 5, 1, 2] = V [0, 6, 8, 2, 4] := by
  have h0 : V [0, 6, 7, 7, 8, 2, 4] = V [6, 3, 6, 5, 4, 5, 2] :=
    overlap torus1466 torus176 [6] [7, 8, 2, 4] (by decide)
  have hl : V [0, 6, 7, 7, 8, 2, 4] = V [0, 6, 8, 2, 4] :=
    (in_context torus7 [0, 6] [8, 2, 4])
  have hr : V [6, 3, 6, 5, 4, 5, 2] = V [6, 3, 5, 1, 2] :=
    ((in_context torus1462 [6, 3] [5, 2]).trans (in_context torus5 [6, 3, 5, 1] [2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1832 : V [8, 3, 4, 6, 0] = V [3, 1, 7, 2, 6] := by
  have h0 : V [4, 3, 2, 3, 7, 2, 6] = V [8, 3, 4, 6, 0] :=
    overlap torus278 torus1468 [8, 3, 4] [6] (by decide)
  have hl : V [4, 3, 2, 3, 7, 2, 6] = V [3, 1, 7, 2, 6] :=
    ((in_context torus1444 [] [3, 7, 2, 6]).trans (in_context torus3 [3, 1] [7, 2, 6]))
  have hr : V [8, 3, 4, 6, 0] = V [8, 3, 4, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1834 : V [7, 6, 4, 6, 1] = V [2, 0, 2, 5, 3] := by
  have h0 : V [8, 2, 3, 5, 3] = V [7, 6, 4, 6, 1, 6, 6] :=
    inclusion torus193 torus1471 [7, 6, 4] [6] (by decide)
  have hl : V [8, 2, 3, 5, 3] = V [2, 0, 2, 5, 3] :=
    (in_context torus1429 [] [5, 3])
  have hr : V [7, 6, 4, 6, 1, 6, 6] = V [7, 6, 4, 6, 1] :=
    (in_context torus6 [7, 6, 4, 6, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1837 : V [7, 2, 0, 2, 5] = V [6, 4, 6, 1, 3] := by
  have h0 : V [7, 8, 2, 3, 5] = V [6, 4, 6, 1, 6, 6, 3] :=
    inclusion torus195 torus1471 [6, 4] [6, 3] (by decide)
  have hl : V [7, 8, 2, 3, 5] = V [7, 2, 0, 2, 5] :=
    (in_context torus1429 [7] [5])
  have hr : V [6, 4, 6, 1, 6, 6, 3] = V [6, 4, 6, 1, 3] :=
    (in_context torus6 [6, 4, 6, 1] [3])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1839 : V [6, 7, 2, 0, 2] = V [4, 6, 1, 3, 5] := by
  have h0 : V [6, 7, 8, 2, 3] = V [4, 6, 1, 6, 6, 3, 5] :=
    inclusion torus197 torus1471 [4] [6, 3, 5] (by decide)
  have hl : V [6, 7, 8, 2, 3] = V [6, 7, 2, 0, 2] :=
    (in_context torus1429 [6, 7] [])
  have hr : V [4, 6, 1, 6, 6, 3, 5] = V [4, 6, 1, 3, 5] :=
    (in_context torus6 [4, 6, 1] [3, 5])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1840 : V [7, 1, 7, 4, 6, 1, 3, 5] = V [2, 3] := by
  have h0 : V [8, 7, 7, 2, 0, 2] = V [7, 1, 7, 4, 6, 1, 3, 5] :=
    overlap torus1481 torus1839 [7, 1, 7] [7, 2, 0, 2] (by decide)
  have hl : V [8, 7, 7, 2, 0, 2] = V [2, 3] :=
    ((in_context torus7 [8] [2, 0, 2]).trans ((in_context torus1430 [] [2]).trans ((in_context torus1436 [] [2]).trans ((in_context torus1428 [1] []).trans (in_context torus1 [] [2, 3])))))
  have hr : V [7, 1, 7, 4, 6, 1, 3, 5] = V [7, 1, 7, 4, 6, 1, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1842 : V [7, 1, 7, 4, 6] = V [2, 3, 5, 3, 0] := by
  have h0 : V [2, 3, 5, 3, 6, 5, 1, 6, 5] = V [8, 7, 6, 4, 7, 7, 6] :=
    overlap torus191 torus1472 [8, 7, 6, 4, 7] [1, 6, 5] (by decide)
  have hl : V [2, 3, 5, 3, 6, 5, 1, 6, 5] = V [2, 3, 5, 3, 0] :=
    ((in_context torus1461 [2, 3, 5, 3] [6, 5]).trans ((in_context torus6 [2, 3, 5, 3, 0, 5] [5]).trans (in_context torus5 [2, 3, 5, 3, 0] [])))
  have hr : V [8, 7, 6, 4, 7, 7, 6] = V [7, 1, 7, 4, 6] :=
    ((in_context torus7 [8, 7, 6, 4] [6]).trans (in_context torus1480 [] [4, 6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1846 : V [7, 4, 6, 1, 3] = V [0, 7, 2, 3, 5] := by
  have h0 : V [0, 7, 8, 8, 2, 3, 5] = V [7, 4, 7, 6, 5, 6, 3] :=
    overlap torus1475 torus196 [7] [8, 2, 3, 5] (by decide)
  have hl : V [0, 7, 8, 8, 2, 3, 5] = V [0, 7, 2, 3, 5] :=
    (in_context torus8 [0, 7] [2, 3, 5])
  have hr : V [7, 4, 7, 6, 5, 6, 3] = V [7, 4, 6, 1, 3] :=
    ((in_context torus1471 [7, 4] [6, 3]).trans (in_context torus6 [7, 4, 6, 1] [3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1849 : V [3, 5, 3, 2, 7] = V [0, 6, 4, 7, 0] := by
  have h0 : V [3, 5, 3, 2, 8, 7, 7, 8, 7] = V [6, 5, 6, 7, 4, 7, 0] :=
    overlap torus204 torus1477 [6, 5, 6, 7, 4] [7, 8, 7] (by decide)
  have hl : V [3, 5, 3, 2, 8, 7, 7, 8, 7] = V [3, 5, 3, 2, 7] :=
    ((in_context torus1434 [3, 5] [7, 7, 8, 7]).trans ((in_context torus7 [3, 5, 2, 1, 2] [8, 7]).trans (in_context torus1435 [3, 5] [7])))
  have hr : V [6, 5, 6, 7, 4, 7, 0] = V [0, 6, 4, 7, 0] :=
    ((in_context torus1466 [] [7, 4, 7, 0]).trans (in_context torus7 [0, 6] [4, 7, 0]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1850 : V [2, 3, 5, 3, 0, 6, 4, 7, 0] = V [7] := by
  have h0 : V [2, 3, 3, 2, 7] = V [7, 1, 7, 4, 6, 1, 0, 6, 4, 7, 0] :=
    overlap torus1840 torus1849 [7, 1, 7, 4, 6, 1] [3, 2, 7] (by decide)
  have hl : V [2, 3, 3, 2, 7] = V [7] :=
    ((in_context torus3 [2] [2, 7]).trans (in_context torus2 [] [7]))
  have hr : V [7, 1, 7, 4, 6, 1, 0, 6, 4, 7, 0] = V [2, 3, 5, 3, 0, 6, 4, 7, 0] :=
    ((in_context torus1842 [] [1, 0, 6, 4, 7, 0]).trans (in_context torus0 [2, 3, 5, 3] [0, 6, 4, 7, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1851 : V [2, 3, 5, 3, 0, 6, 4, 6, 7, 8] = V [] := by
  have h0 : V [7, 7] = V [2, 3, 5, 3, 0, 6, 4, 6, 7, 8] :=
    overlap torus1850 torus1476 [2, 3, 5, 3, 0, 6, 4] [7] (by decide)
  have hl : V [7, 7] = V [] :=
    (in_context torus7 [] [])
  have hr : V [2, 3, 5, 3, 0, 6, 4, 6, 7, 8] = V [2, 3, 5, 3, 0, 6, 4, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1852 : V [2, 3, 5, 3, 0, 6, 4, 6, 7] = V [8] := by
  have h0 : V [8] = V [2, 3, 5, 3, 0, 6, 4, 6, 7] :=
    overlap torus1851 torus8 [2, 3, 5, 3, 0, 6, 4, 6, 7] [8] (by decide)
  have hl : V [8] = V [8] :=
    rfl
  have hr : V [2, 3, 5, 3, 0, 6, 4, 6, 7] = V [2, 3, 5, 3, 0, 6, 4, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1856 : V [3, 4, 6, 4, 0] = V [2, 8, 7, 5, 7] := by
  have h0 : V [2, 8, 7, 5, 8, 7, 7, 8, 7] = V [3, 4, 6, 4, 7, 7, 0] :=
    overlap torus211 torus1477 [3, 4, 6, 4, 7] [7, 8, 7] (by decide)
  have hl : V [2, 8, 7, 5, 8, 7, 7, 8, 7] = V [2, 8, 7, 5, 7] :=
    ((in_context torus7 [2, 8, 7, 5, 8] [8, 7]).trans (in_context torus8 [2, 8, 7, 5] [7]))
  have hr : V [3, 4, 6, 4, 7, 7, 0] = V [3, 4, 6, 4, 0] :=
    (in_context torus7 [3, 4, 6, 4] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1860 : V [7, 5, 7, 1, 4] = V [2, 0, 2, 4, 6] := by
  have h0 : V [8, 2, 3, 4, 6] = V [7, 5, 7, 1, 7, 7, 4] :=
    inclusion torus215 torus1480 [7, 5] [7, 4] (by decide)
  have hl : V [8, 2, 3, 4, 6] = V [2, 0, 2, 4, 6] :=
    (in_context torus1429 [] [4, 6])
  have hr : V [7, 5, 7, 1, 7, 7, 4] = V [7, 5, 7, 1, 4] :=
    (in_context torus7 [7, 5, 7, 1] [4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1861 : V [7, 2, 0, 2, 4, 6] = V [5, 7, 1, 4] := by
  have h0 : V [5, 7, 1, 4] = V [7, 2, 0, 2, 4, 6] :=
    overlap torus7 torus1860 [7] [5, 7, 1, 4] (by decide)
  have hl : V [5, 7, 1, 4] = V [5, 7, 1, 4] :=
    rfl
  have hr : V [7, 2, 0, 2, 4, 6] = V [7, 2, 0, 2, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1862 : V [1, 8, 5, 7, 1, 4] = V [8, 3, 4, 6] := by
  have h0 : V [8, 3, 2, 2, 4, 6] = V [1, 8, 5, 7, 1, 4] :=
    overlap torus1558 torus1861 [1, 8] [2, 4, 6] (by decide)
  have hl : V [8, 3, 2, 2, 4, 6] = V [8, 3, 4, 6] :=
    (in_context torus2 [8, 3] [4, 6])
  have hr : V [1, 8, 5, 7, 1, 4] = V [1, 8, 5, 7, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1863 : V [7, 2, 0, 2, 4] = V [5, 7, 1, 4, 6] := by
  have h0 : V [7, 8, 2, 3, 4] = V [5, 7, 1, 7, 7, 4, 6] :=
    inclusion torus217 torus1480 [5] [7, 4, 6] (by decide)
  have hl : V [7, 8, 2, 3, 4] = V [7, 2, 0, 2, 4] :=
    (in_context torus1429 [7] [4])
  have hr : V [5, 7, 1, 7, 7, 4, 6] = V [5, 7, 1, 4, 6] :=
    (in_context torus7 [5, 7, 1] [4, 6])
  exact hl.symm.trans (h0.trans hr)

private theorem torus1866 : V [3, 2, 7, 1, 7] = V [2, 1, 2, 7, 6] := by
  have h0 : V [2, 1, 2, 7, 6] = V [3, 2, 7, 1, 7] :=
    overlap torus1434 torus1480 [3, 2] [7, 6] (by decide)
  have hl : V [2, 1, 2, 7, 6] = V [2, 1, 2, 7, 6] :=
    rfl
  have hr : V [3, 2, 7, 1, 7] = V [3, 2, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1874 : V [4, 5, 7, 5, 0] = V [2, 1, 2, 6, 8] := by
  have h0 : V [3, 2, 8, 6, 2, 8, 8, 2, 8] = V [4, 5, 7, 5, 8, 8, 0] :=
    overlap torus231 torus1486 [4, 5, 7, 5, 8] [8, 2, 8] (by decide)
  have hl : V [3, 2, 8, 6, 2, 8, 8, 2, 8] = V [2, 1, 2, 6, 8] :=
    ((in_context torus1434 [] [6, 2, 8, 8, 2, 8]).trans ((in_context torus8 [2, 1, 2, 6, 2] [2, 8]).trans (in_context torus2 [2, 1, 2, 6] [8])))
  have hr : V [4, 5, 7, 5, 8, 8, 0] = V [4, 5, 7, 5, 0] :=
    (in_context torus8 [4, 5, 7, 5] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1875 : V [6, 0, 7, 2, 8] = V [1, 6, 5, 8, 0] := by
  have h0 : V [5, 6, 7, 6, 7, 2, 8] = V [6, 7, 6, 8, 0] :=
    overlap torus125 torus1486 [6, 7, 6] [2, 8] (by decide)
  have hl : V [5, 6, 7, 6, 7, 2, 8] = V [6, 0, 7, 2, 8] :=
    (in_context torus1468 [] [7, 2, 8])
  have hr : V [6, 7, 6, 8, 0] = V [1, 6, 5, 8, 0] :=
    ((in_context torus1469 [] [8, 0]).trans (in_context torus1473 [] [8, 0]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1876 : V [8, 2, 7, 8, 2] = V [1, 8, 7, 0, 8] := by
  have h0 : V [7, 8, 0, 0, 8] = V [8, 2, 7, 8, 2] :=
    overlap torus1487 torus1485 [8, 2] [0, 8] (by decide)
  have hl : V [7, 8, 0, 0, 8] = V [1, 8, 7, 0, 8] :=
    (in_context torus1490 [] [0, 8])
  have hr : V [8, 2, 7, 8, 2] = V [8, 2, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1884 : V [5, 7, 5, 4, 2] = V [0, 8, 6, 2, 0] := by
  have h0 : V [5, 7, 5, 4, 3, 2, 1, 2, 8] = V [8, 7, 8, 2, 6, 2, 0] :=
    overlap torus244 torus1494 [8, 7, 8, 2, 6] [1, 2, 8] (by decide)
  have hl : V [5, 7, 5, 4, 3, 2, 1, 2, 8] = V [5, 7, 5, 4, 2] :=
    ((in_context torus1453 [5, 7] [2, 1, 2, 8]).trans ((in_context torus1435 [5, 7, 4, 1, 4] []).trans (in_context torus1454 [5, 7] [2])))
  have hr : V [8, 7, 8, 2, 6, 2, 0] = V [0, 8, 6, 2, 0] :=
    ((in_context torus1484 [] [2, 6, 2, 0]).trans (in_context torus2 [0, 8] [6, 2, 0]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1885 : V [5, 7, 4, 1, 4, 2, 8] = V [0, 8, 6] := by
  have h0 : V [0, 8, 6, 2, 0, 1, 2] = V [5, 7, 5, 3, 1, 3, 8] :=
    overlap torus1884 torus1553 [5, 7, 5] [1, 2] (by decide)
  have hl : V [0, 8, 6, 2, 0, 1, 2] = V [0, 8, 6] :=
    ((in_context torus0 [0, 8, 6, 2] [2]).trans (in_context torus2 [0, 8, 6] []))
  have hr : V [5, 7, 5, 3, 1, 3, 8] = V [5, 7, 4, 1, 4, 2, 8] :=
    (in_context torus1563 [5, 7] [8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1886 : V [5, 0, 8, 6, 2, 0] = V [7, 5, 4, 2] := by
  have h0 : V [7, 5, 4, 2] = V [5, 0, 8, 6, 2, 0] :=
    overlap torus5 torus1884 [5] [7, 5, 4, 2] (by decide)
  have hl : V [7, 5, 4, 2] = V [7, 5, 4, 2] :=
    rfl
  have hr : V [5, 0, 8, 6, 2, 0] = V [5, 0, 8, 6, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1887 : V [5, 0, 8, 6, 8, 2, 4, 0] = V [7, 4] := by
  have h0 : V [7, 5, 4, 2, 2, 1, 4, 3] = V [5, 0, 8, 6, 8, 2, 4, 0] :=
    overlap torus1886 torus1672 [5, 0, 8, 6] [2, 1, 4, 3] (by decide)
  have hl : V [7, 5, 4, 2, 2, 1, 4, 3] = V [7, 4] :=
    ((in_context torus2 [7, 5, 4] [1, 4, 3]).trans ((in_context torus1452 [7] [4, 3]).trans ((in_context torus1451 [7, 0] [3]).trans ((in_context torus1447 [7] [3]).trans (in_context torus3 [7, 4] [])))))
  have hr : V [5, 0, 8, 6, 8, 2, 4, 0] = V [5, 0, 8, 6, 8, 2, 4, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1889 : V [5, 0, 8, 6, 8, 2, 4] = V [7, 4, 1] := by
  have h0 : V [7, 4, 1] = V [5, 0, 8, 6, 8, 2, 4] :=
    overlap torus1887 torus0 [5, 0, 8, 6, 8, 2, 4] [1] (by decide)
  have hl : V [7, 4, 1] = V [7, 4, 1] :=
    rfl
  have hr : V [5, 0, 8, 6, 8, 2, 4] = V [5, 0, 8, 6, 8, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1890 : V [5, 0, 8, 6, 8, 3] = V [7, 5, 3, 1] := by
  have h0 : V [7, 5, 4, 2, 2, 0, 3, 4] = V [5, 0, 8, 6, 2, 2, 8, 3] :=
    overlap torus1886 torus1517 [5, 0, 8, 6, 2] [2, 0, 3, 4] (by decide)
  have hl : V [7, 5, 4, 2, 2, 0, 3, 4] = V [7, 5, 3, 1] :=
    ((in_context torus2 [7, 5, 4] [0, 3, 4]).trans (in_context torus1495 [7, 5] []))
  have hr : V [5, 0, 8, 6, 2, 2, 8, 3] = V [5, 0, 8, 6, 8, 3] :=
    (in_context torus2 [5, 0, 8, 6] [8, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1891 : V [5, 0, 8, 6, 8, 2] = V [7, 4, 1, 4] := by
  have h0 : V [7, 5, 4, 2, 2, 3] = V [5, 0, 8, 6, 8, 2] :=
    overlap torus1886 torus1438 [5, 0, 8, 6] [2, 3] (by decide)
  have hl : V [7, 5, 4, 2, 2, 3] = V [7, 4, 1, 4] :=
    ((in_context torus2 [7, 5, 4] [3]).trans (in_context torus1453 [7] []))
  have hr : V [5, 0, 8, 6, 8, 2] = V [5, 0, 8, 6, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1892 : V [5, 4, 2, 1, 3] = V [4, 1, 4, 0, 2] := by
  have h0 : V [4, 1, 4, 0, 2] = V [5, 4, 2, 1, 3] :=
    overlap torus1453 torus1500 [5, 4] [0, 2] (by decide)
  have hl : V [4, 1, 4, 0, 2] = V [4, 1, 4, 0, 2] :=
    rfl
  have hr : V [5, 4, 2, 1, 3] = V [5, 4, 2, 1, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1905 : V [7, 0, 0, 5, 6] = V [6, 1, 7, 5, 1] := by
  have h0 : V [6, 1, 7, 5, 1] = V [7, 0, 0, 5, 6] :=
    overlap torus1505 torus1461 [7, 0] [5, 1] (by decide)
  have hl : V [6, 1, 7, 5, 1] = V [6, 1, 7, 5, 1] :=
    rfl
  have hr : V [7, 0, 0, 5, 6] = V [7, 0, 0, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1925 : V [4, 1, 3, 8, 2] = V [0, 4, 5, 2, 1] := by
  have h0 : V [0, 4, 5, 3, 3, 2, 1] = V [4, 1, 3, 8, 2] :=
    overlap torus1554 torus1431 [4, 1, 3] [3, 2, 1] (by decide)
  have hl : V [0, 4, 5, 3, 3, 2, 1] = V [0, 4, 5, 2, 1] :=
    (in_context torus3 [0, 4, 5] [2, 1])
  have hr : V [4, 1, 3, 8, 2] = V [4, 1, 3, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1926 : V [5, 1, 4, 1, 3] = V [0, 5, 6, 3, 2] := by
  have h0 : V [6, 5, 1, 3, 2] = V [5, 1, 5, 0, 4, 5, 3] :=
    overlap torus1463 torus1554 [5, 1, 5] [1, 3, 2] (by decide)
  have hl : V [6, 5, 1, 3, 2] = V [0, 5, 6, 3, 2] :=
    (in_context torus1461 [] [3, 2])
  have hr : V [5, 1, 5, 0, 4, 5, 3] = V [5, 1, 4, 1, 3] :=
    (in_context torus1496 [5, 1] [3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1930 : V [4, 3, 5, 7, 6] = V [0, 4, 0, 6, 0] := by
  have h0 : V [0, 4, 6, 5, 6, 7, 0] = V [4, 3, 5, 7, 6] :=
    overlap torus1564 torus1474 [4, 3, 5] [6, 7, 0] (by decide)
  have hl : V [0, 4, 6, 5, 6, 7, 0] = V [0, 4, 0, 6, 0] :=
    ((in_context torus1466 [0, 4] [7, 0]).trans (in_context torus7 [0, 4, 0, 6] [0]))
  have hr : V [4, 3, 5, 7, 6] = V [4, 3, 5, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1932 : V [6, 1, 4, 1, 4] = V [0, 6, 7, 5, 3] := by
  have h0 : V [0, 6, 7, 5, 3] = V [6, 1, 4, 1, 4] :=
    overlap torus1569 torus1453 [6, 1] [3] (by decide)
  have hl : V [0, 6, 7, 5, 3] = V [0, 6, 7, 5, 3] :=
    rfl
  have hr : V [6, 1, 4, 1, 4] = V [6, 1, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1935 : V [7, 1, 5, 1, 5] = V [0, 7, 8, 6, 4] := by
  have h0 : V [0, 7, 8, 6, 4] = V [7, 1, 5, 1, 5] :=
    overlap torus1577 torus1462 [7, 1] [4] (by decide)
  have hl : V [0, 7, 8, 6, 4] = V [0, 7, 8, 6, 4] :=
    rfl
  have hr : V [7, 1, 5, 1, 5] = V [7, 1, 5, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1945 : V [5, 6, 3, 1, 3] = V [1, 5, 1, 4, 2] := by
  have h0 : V [1, 5, 1, 4, 2] = V [5, 6, 3, 1, 3] :=
    overlap torus1613 torus1444 [5, 6] [2] (by decide)
  have hl : V [1, 5, 1, 4, 2] = V [1, 5, 1, 4, 2] :=
    rfl
  have hr : V [5, 6, 3, 1, 3] = V [5, 6, 3, 1, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1946 : V [4, 5, 3, 8, 2] = V [1, 4, 1, 2, 1] := by
  have h0 : V [1, 4, 1, 3, 3, 2, 1] = V [4, 5, 3, 8, 2] :=
    overlap torus1614 torus1431 [4, 5, 3] [3, 2, 1] (by decide)
  have hl : V [1, 4, 1, 3, 3, 2, 1] = V [1, 4, 1, 2, 1] :=
    (in_context torus3 [1, 4, 1] [2, 1])
  have hr : V [4, 5, 3, 8, 2] = V [4, 5, 3, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1948 : V [6, 7, 4, 1, 4] = V [1, 6, 1, 5, 3] := by
  have h0 : V [1, 6, 1, 5, 3] = V [6, 7, 4, 1, 4] :=
    overlap torus1615 torus1453 [6, 7] [3] (by decide)
  have hl : V [1, 6, 1, 5, 3] = V [1, 6, 1, 5, 3] :=
    rfl
  have hr : V [6, 7, 4, 1, 4] = V [6, 7, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1951 : V [5, 1, 2, 4, 8] = V [3, 5, 6, 8, 0] := by
  have h0 : V [3, 5, 6, 8, 0] = V [5, 1, 2, 4, 2, 7, 1, 0, 7, 2, 8] :=
    overlap torus1623 torus1588 [5, 1, 2, 4, 2, 7, 1] [6, 8, 0] (by decide)
  have hl : V [3, 5, 6, 8, 0] = V [3, 5, 6, 8, 0] :=
    rfl
  have hr : V [5, 1, 2, 4, 2, 7, 1, 0, 7, 2, 8] = V [5, 1, 2, 4, 8] :=
    ((in_context torus1 [5, 1, 2, 4, 2, 7] [7, 2, 8]).trans ((in_context torus7 [5, 1, 2, 4, 2] [2, 8]).trans (in_context torus2 [5, 1, 2, 4] [8])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1952 : V [4, 2, 0, 5, 3, 5, 6, 8, 0] = V [8] := by
  have h0 : V [4, 2, 0, 1, 2, 4, 8] = V [2, 7, 1, 7, 5, 3, 3, 5, 6, 8, 0] :=
    overlap torus1656 torus1951 [2, 7, 1, 7, 5, 3] [1, 2, 4, 8] (by decide)
  have hl : V [4, 2, 0, 1, 2, 4, 8] = V [8] :=
    ((in_context torus0 [4, 2] [2, 4, 8]).trans ((in_context torus2 [4] [4, 8]).trans (in_context torus4 [] [8])))
  have hr : V [2, 7, 1, 7, 5, 3, 3, 5, 6, 8, 0] = V [4, 2, 0, 5, 3, 5, 6, 8, 0] :=
    (in_context torus1745 [] [3, 5, 6, 8, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1953 : V [4, 2, 0, 5, 3, 5, 6, 8] = V [8, 1] := by
  have h0 : V [8, 1] = V [4, 2, 0, 5, 3, 5, 6, 8] :=
    overlap torus1952 torus0 [4, 2, 0, 5, 3, 5, 6, 8] [1] (by decide)
  have hl : V [8, 1] = V [8, 1] :=
    rfl
  have hr : V [4, 2, 0, 5, 3, 5, 6, 8] = V [4, 2, 0, 5, 3, 5, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1954 : V [4, 2, 0, 5, 3, 5, 6, 7] = V [2, 8] := by
  have h0 : V [8, 7, 8, 0] = V [4, 2, 0, 5, 3, 5, 6, 8, 8, 7] :=
    overlap torus1952 torus1483 [4, 2, 0, 5, 3, 5, 6, 8] [7, 8, 0] (by decide)
  have hl : V [8, 7, 8, 0] = V [2, 8] :=
    ((in_context torus1484 [] [0]).trans ((in_context torus1430 [0] []).trans (in_context torus1433 [] [])))
  have hr : V [4, 2, 0, 5, 3, 5, 6, 8, 8, 7] = V [4, 2, 0, 5, 3, 5, 6, 7] :=
    (in_context torus8 [4, 2, 0, 5, 3, 5, 6] [7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1955 : V [4, 2, 0, 5, 3, 5, 7, 0] = V [2, 7] := by
  have h0 : V [2, 8, 8, 7] = V [4, 2, 0, 5, 3, 5, 6, 6, 7, 0] :=
    overlap torus1954 torus1478 [4, 2, 0, 5, 3, 5, 6] [8, 7] (by decide)
  have hl : V [2, 8, 8, 7] = V [2, 7] :=
    (in_context torus8 [2] [7])
  have hr : V [4, 2, 0, 5, 3, 5, 6, 6, 7, 0] = V [4, 2, 0, 5, 3, 5, 7, 0] :=
    (in_context torus6 [4, 2, 0, 5, 3, 5] [7, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1956 : V [4, 2, 0, 5, 3, 5, 6] = V [2, 8, 7] := by
  have h0 : V [8, 1, 8] = V [4, 2, 0, 5, 3, 5, 6] :=
    overlap torus1953 torus8 [4, 2, 0, 5, 3, 5, 6] [8] (by decide)
  have hl : V [8, 1, 8] = V [2, 8, 7] :=
    (in_context torus1489 [] [])
  have hr : V [4, 2, 0, 5, 3, 5, 6] = V [4, 2, 0, 5, 3, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1957 : V [3, 5, 1, 2, 4, 2, 8, 7] = V [5, 6] := by
  have h0 : V [3, 6, 5, 4, 5, 2, 2, 0, 5, 3, 5, 6] = V [5, 6, 7, 8, 2, 2, 8, 7] :=
    overlap torus176 torus1956 [5, 6, 7, 8, 2] [2, 0, 5, 3, 5, 6] (by decide)
  have hl : V [3, 6, 5, 4, 5, 2, 2, 0, 5, 3, 5, 6] = V [5, 6] :=
    ((in_context torus1462 [3] [5, 2, 2, 0, 5, 3, 5, 6]).trans ((in_context torus5 [3, 5, 1] [2, 2, 0, 5, 3, 5, 6]).trans ((in_context torus2 [3, 5, 1] [0, 5, 3, 5, 6]).trans ((in_context torus1 [3, 5] [5, 3, 5, 6]).trans ((in_context torus5 [3] [3, 5, 6]).trans (in_context torus3 [] [5, 6]))))))
  have hr : V [5, 6, 7, 8, 2, 2, 8, 7] = V [3, 5, 1, 2, 4, 2, 8, 7] :=
    (in_context torus1823 [] [2, 8, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1958 : V [3, 5, 1, 2, 4, 2, 8] = V [5, 6, 7] := by
  have h0 : V [3, 6, 5, 4, 5, 2, 2, 0, 5, 3, 5, 6, 7] = V [5, 6, 7, 8, 2, 2, 8] :=
    overlap torus176 torus1954 [5, 6, 7, 8, 2] [2, 0, 5, 3, 5, 6, 7] (by decide)
  have hl : V [3, 6, 5, 4, 5, 2, 2, 0, 5, 3, 5, 6, 7] = V [5, 6, 7] :=
    ((in_context torus1462 [3] [5, 2, 2, 0, 5, 3, 5, 6, 7]).trans ((in_context torus5 [3, 5, 1] [2, 2, 0, 5, 3, 5, 6, 7]).trans ((in_context torus2 [3, 5, 1] [0, 5, 3, 5, 6, 7]).trans ((in_context torus1 [3, 5] [5, 3, 5, 6, 7]).trans ((in_context torus5 [3] [3, 5, 6, 7]).trans (in_context torus3 [] [5, 6, 7]))))))
  have hr : V [5, 6, 7, 8, 2, 2, 8] = V [3, 5, 1, 2, 4, 2, 8] :=
    (in_context torus1823 [] [2, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1960 : V [4, 2, 0, 5, 3, 5, 7] = V [2, 7, 1] := by
  have h0 : V [2, 7, 1] = V [4, 2, 0, 5, 3, 5, 7] :=
    overlap torus1955 torus0 [4, 2, 0, 5, 3, 5, 7] [1] (by decide)
  have hl : V [2, 7, 1] = V [2, 7, 1] :=
    rfl
  have hr : V [4, 2, 0, 5, 3, 5, 7] = V [4, 2, 0, 5, 3, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1964 : V [8, 7, 5, 7, 1] = V [2, 3, 4, 6, 4] := by
  have h0 : V [3, 0, 1, 3, 8, 7, 5, 7, 1] = V [2, 3, 4, 6, 4] :=
    overlap torus1441 torus1630 [2, 3, 4] [1, 3, 8, 7, 5, 7, 1] (by decide)
  have hl : V [3, 0, 1, 3, 8, 7, 5, 7, 1] = V [8, 7, 5, 7, 1] :=
    ((in_context torus0 [3] [3, 8, 7, 5, 7, 1]).trans (in_context torus3 [] [8, 7, 5, 7, 1]))
  have hr : V [2, 3, 4, 6, 4] = V [2, 3, 4, 6, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1967 : V [3, 5, 2, 1, 2] = V [0, 6, 4, 6, 7] := by
  have h0 : V [0, 6, 4, 6, 7] = V [3, 5, 3, 2, 7, 1, 0, 7, 8] :=
    overlap torus1645 torus1475 [3, 5, 3, 2, 7, 1] [6, 7] (by decide)
  have hl : V [0, 6, 4, 6, 7] = V [0, 6, 4, 6, 7] :=
    rfl
  have hr : V [3, 5, 3, 2, 7, 1, 0, 7, 8] = V [3, 5, 2, 1, 2] :=
    ((in_context torus1 [3, 5, 3, 2, 7] [7, 8]).trans ((in_context torus7 [3, 5, 3, 2] [8]).trans (in_context torus1434 [3, 5] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1968 : V [6, 1, 3, 5, 2] = V [4, 6, 7, 2, 0] := by
  have h0 : V [4, 6, 8, 8, 7, 2, 0] = V [6, 1, 3, 5, 3, 8, 8, 3, 2] :=
    overlap torus1650 torus1558 [6, 1, 3, 5, 3, 8] [8, 7, 2, 0] (by decide)
  have hl : V [4, 6, 8, 8, 7, 2, 0] = V [4, 6, 7, 2, 0] :=
    (in_context torus8 [4, 6] [7, 2, 0])
  have hr : V [6, 1, 3, 5, 3, 8, 8, 3, 2] = V [6, 1, 3, 5, 2] :=
    ((in_context torus8 [6, 1, 3, 5, 3] [3, 2]).trans (in_context torus3 [6, 1, 3, 5] [2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1969 : V [0, 6, 4, 6, 7, 2, 0] = V [3, 5, 2] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 5, 2] = V [6, 5, 6, 7, 4, 6, 7, 2, 0] :=
    overlap torus117 torus1968 [6, 5, 6, 7] [1, 3, 5, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 5, 2] = V [3, 5, 2] :=
    ((in_context torus143 [] [1, 3, 5, 2]).trans ((in_context torus1428 [] [3, 2, 1, 3, 5, 2]).trans ((in_context torus3 [0, 2] [2, 1, 3, 5, 2]).trans ((in_context torus2 [0] [1, 3, 5, 2]).trans (in_context torus0 [] [3, 5, 2])))))
  have hr : V [6, 5, 6, 7, 4, 6, 7, 2, 0] = V [0, 6, 4, 6, 7, 2, 0] :=
    ((in_context torus204 [] [7, 2, 0]).trans ((in_context torus1434 [3, 5] [7, 7, 2, 0]).trans ((in_context torus1967 [] [7, 7, 2, 0]).trans (in_context torus7 [0, 6, 4, 6] [7, 2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1970 : V [6, 4, 6, 7, 2, 0] = V [1, 3, 5, 2] := by
  have h0 : V [1, 3, 5, 2] = V [6, 4, 6, 7, 2, 0] :=
    overlap torus6 torus1968 [6] [1, 3, 5, 2] (by decide)
  have hl : V [1, 3, 5, 2] = V [1, 3, 5, 2] :=
    rfl
  have hr : V [6, 4, 6, 7, 2, 0] = V [6, 4, 6, 7, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1971 : V [6, 4, 6, 7, 8, 2] = V [1, 3, 5, 3] := by
  have h0 : V [1, 3, 5, 2, 2, 3] = V [6, 4, 6, 7, 8, 2] :=
    overlap torus1970 torus1438 [6, 4, 6, 7] [2, 3] (by decide)
  have hl : V [1, 3, 5, 2, 2, 3] = V [1, 3, 5, 3] :=
    (in_context torus2 [1, 3, 5] [3])
  have hr : V [6, 4, 6, 7, 8, 2] = V [6, 4, 6, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1972 : V [8, 1, 5, 7, 5] = V [6, 2, 0, 2, 4] := by
  have h0 : V [6, 8, 2, 3, 4] = V [8, 1, 5, 7, 4, 1, 0, 4, 5] :=
    overlap torus1652 torus1448 [8, 1, 5, 7, 4, 1] [3, 4] (by decide)
  have hl : V [6, 8, 2, 3, 4] = V [6, 2, 0, 2, 4] :=
    (in_context torus1429 [6] [4])
  have hr : V [8, 1, 5, 7, 4, 1, 0, 4, 5] = V [8, 1, 5, 7, 5] :=
    ((in_context torus1 [8, 1, 5, 7, 4] [4, 5]).trans (in_context torus4 [8, 1, 5, 7] [5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1975 : V [5, 3, 2, 7, 2] = V [0, 5, 8, 6, 0] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 5, 3, 2, 7, 2] = V [5, 4, 5, 6, 8, 6, 0] :=
    overlap torus108 torus1655 [5, 4, 5, 6] [1, 5, 3, 2, 7, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 5, 3, 2, 7, 2] = V [5, 3, 2, 7, 2] :=
    ((in_context torus143 [] [1, 5, 3, 2, 7, 2]).trans ((in_context torus1428 [] [3, 2, 1, 5, 3, 2, 7, 2]).trans ((in_context torus3 [0, 2] [2, 1, 5, 3, 2, 7, 2]).trans ((in_context torus2 [0] [1, 5, 3, 2, 7, 2]).trans (in_context torus0 [] [5, 3, 2, 7, 2])))))
  have hr : V [5, 4, 5, 6, 8, 6, 0] = V [0, 5, 8, 6, 0] :=
    ((in_context torus1457 [] [6, 8, 6, 0]).trans (in_context torus6 [0, 5] [8, 6, 0]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus1981 : V [8, 6, 0, 2, 7] = V [5, 1, 5, 3, 2] := by
  have h0 : V [5, 1, 5, 3, 2] = V [8, 6, 0, 2, 7] :=
    overlap torus8 torus1668 [8] [5, 1, 5, 3, 2] (by decide)
  have hl : V [5, 1, 5, 3, 2] = V [5, 1, 5, 3, 2] :=
    rfl
  have hr : V [8, 6, 0, 2, 7] = V [8, 6, 0, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1982 : V [6, 1, 6, 4, 3] = V [2, 7, 0, 3, 8] := by
  have h0 : V [2, 7, 0, 3, 8] = V [6, 1, 6, 4, 3] :=
    overlap torus1671 torus8 [6, 1, 6, 4, 3] [8] (by decide)
  have hl : V [2, 7, 0, 3, 8] = V [2, 7, 0, 3, 8] :=
    rfl
  have hr : V [6, 1, 6, 4, 3] = V [6, 1, 6, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1984 : V [7, 2, 7, 0, 3, 8] = V [5, 1, 5, 3] := by
  have h0 : V [0, 6, 7, 6, 4, 3] = V [7, 2, 7, 0, 3, 8] :=
    overlap torus1470 torus1982 [7] [6, 4, 3] (by decide)
  have hl : V [0, 6, 7, 6, 4, 3] = V [5, 1, 5, 3] :=
    ((in_context torus1469 [0] [4, 3]).trans ((in_context torus1465 [] [4, 3]).trans (in_context torus1462 [] [3])))
  have hr : V [7, 2, 7, 0, 3, 8] = V [7, 2, 7, 0, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1988 : V [7, 0, 3, 8, 3] = V [2, 6, 1, 6, 4] := by
  have h0 : V [2, 6, 1, 6, 4] = V [7, 0, 3, 8, 3] :=
    overlap torus7 torus1677 [7] [2, 6, 1, 6, 4] (by decide)
  have hl : V [2, 6, 1, 6, 4] = V [2, 6, 1, 6, 4] :=
    rfl
  have hr : V [7, 0, 3, 8, 3] = V [7, 0, 3, 8, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1989 : V [7, 1, 7, 5, 4] = V [3, 8, 0, 4, 2] := by
  have h0 : V [3, 8, 0, 4, 2] = V [7, 1, 7, 5, 4] :=
    overlap torus1678 torus2 [7, 1, 7, 5, 4] [2] (by decide)
  have hl : V [3, 8, 0, 4, 2] = V [3, 8, 0, 4, 2] :=
    rfl
  have hr : V [7, 1, 7, 5, 4] = V [7, 1, 7, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1992 : V [7, 3, 8, 0, 4] = V [1, 7, 5, 4, 2] := by
  have h0 : V [1, 7, 5, 4, 2] = V [7, 3, 8, 0, 4] :=
    overlap torus7 torus1678 [7] [1, 7, 5, 4, 2] (by decide)
  have hl : V [1, 7, 5, 4, 2] = V [1, 7, 5, 4, 2] :=
    rfl
  have hr : V [7, 3, 8, 0, 4] = V [7, 3, 8, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1996 : V [4, 2, 4, 6, 0] = V [1, 8, 3, 8, 6] := by
  have h0 : V [4, 2, 4, 6, 0] = V [1, 8, 3, 8, 6] :=
    overlap torus1 torus1680 [1] [4, 2, 4, 6, 0] (by decide)
  have hl : V [4, 2, 4, 6, 0] = V [4, 2, 4, 6, 0] :=
    rfl
  have hr : V [1, 8, 3, 8, 6] = V [1, 8, 3, 8, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus1997 : V [4, 1, 8, 3, 8, 6] = V [2, 4, 6, 0] := by
  have h0 : V [2, 4, 6, 0] = V [4, 1, 8, 3, 8, 6] :=
    overlap torus4 torus1996 [4] [2, 4, 6, 0] (by decide)
  have hl : V [2, 4, 6, 0] = V [2, 4, 6, 0] :=
    rfl
  have hr : V [4, 1, 8, 3, 8, 6] = V [4, 1, 8, 3, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1998 : V [4, 2, 7, 1, 7] = V [2, 0, 5, 3, 5] := by
  have h0 : V [2, 0, 5, 3, 5] = V [4, 2, 7, 1, 7] :=
    overlap torus1683 torus5 [4, 2, 7, 1, 7] [5] (by decide)
  have hl : V [2, 0, 5, 3, 5] = V [2, 0, 5, 3, 5] :=
    rfl
  have hr : V [4, 2, 7, 1, 7] = V [4, 2, 7, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus1999 : V [4, 2, 0, 5, 3] = V [2, 7, 1, 7, 5] := by
  have h0 : V [2, 7, 1, 7, 5] = V [4, 2, 0, 5, 3] :=
    overlap torus4 torus1683 [4] [2, 7, 1, 7, 5] (by decide)
  have hl : V [2, 7, 1, 7, 5] = V [2, 7, 1, 7, 5] :=
    rfl
  have hr : V [4, 2, 0, 5, 3] = V [4, 2, 0, 5, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2000 : V [4, 2, 8, 6, 1] = V [2, 0, 5, 3, 6] := by
  have h0 : V [2, 0, 5, 3, 6] = V [4, 2, 8, 6, 1] :=
    overlap torus1683 torus1579 [4, 2] [6] (by decide)
  have hl : V [2, 0, 5, 3, 6] = V [2, 0, 5, 3, 6] :=
    rfl
  have hr : V [4, 2, 8, 6, 1] = V [4, 2, 8, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2001 : V [8, 0, 4, 2, 4] = V [3, 7, 1, 7, 5] := by
  have h0 : V [3, 7, 1, 7, 5] = V [8, 0, 4, 2, 4] :=
    overlap torus8 torus1684 [8] [3, 7, 1, 7, 5] (by decide)
  have hl : V [3, 7, 1, 7, 5] = V [3, 7, 1, 7, 5] :=
    rfl
  have hr : V [8, 0, 4, 2, 4] = V [8, 0, 4, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2002 : V [5, 3, 2, 7, 1] = V [3, 0, 6, 4, 7] := by
  have h0 : V [3, 0, 6, 4, 7] = V [5, 3, 2, 7, 1] :=
    overlap torus1687 torus7 [5, 3, 2, 7, 1] [7] (by decide)
  have hl : V [3, 0, 6, 4, 7] = V [3, 0, 6, 4, 7] :=
    rfl
  have hr : V [5, 3, 2, 7, 1] = V [5, 3, 2, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2003 : V [5, 3, 0, 6, 4, 7] = V [3, 2, 7, 1] := by
  have h0 : V [3, 2, 7, 1] = V [5, 3, 0, 6, 4, 7] :=
    overlap torus5 torus2002 [5] [3, 2, 7, 1] (by decide)
  have hl : V [3, 2, 7, 1] = V [3, 2, 7, 1] :=
    rfl
  have hr : V [5, 3, 0, 6, 4, 7] = V [5, 3, 0, 6, 4, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2004 : V [5, 3, 0, 6, 4, 6, 7, 8] = V [3, 2] := by
  have h0 : V [3, 2, 7, 1, 0, 7] = V [5, 3, 0, 6, 4, 6, 7, 8] :=
    overlap torus2003 torus1476 [5, 3, 0, 6, 4] [0, 7] (by decide)
  have hl : V [3, 2, 7, 1, 0, 7] = V [3, 2] :=
    ((in_context torus1 [3, 2, 7] [7]).trans (in_context torus7 [3, 2] []))
  have hr : V [5, 3, 0, 6, 4, 6, 7, 8] = V [5, 3, 0, 6, 4, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2006 : V [5, 3, 0, 6, 4, 6, 7] = V [2, 1, 2] := by
  have h0 : V [3, 2, 8] = V [5, 3, 0, 6, 4, 6, 7] :=
    overlap torus2004 torus8 [5, 3, 0, 6, 4, 6, 7] [8] (by decide)
  have hl : V [3, 2, 8] = V [2, 1, 2] :=
    (in_context torus1434 [] [])
  have hr : V [5, 3, 0, 6, 4, 6, 7] = V [5, 3, 0, 6, 4, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2009 : V [5, 3, 0, 6, 4] = V [2, 1, 2, 7, 6] := by
  have h0 : V [3, 2, 7, 1, 7] = V [5, 3, 0, 6, 4] :=
    overlap torus5 torus1687 [5] [3, 2, 7, 1, 7] (by decide)
  have hl : V [3, 2, 7, 1, 7] = V [2, 1, 2, 7, 6] :=
    (in_context torus1866 [] [])
  have hr : V [5, 3, 0, 6, 4] = V [5, 3, 0, 6, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2010 : V [5, 2, 1, 2, 7] = V [3, 0, 6, 4, 6] := by
  have h0 : V [3, 0, 6, 4, 6] = V [5, 3, 2, 8, 7] :=
    overlap torus1687 torus1481 [5, 3, 2] [6] (by decide)
  have hl : V [3, 0, 6, 4, 6] = V [3, 0, 6, 4, 6] :=
    rfl
  have hr : V [5, 3, 2, 8, 7] = V [5, 2, 1, 2, 7] :=
    (in_context torus1434 [5] [7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2014 : V [2, 3, 8, 6, 7] = V [1, 2, 1, 7, 1] := by
  have h0 : V [1, 2, 1, 7, 1] = V [2, 3, 8, 6, 7] :=
    overlap torus2 torus1709 [2] [1, 2, 1, 7, 1] (by decide)
  have hl : V [1, 2, 1, 7, 1] = V [1, 2, 1, 7, 1] :=
    rfl
  have hr : V [2, 3, 8, 6, 7] = V [2, 3, 8, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2015 : V [5, 6, 4, 2, 3] = V [1, 5, 1, 3, 1] := by
  have h0 : V [1, 5, 1, 3, 1] = V [5, 6, 4, 2, 3] :=
    overlap torus5 torus1726 [5] [1, 5, 1, 3, 1] (by decide)
  have hl : V [1, 5, 1, 3, 1] = V [1, 5, 1, 3, 1] :=
    rfl
  have hr : V [5, 6, 4, 2, 3] = V [5, 6, 4, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2017 : V [7, 8, 6, 4, 5] = V [1, 7, 1, 5, 1] := by
  have h0 : V [1, 7, 1, 5, 1] = V [7, 8, 6, 4, 5] :=
    overlap torus7 torus1731 [7] [1, 7, 1, 5, 1] (by decide)
  have hl : V [1, 7, 1, 5, 1] = V [1, 7, 1, 5, 1] :=
    rfl
  have hr : V [7, 8, 6, 4, 5] = V [7, 8, 6, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2018 : V [5, 1, 2, 4, 2] = V [3, 5, 6, 7, 8] := by
  have h0 : V [3, 5, 7, 0, 7] = V [5, 1, 2, 4, 2] :=
    overlap torus1732 torus7 [5, 1, 2, 4, 2] [7] (by decide)
  have hl : V [3, 5, 7, 0, 7] = V [3, 5, 6, 7, 8] :=
    (in_context torus1476 [3, 5] [])
  have hr : V [5, 1, 2, 4, 2] = V [5, 1, 2, 4, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2019 : V [0, 5, 3, 5, 6, 7, 8] = V [2, 4, 2] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 2, 4, 2] = V [5, 4, 5, 6, 3, 5, 6, 7, 8] :=
    overlap torus108 torus2018 [5, 4, 5, 6] [1, 2, 4, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 2, 4, 2] = V [2, 4, 2] :=
    ((in_context torus143 [] [1, 2, 4, 2]).trans ((in_context torus1428 [] [3, 2, 1, 2, 4, 2]).trans ((in_context torus3 [0, 2] [2, 1, 2, 4, 2]).trans ((in_context torus2 [0] [1, 2, 4, 2]).trans (in_context torus0 [] [2, 4, 2])))))
  have hr : V [5, 4, 5, 6, 3, 5, 6, 7, 8] = V [0, 5, 3, 5, 6, 7, 8] :=
    ((in_context torus184 [] [6, 7, 8]).trans ((in_context torus1480 [2, 4, 2] [6, 7, 8]).trans (in_context torus1741 [] [6, 7, 8])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2020 : V [5, 3, 5, 6, 7, 8] = V [1, 2, 4, 2] := by
  have h0 : V [1, 2, 4, 2] = V [5, 3, 5, 6, 7, 8] :=
    overlap torus5 torus2018 [5] [1, 2, 4, 2] (by decide)
  have hl : V [1, 2, 4, 2] = V [1, 2, 4, 2] :=
    rfl
  have hr : V [5, 3, 5, 6, 7, 8] = V [5, 3, 5, 6, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2022 : V [6, 1, 3, 5, 3] = V [4, 6, 7, 8, 2] := by
  have h0 : V [4, 6, 8, 0, 8] = V [6, 1, 3, 5, 3] :=
    overlap torus1733 torus8 [6, 1, 3, 5, 3] [8] (by decide)
  have hl : V [4, 6, 8, 0, 8] = V [4, 6, 7, 8, 2] :=
    (in_context torus1485 [4, 6] [])
  have hr : V [6, 1, 3, 5, 3] = V [6, 1, 3, 5, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2024 : V [7, 1, 4, 6, 4] = V [5, 7, 2, 0, 2] := by
  have h0 : V [5, 7, 2, 0, 2] = V [7, 1, 4, 6, 4] :=
    overlap torus1734 torus2 [7, 1, 4, 6, 4] [2] (by decide)
  have hl : V [5, 7, 2, 0, 2] = V [5, 7, 2, 0, 2] :=
    rfl
  have hr : V [7, 1, 4, 6, 4] = V [7, 1, 4, 6, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2025 : V [7, 1, 4, 6, 3, 1] = V [5, 7, 8, 3] := by
  have h0 : V [5, 7, 2, 0, 2, 0, 3, 4] = V [7, 1, 4, 6, 3, 1] :=
    overlap torus2024 torus1495 [7, 1, 4, 6] [0, 3, 4] (by decide)
  have hl : V [5, 7, 2, 0, 2, 0, 3, 4] = V [5, 7, 8, 3] :=
    (in_context torus1512 [5, 7] [])
  have hr : V [7, 1, 4, 6, 3, 1] = V [7, 1, 4, 6, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2026 : V [7, 5, 7, 2, 0, 2] = V [1, 4, 6, 4] := by
  have h0 : V [1, 4, 6, 4] = V [7, 5, 7, 2, 0, 2] :=
    overlap torus7 torus2024 [7] [1, 4, 6, 4] (by decide)
  have hl : V [1, 4, 6, 4] = V [1, 4, 6, 4] :=
    rfl
  have hr : V [7, 5, 7, 2, 0, 2] = V [7, 5, 7, 2, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2030 : V [2, 7, 5, 7, 1] = V [0, 2, 4, 6, 4] := by
  have h0 : V [0, 2, 4, 6, 4] = V [2, 7, 5, 7, 1] :=
    overlap torus2 torus1736 [2] [0, 2, 4, 6, 4] (by decide)
  have hl : V [0, 2, 4, 6, 4] = V [0, 2, 4, 6, 4] :=
    rfl
  have hr : V [2, 7, 5, 7, 1] = V [2, 7, 5, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2034 : V [2, 4, 2, 8, 7] = V [0, 5, 3, 5, 6] := by
  have h0 : V [0, 5, 3, 5, 6] = V [2, 4, 2, 8, 7] :=
    overlap torus1741 torus1481 [2, 4, 2] [6] (by decide)
  have hl : V [0, 5, 3, 5, 6] = V [0, 5, 3, 5, 6] :=
    rfl
  have hr : V [2, 4, 2, 8, 7] = V [2, 4, 2, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2036 : V [5, 8, 6, 0, 2] = V [1, 5, 3, 2, 7] := by
  have h0 : V [1, 5, 3, 2, 7] = V [5, 8, 6, 0, 2] :=
    overlap torus5 torus1744 [5] [1, 5, 3, 2, 7] (by decide)
  have hl : V [1, 5, 3, 2, 7] = V [1, 5, 3, 2, 7] :=
    rfl
  have hr : V [5, 8, 6, 0, 2] = V [5, 8, 6, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2037 : V [7, 1, 7, 5, 3] = V [2, 4, 2, 0, 5] := by
  have h0 : V [7, 1, 7, 5, 3] = V [2, 4, 2, 0, 5] :=
    overlap torus2 torus1745 [2] [7, 1, 7, 5, 3] (by decide)
  have hl : V [7, 1, 7, 5, 3] = V [7, 1, 7, 5, 3] :=
    rfl
  have hr : V [2, 4, 2, 0, 5] = V [2, 4, 2, 0, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2041 : V [6, 8, 2, 4, 2] = V [1, 6, 3, 5, 1] := by
  have h0 : V [1, 6, 3, 6, 5, 4, 5] = V [6, 8, 2, 4, 2, 0, 3, 4, 3, 2, 3] :=
    overlap torus1746 torus111 [6, 8, 2, 4, 2, 0] [6, 5, 4, 5] (by decide)
  have hl : V [1, 6, 3, 6, 5, 4, 5] = V [1, 6, 3, 5, 1] :=
    ((in_context torus1462 [1, 6, 3] [5]).trans (in_context torus5 [1, 6, 3, 5, 1] []))
  have hr : V [6, 8, 2, 4, 2, 0, 3, 4, 3, 2, 3] = V [6, 8, 2, 4, 2] :=
    ((in_context torus1544 [6, 8, 2, 4] [3, 2, 3]).trans ((in_context torus3 [6, 8, 2, 4, 1, 2, 8] [2, 3]).trans ((in_context torus1428 [6, 8, 2, 4, 1] [3]).trans ((in_context torus1 [6, 8, 2, 4] [2, 3, 3]).trans (in_context torus3 [6, 8, 2, 4, 2] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2042 : V [8, 6, 5, 3, 5] = V [0, 8, 4, 2, 0] := by
  have h0 : V [8, 7, 8, 2, 4, 2, 0] = V [7, 1, 7, 1, 6, 3, 5] :=
    overlap torus1481 torus1747 [7, 1, 7] [8, 2, 4, 2, 0] (by decide)
  have hl : V [8, 7, 8, 2, 4, 2, 0] = V [0, 8, 4, 2, 0] :=
    ((in_context torus1484 [] [2, 4, 2, 0]).trans (in_context torus2 [0, 8] [4, 2, 0]))
  have hr : V [7, 1, 7, 1, 6, 3, 5] = V [8, 6, 5, 3, 5] :=
    (in_context torus1578 [] [3, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2044 : V [6, 4, 3, 8, 3] = V [0, 6, 2, 7, 0] := by
  have h0 : V [6, 4, 3, 8, 3] = V [0, 6, 2, 7, 0] :=
    overlap torus1749 torus3 [0, 6, 2, 7, 0] [3] (by decide)
  have hl : V [6, 4, 3, 8, 3] = V [6, 4, 3, 8, 3] :=
    rfl
  have hr : V [0, 6, 2, 7, 0] = V [0, 6, 2, 7, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2046 : V [7, 5, 4, 2, 4] = V [0, 7, 3, 8, 0] := by
  have h0 : V [7, 5, 4, 2, 4] = V [0, 7, 3, 8, 0] :=
    overlap torus1752 torus4 [0, 7, 3, 8, 0] [4] (by decide)
  have hl : V [7, 5, 4, 2, 4] = V [7, 5, 4, 2, 4] :=
    rfl
  have hr : V [0, 7, 3, 8, 0] = V [0, 7, 3, 8, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2047 : V [4, 2, 4, 5, 7] = V [1, 8, 3, 7, 1] := by
  have h0 : V [4, 2, 4, 5, 7] = V [1, 8, 3, 7, 1] :=
    overlap torus1 torus1754 [1] [4, 2, 4, 5, 7] (by decide)
  have hl : V [4, 2, 4, 5, 7] = V [4, 2, 4, 5, 7] :=
    rfl
  have hr : V [1, 8, 3, 7, 1] = V [1, 8, 3, 7, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2048 : V [4, 1, 8, 3, 7, 1] = V [2, 4, 5, 7] := by
  have h0 : V [2, 4, 5, 7] = V [4, 1, 8, 3, 7, 1] :=
    overlap torus4 torus2047 [4] [2, 4, 5, 7] (by decide)
  have hl : V [2, 4, 5, 7] = V [2, 4, 5, 7] :=
    rfl
  have hr : V [4, 1, 8, 3, 7, 1] = V [4, 1, 8, 3, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2049 : V [3, 7, 2, 1, 6] = V [0, 3, 5, 6, 8] := by
  have h0 : V [0, 3, 4, 4, 5, 6, 8] = V [3, 2, 2, 7, 2, 1, 6] :=
    overlap torus1439 torus1764 [3, 2] [4, 5, 6, 8] (by decide)
  have hl : V [0, 3, 4, 4, 5, 6, 8] = V [0, 3, 5, 6, 8] :=
    (in_context torus4 [0, 3] [5, 6, 8])
  have hr : V [3, 2, 2, 7, 2, 1, 6] = V [3, 7, 2, 1, 6] :=
    (in_context torus2 [3] [7, 2, 1, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2050 : V [7, 2, 1, 6, 8] = V [2, 3, 4, 5, 6] := by
  have h0 : V [2, 3, 4, 5, 6] = V [7, 2, 1, 6, 8] :=
    overlap torus1768 torus6 [7, 2, 1, 6, 8] [6] (by decide)
  have hl : V [2, 3, 4, 5, 6] = V [2, 3, 4, 5, 6] :=
    rfl
  have hr : V [7, 2, 1, 6, 8] = V [7, 2, 1, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2053 : V [4, 8, 3, 1, 7] = V [0, 4, 6, 7, 2] := by
  have h0 : V [0, 4, 5, 5, 6, 7, 2] = V [4, 3, 3, 8, 3, 1, 7] :=
    overlap torus1448 torus1783 [4, 3] [5, 6, 7, 2] (by decide)
  have hl : V [0, 4, 5, 5, 6, 7, 2] = V [0, 4, 6, 7, 2] :=
    (in_context torus5 [0, 4] [6, 7, 2])
  have hr : V [4, 3, 3, 8, 3, 1, 7] = V [4, 8, 3, 1, 7] :=
    (in_context torus3 [4] [8, 3, 1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2054 : V [8, 3, 1, 7, 2] = V [3, 4, 5, 6, 7] := by
  have h0 : V [3, 4, 5, 6, 7] = V [8, 3, 1, 7, 2] :=
    overlap torus1786 torus7 [8, 3, 1, 7, 2] [7] (by decide)
  have hl : V [3, 4, 5, 6, 7] = V [3, 4, 5, 6, 7] :=
    rfl
  have hr : V [8, 3, 1, 7, 2] = V [8, 3, 1, 7, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2055 : V [4, 2, 4, 5, 6] = V [1, 8, 3, 8, 7] := by
  have h0 : V [4, 2, 5, 0, 5] = V [1, 8, 3, 8, 7] :=
    overlap torus1792 torus5 [1, 8, 3, 8, 7] [5] (by decide)
  have hl : V [4, 2, 5, 0, 5] = V [4, 2, 4, 5, 6] :=
    (in_context torus1458 [4, 2] [])
  have hr : V [1, 8, 3, 8, 7] = V [1, 8, 3, 8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2057 : V [7, 2, 3, 5, 3] = V [1, 7, 4, 6, 1] := by
  have h0 : V [6, 7, 0, 6, 4, 6, 1] = V [7, 8, 2, 0, 2, 5, 3] :=
    overlap torus1478 torus1834 [7, 8] [6, 4, 6, 1] (by decide)
  have hl : V [6, 7, 0, 6, 4, 6, 1] = V [1, 7, 4, 6, 1] :=
    ((in_context torus1482 [] [6, 4, 6, 1]).trans (in_context torus6 [1, 7] [4, 6, 1]))
  have hr : V [7, 8, 2, 0, 2, 5, 3] = V [7, 2, 3, 5, 3] :=
    ((in_context torus1430 [7] [2, 5, 3]).trans ((in_context torus1436 [7] [2, 5, 3]).trans ((in_context torus1428 [7, 1] [5, 3]).trans (in_context torus1 [7] [2, 3, 5, 3]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2059 : V [3, 8, 7, 5, 7] = V [0, 3, 6, 4, 0] := by
  have h0 : V [0, 3, 4, 4, 6, 4, 0] = V [3, 2, 2, 8, 7, 5, 7] :=
    overlap torus1439 torus1856 [3, 2] [4, 6, 4, 0] (by decide)
  have hl : V [0, 3, 4, 4, 6, 4, 0] = V [0, 3, 6, 4, 0] :=
    (in_context torus4 [0, 3] [6, 4, 0])
  have hr : V [3, 2, 2, 8, 7, 5, 7] = V [3, 8, 7, 5, 7] :=
    (in_context torus2 [3] [8, 7, 5, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2061 : V [6, 5, 7, 2, 8] = V [0, 6, 0, 8, 0] := by
  have h0 : V [6, 5, 7, 2, 8] = V [0, 5, 1, 6, 5, 8, 0] :=
    overlap torus1465 torus1875 [0, 5] [7, 2, 8] (by decide)
  have hl : V [6, 5, 7, 2, 8] = V [6, 5, 7, 2, 8] :=
    rfl
  have hr : V [0, 5, 1, 6, 5, 8, 0] = V [0, 6, 0, 8, 0] :=
    (in_context torus1509 [0] [8, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2062 : V [7, 5, 4, 2, 1] = V [5, 0, 8, 6, 2] := by
  have h0 : V [7, 5, 4, 2, 1] = V [5, 0, 8, 6, 2] :=
    overlap torus1886 torus0 [5, 0, 8, 6, 2] [1] (by decide)
  have hl : V [7, 5, 4, 2, 1] = V [7, 5, 4, 2, 1] :=
    rfl
  have hr : V [5, 0, 8, 6, 2] = V [5, 0, 8, 6, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2063 : V [7, 5, 0, 8, 6, 2] = V [5, 4, 2, 1] := by
  have h0 : V [5, 4, 2, 1] = V [7, 5, 0, 8, 6, 2] :=
    overlap torus7 torus2062 [7] [5, 4, 2, 1] (by decide)
  have hl : V [5, 4, 2, 1] = V [5, 4, 2, 1] :=
    rfl
  have hr : V [7, 5, 0, 8, 6, 2] = V [7, 5, 0, 8, 6, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2064 : V [7, 5, 0, 8, 6, 8] = V [4, 1, 4, 2] := by
  have h0 : V [5, 4, 2, 1, 3, 5, 3, 0, 6, 4, 6, 7] = V [7, 5, 0, 8, 6, 8] :=
    overlap torus2063 torus1852 [7, 5, 0, 8, 6] [3, 5, 3, 0, 6, 4, 6, 7] (by decide)
  have hl : V [5, 4, 2, 1, 3, 5, 3, 0, 6, 4, 6, 7] = V [4, 1, 4, 2] :=
    ((in_context torus1892 [] [5, 3, 0, 6, 4, 6, 7]).trans ((in_context torus2006 [4, 1, 4, 0, 2] []).trans ((in_context torus2 [4, 1, 4, 0] [1, 2]).trans (in_context torus0 [4, 1, 4] [2]))))
  have hr : V [7, 5, 0, 8, 6, 8] = V [7, 5, 0, 8, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2065 : V [7, 4, 1, 4, 2] = V [5, 0, 8, 6, 8] := by
  have h0 : V [7, 5, 4, 2, 2, 3, 2] = V [5, 0, 8, 6, 2, 2, 8] :=
    overlap torus1886 torus1433 [5, 0, 8, 6, 2] [2, 3, 2] (by decide)
  have hl : V [7, 5, 4, 2, 2, 3, 2] = V [7, 4, 1, 4, 2] :=
    ((in_context torus2 [7, 5, 4] [3, 2]).trans (in_context torus1453 [7] [2]))
  have hr : V [5, 0, 8, 6, 2, 2, 8] = V [5, 0, 8, 6, 8] :=
    (in_context torus2 [5, 0, 8, 6] [8])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2068 : V [5, 7, 8, 3, 8] = V [1, 5, 2, 4, 1] := by
  have h0 : V [5, 6, 5, 4, 2, 4, 1] = V [3, 5, 1, 2, 4, 2, 8, 0, 7, 3, 8] :=
    overlap torus1957 torus1802 [3, 5, 1, 2, 4, 2, 8] [5, 4, 2, 4, 1] (by decide)
  have hl : V [5, 6, 5, 4, 2, 4, 1] = V [1, 5, 2, 4, 1] :=
    ((in_context torus1460 [] [4, 2, 4, 1]).trans ((in_context torus1464 [] [4, 2, 4, 1]).trans (in_context torus4 [1, 5] [2, 4, 1])))
  have hr : V [3, 5, 1, 2, 4, 2, 8, 0, 7, 3, 8] = V [5, 7, 8, 3, 8] :=
    ((in_context torus1506 [3, 5, 1, 2, 4, 2] [3, 8]).trans ((in_context torus1647 [3] [8, 3, 8]).trans (in_context torus3 [] [5, 7, 8, 3, 8])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2074 : V [4, 1, 8, 3, 8] = V [2, 4, 5, 6, 7] := by
  have h0 : V [2, 4, 6, 0, 6] = V [4, 1, 8, 3, 8] :=
    overlap torus1997 torus6 [4, 1, 8, 3, 8] [6] (by decide)
  have hl : V [2, 4, 6, 0, 6] = V [2, 4, 5, 6, 7] :=
    (in_context torus1467 [2, 4] [])
  have hr : V [4, 1, 8, 3, 8] = V [4, 1, 8, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2075 : V [7, 1, 4, 6, 3] = V [5, 7, 8, 3, 0] := by
  have h0 : V [5, 7, 8, 3, 0] = V [7, 1, 4, 6, 3] :=
    overlap torus2025 torus1 [7, 1, 4, 6, 3] [0] (by decide)
  have hl : V [5, 7, 8, 3, 0] = V [5, 7, 8, 3, 0] :=
    rfl
  have hr : V [7, 1, 4, 6, 3] = V [7, 1, 4, 6, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2077 : V [7, 5, 7, 8, 2] = V [1, 4, 6, 4, 3] := by
  have h0 : V [1, 4, 6, 4, 3] = V [7, 5, 7, 8, 2] :=
    overlap torus2026 torus1438 [7, 5, 7] [3] (by decide)
  have hl : V [1, 4, 6, 4, 3] = V [1, 4, 6, 4, 3] :=
    rfl
  have hr : V [7, 5, 7, 8, 2] = V [7, 5, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2080 : V [7, 5, 0, 8, 6] = V [4, 1, 4, 2, 8] := by
  have h0 : V [5, 4, 2, 1, 2] = V [7, 5, 0, 8, 6] :=
    overlap torus2063 torus2 [7, 5, 0, 8, 6] [2] (by decide)
  have hl : V [5, 4, 2, 1, 2] = V [4, 1, 4, 2, 8] :=
    ((in_context torus1553 [5] []).trans (in_context torus1563 [] [8]))
  have hr : V [7, 5, 0, 8, 6] = V [7, 5, 0, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2081 : V [2, 1, 6, 8, 6, 5] = V [7, 2, 3, 4] := by
  have h0 : V [2, 1, 2, 2, 6, 8, 6, 5] = V [3, 2, 2, 3, 7, 2, 3, 4] :=
    overlap torus1434 torus262 [3, 2] [2, 6, 8, 6, 5] (by decide)
  have hl : V [2, 1, 2, 2, 6, 8, 6, 5] = V [2, 1, 6, 8, 6, 5] :=
    (in_context torus2 [2, 1] [6, 8, 6, 5])
  have hr : V [3, 2, 2, 3, 7, 2, 3, 4] = V [7, 2, 3, 4] :=
    ((in_context torus2 [3] [3, 7, 2, 3, 4]).trans (in_context torus3 [] [7, 2, 3, 4]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2082 : V [0, 3, 5, 6, 8, 6] = V [3, 7, 2, 1] := by
  have h0 : V [0, 3, 4, 4, 5, 6, 8, 6] = V [3, 2, 2, 7, 3, 2, 8, 2] :=
    overlap torus1439 torus255 [3, 2] [4, 5, 6, 8, 6] (by decide)
  have hl : V [0, 3, 4, 4, 5, 6, 8, 6] = V [0, 3, 5, 6, 8, 6] :=
    (in_context torus4 [0, 3] [5, 6, 8, 6])
  have hr : V [3, 2, 2, 7, 3, 2, 8, 2] = V [3, 7, 2, 1] :=
    ((in_context torus2 [3] [7, 3, 2, 8, 2]).trans ((in_context torus1434 [3, 7] [2]).trans (in_context torus2 [3, 7, 2, 1] [])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2083 : V [3, 5, 6, 8, 6] = V [1, 3, 7, 2, 1] := by
  have h0 : V [3, 5, 6, 8, 6] = V [1, 3, 7, 2, 1] :=
    overlap torus1 torus2082 [1] [3, 5, 6, 8, 6] (by decide)
  have hl : V [3, 5, 6, 8, 6] = V [3, 5, 6, 8, 6] :=
    rfl
  have hr : V [1, 3, 7, 2, 1] = V [1, 3, 7, 2, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2084 : V [0, 3, 8, 3, 4, 5] = V [7, 2, 7, 6] := by
  have h0 : V [0, 3, 4, 4, 8, 3, 4, 5] = V [3, 2, 2, 3, 7, 2, 7, 6] :=
    overlap torus1439 torus282 [3, 2] [4, 8, 3, 4, 5] (by decide)
  have hl : V [0, 3, 4, 4, 8, 3, 4, 5] = V [0, 3, 8, 3, 4, 5] :=
    (in_context torus4 [0, 3] [8, 3, 4, 5])
  have hr : V [3, 2, 2, 3, 7, 2, 7, 6] = V [7, 2, 7, 6] :=
    ((in_context torus2 [3] [3, 7, 2, 7, 6]).trans (in_context torus3 [] [7, 2, 7, 6]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2085 : V [3, 8, 3, 4, 5] = V [1, 7, 2, 7, 6] := by
  have h0 : V [3, 8, 3, 4, 5] = V [1, 7, 2, 7, 6] :=
    overlap torus1 torus2084 [1] [3, 8, 3, 4, 5] (by decide)
  have hl : V [3, 8, 3, 4, 5] = V [3, 8, 3, 4, 5] :=
    rfl
  have hr : V [1, 7, 2, 7, 6] = V [1, 7, 2, 7, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2087 : V [3, 1, 7, 2, 7, 6] = V [8, 3, 4, 5] := by
  have h0 : V [3, 1, 3, 3, 7, 2, 7, 6] = V [4, 4, 8, 3, 4, 5] :=
    overlap torus1444 torus281 [4] [3, 7, 2, 7, 6] (by decide)
  have hl : V [3, 1, 3, 3, 7, 2, 7, 6] = V [3, 1, 7, 2, 7, 6] :=
    (in_context torus3 [3, 1] [7, 2, 7, 6])
  have hr : V [4, 4, 8, 3, 4, 5] = V [8, 3, 4, 5] :=
    (in_context torus4 [] [8, 3, 4, 5])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2088 : V [0, 4, 6, 7, 2, 7] = V [4, 8, 3, 1] := by
  have h0 : V [0, 4, 5, 5, 6, 7, 2, 7] = V [4, 3, 3, 8, 4, 3, 2, 3] :=
    overlap torus1448 torus275 [4, 3] [5, 6, 7, 2, 7] (by decide)
  have hl : V [0, 4, 5, 5, 6, 7, 2, 7] = V [0, 4, 6, 7, 2, 7] :=
    (in_context torus5 [0, 4] [6, 7, 2, 7])
  have hr : V [4, 3, 3, 8, 4, 3, 2, 3] = V [4, 8, 3, 1] :=
    ((in_context torus3 [4] [8, 4, 3, 2, 3]).trans ((in_context torus1444 [4, 8] [3]).trans (in_context torus3 [4, 8, 3, 1] [])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2089 : V [4, 6, 7, 2, 7] = V [1, 4, 8, 3, 1] := by
  have h0 : V [4, 6, 7, 2, 7] = V [1, 4, 8, 3, 1] :=
    overlap torus1 torus2088 [1] [4, 6, 7, 2, 7] (by decide)
  have hl : V [4, 6, 7, 2, 7] = V [4, 6, 7, 2, 7] :=
    rfl
  have hr : V [1, 4, 8, 3, 1] = V [1, 4, 8, 3, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2093 : V [2, 1, 2, 7, 6, 4] = V [5, 3, 0, 6] := by
  have h0 : V [3, 2, 8, 7, 6, 4] = V [5, 3, 0, 6, 7, 7] :=
    inclusion torus187 torus1466 [5, 3] [7] (by decide)
  have hl : V [3, 2, 8, 7, 6, 4] = V [2, 1, 2, 7, 6, 4] :=
    (in_context torus1434 [] [7, 6, 4])
  have hr : V [5, 3, 0, 6, 7, 7] = V [5, 3, 0, 6] :=
    (in_context torus7 [5, 3, 0, 6] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2094 : V [2, 5, 3, 0, 6] = V [1, 2, 7, 6, 4] := by
  have h0 : V [1, 2, 7, 6, 4] = V [2, 5, 3, 0, 6] :=
    overlap torus2 torus2093 [2] [1, 2, 7, 6, 4] (by decide)
  have hl : V [1, 2, 7, 6, 4] = V [1, 2, 7, 6, 4] :=
    rfl
  have hr : V [2, 5, 3, 0, 6] = V [2, 5, 3, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2095 : V [3, 5, 3, 0, 6] = V [2, 7, 1, 7, 4] := by
  have h0 : V [0, 2, 3, 2, 7, 6, 4] = V [3, 5, 3, 0, 6] :=
    overlap torus1432 torus2093 [3] [2, 7, 6, 4] (by decide)
  have hl : V [0, 2, 3, 2, 7, 6, 4] = V [2, 7, 1, 7, 4] :=
    ((in_context torus1433 [] [7, 6, 4]).trans (in_context torus1480 [2] [4]))
  have hr : V [3, 5, 3, 0, 6] = V [3, 5, 3, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2097 : V [6, 1, 6, 3, 5, 1] = V [8, 2, 4, 2] := by
  have h0 : V [6, 1, 6, 3, 6, 5, 4, 5] = V [7, 7, 8, 2, 4, 2] :=
    overlap torus1471 torus173 [7] [3, 6, 5, 4, 5] (by decide)
  have hl : V [6, 1, 6, 3, 6, 5, 4, 5] = V [6, 1, 6, 3, 5, 1] :=
    ((in_context torus1462 [6, 1, 6, 3] [5]).trans (in_context torus5 [6, 1, 6, 3, 5, 1] []))
  have hr : V [7, 7, 8, 2, 4, 2] = V [8, 2, 4, 2] :=
    (in_context torus7 [] [8, 2, 4, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2099 : V [2, 0, 2, 5, 3, 0] = V [7, 6, 4, 6] := by
  have h0 : V [8, 2, 3, 5, 3, 0] = V [7, 6, 4, 7, 6, 1, 6, 5] :=
    overlap torus193 torus1473 [7, 6, 4, 7, 6] [0] (by decide)
  have hl : V [8, 2, 3, 5, 3, 0] = V [2, 0, 2, 5, 3, 0] :=
    (in_context torus1429 [] [5, 3, 0])
  have hr : V [7, 6, 4, 7, 6, 1, 6, 5] = V [7, 6, 4, 6] :=
    ((in_context torus1470 [7, 6, 4] [6, 5]).trans ((in_context torus1469 [7, 6, 4, 0] [5]).trans ((in_context torus1465 [7, 6, 4] [5]).trans (in_context torus5 [7, 6, 4, 6] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2100 : V [2, 7, 6, 4, 6] = V [0, 2, 5, 3, 0] := by
  have h0 : V [0, 2, 5, 3, 0] = V [2, 7, 6, 4, 6] :=
    overlap torus2 torus2099 [2] [0, 2, 5, 3, 0] (by decide)
  have hl : V [0, 2, 5, 3, 0] = V [0, 2, 5, 3, 0] :=
    rfl
  have hr : V [2, 7, 6, 4, 6] = V [2, 7, 6, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2101 : V [3, 1, 3, 8, 7, 5] = V [6, 4, 0, 7] := by
  have h0 : V [4, 3, 2, 8, 7, 5] = V [6, 4, 0, 7, 8, 8] :=
    inclusion torus207 torus1475 [6, 4] [8] (by decide)
  have hl : V [4, 3, 2, 8, 7, 5] = V [3, 1, 3, 8, 7, 5] :=
    (in_context torus1444 [] [8, 7, 5])
  have hr : V [6, 4, 0, 7, 8, 8] = V [6, 4, 0, 7] :=
    (in_context torus8 [6, 4, 0, 7] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2102 : V [6, 4, 0, 7, 5] = V [3, 1, 3, 8, 7] := by
  have h0 : V [6, 4, 0, 7, 5] = V [3, 1, 3, 8, 7] :=
    overlap torus2101 torus5 [3, 1, 3, 8, 7] [5] (by decide)
  have hl : V [6, 4, 0, 7, 5] = V [6, 4, 0, 7, 5] :=
    rfl
  have hr : V [3, 1, 3, 8, 7] = V [3, 1, 3, 8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2103 : V [6, 3, 1, 3, 8, 7] = V [4, 0, 7, 5] := by
  have h0 : V [4, 0, 7, 5] = V [6, 3, 1, 3, 8, 7] :=
    overlap torus6 torus2102 [6] [4, 0, 7, 5] (by decide)
  have hl : V [4, 0, 7, 5] = V [4, 0, 7, 5] :=
    rfl
  have hr : V [6, 3, 1, 3, 8, 7] = V [6, 3, 1, 3, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2105 : V [4, 6, 4, 0, 7] = V [2, 1, 2, 7, 5] := by
  have h0 : V [0, 3, 4, 3, 8, 7, 5] = V [4, 6, 4, 0, 7] :=
    overlap torus1443 torus2101 [4] [3, 8, 7, 5] (by decide)
  have hl : V [0, 3, 4, 3, 8, 7, 5] = V [2, 1, 2, 7, 5] :=
    ((in_context torus1442 [0] [8, 7, 5]).trans ((in_context torus1437 [] [8, 7, 5]).trans (in_context torus1434 [] [7, 5])))
  have hr : V [4, 6, 4, 0, 7] = V [4, 6, 4, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2106 : V [6, 3, 1, 3, 8] = V [4, 0, 7, 5, 7] := by
  have h0 : V [4, 0, 7, 5, 7] = V [6, 3, 1, 3, 8] :=
    overlap torus2103 torus7 [6, 3, 1, 3, 8] [7] (by decide)
  have hl : V [4, 0, 7, 5, 7] = V [4, 0, 7, 5, 7] :=
    rfl
  have hr : V [6, 3, 1, 3, 8] = V [6, 3, 1, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2107 : V [6, 4, 3, 8, 1] = V [4, 0, 7, 5, 8] := by
  have h0 : V [4, 0, 7, 5, 8] = V [6, 3, 1, 3, 0, 8, 2] :=
    overlap torus2103 torus1484 [6, 3, 1, 3] [8] (by decide)
  have hl : V [4, 0, 7, 5, 8] = V [4, 0, 7, 5, 8] :=
    rfl
  have hr : V [6, 3, 1, 3, 0, 8, 2] = V [6, 4, 3, 8, 1] :=
    ((in_context torus1543 [6, 3, 1] []).trans (in_context torus1520 [6] [1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2108 : V [2, 1, 2, 7, 5, 7] = V [4, 6, 4, 0] := by
  have h0 : V [3, 2, 8, 7, 5, 8, 8, 7] = V [4, 6, 4, 7, 7, 0] :=
    overlap torus209 torus1477 [4, 6, 4, 7] [8, 7] (by decide)
  have hl : V [3, 2, 8, 7, 5, 8, 8, 7] = V [2, 1, 2, 7, 5, 7] :=
    ((in_context torus1434 [] [7, 5, 8, 8, 7]).trans (in_context torus8 [2, 1, 2, 7, 5] [7]))
  have hr : V [4, 6, 4, 7, 7, 0] = V [4, 6, 4, 0] :=
    (in_context torus7 [4, 6, 4] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2111 : V [4, 1, 4, 2, 8, 6] = V [7, 5, 0, 8] := by
  have h0 : V [5, 4, 3, 2, 8, 6] = V [7, 5, 0, 8, 2, 2] :=
    inclusion torus227 torus1484 [7, 5] [2] (by decide)
  have hl : V [5, 4, 3, 2, 8, 6] = V [4, 1, 4, 2, 8, 6] :=
    (in_context torus1453 [] [2, 8, 6])
  have hr : V [7, 5, 0, 8, 2, 2] = V [7, 5, 0, 8] :=
    (in_context torus2 [7, 5, 0, 8] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2114 : V [3, 1, 3, 8, 6, 8] = V [5, 7, 5, 0] := by
  have h0 : V [4, 3, 2, 8, 6, 2, 2, 8] = V [5, 7, 5, 8, 8, 0] :=
    overlap torus229 torus1486 [5, 7, 5, 8] [2, 8] (by decide)
  have hl : V [4, 3, 2, 8, 6, 2, 2, 8] = V [3, 1, 3, 8, 6, 8] :=
    ((in_context torus1444 [] [8, 6, 2, 2, 8]).trans (in_context torus2 [3, 1, 3, 8, 6] [8]))
  have hr : V [5, 7, 5, 8, 8, 0] = V [5, 7, 5, 0] :=
    (in_context torus8 [5, 7, 5] [0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2115 : V [0, 3, 5, 7, 5, 0] = V [3, 8, 6, 8] := by
  have h0 : V [2, 8, 2, 3, 2, 1, 3, 8, 6, 8] = V [3, 2, 3, 4, 5, 7, 5, 0] :=
    overlap torus143 torus2114 [3, 2, 3, 4] [1, 3, 8, 6, 8] (by decide)
  have hl : V [2, 8, 2, 3, 2, 1, 3, 8, 6, 8] = V [3, 8, 6, 8] :=
    ((in_context torus1428 [] [3, 2, 1, 3, 8, 6, 8]).trans ((in_context torus3 [0, 2] [2, 1, 3, 8, 6, 8]).trans ((in_context torus2 [0] [1, 3, 8, 6, 8]).trans (in_context torus0 [] [3, 8, 6, 8]))))
  have hr : V [3, 2, 3, 4, 5, 7, 5, 0] = V [0, 3, 5, 7, 5, 0] :=
    ((in_context torus1439 [] [4, 5, 7, 5, 0]).trans (in_context torus4 [0, 3] [5, 7, 5, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2117 : V [3, 8, 6, 8, 1] = V [0, 3, 5, 7, 5] := by
  have h0 : V [3, 8, 6, 8, 1] = V [0, 3, 5, 7, 5] :=
    overlap torus2115 torus0 [0, 3, 5, 7, 5] [1] (by decide)
  have hl : V [3, 8, 6, 8, 1] = V [3, 8, 6, 8, 1] :=
    rfl
  have hr : V [0, 3, 5, 7, 5] = V [0, 3, 5, 7, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2118 : V [2, 3, 4, 5, 7, 5] = V [8, 6, 8, 1] := by
  have h0 : V [8, 6, 8, 1] = V [3, 0, 3, 5, 7, 5] :=
    overlap torus3 torus2117 [3] [8, 6, 8, 1] (by decide)
  have hl : V [8, 6, 8, 1] = V [8, 6, 8, 1] :=
    rfl
  have hr : V [3, 0, 3, 5, 7, 5] = V [2, 3, 4, 5, 7, 5] :=
    (in_context torus1440 [] [5, 7, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2119 : V [8, 6, 8, 1, 5] = V [2, 3, 4, 5, 7] := by
  have h0 : V [8, 6, 8, 1, 5] = V [2, 3, 4, 5, 7] :=
    overlap torus2118 torus5 [2, 3, 4, 5, 7] [5] (by decide)
  have hl : V [8, 6, 8, 1, 5] = V [8, 6, 8, 1, 5] :=
    rfl
  have hr : V [2, 3, 4, 5, 7] = V [2, 3, 4, 5, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2125 : V [0, 8, 2, 7, 5, 6] = V [8, 1, 6, 1] := by
  have h0 : V [0, 8, 2, 7, 5, 6] = V [8, 1, 7, 0, 6, 7] :=
    overlap torus1585 torus1466 [8, 1, 7] [5, 6] (by decide)
  have hl : V [0, 8, 2, 7, 5, 6] = V [0, 8, 2, 7, 5, 6] :=
    rfl
  have hr : V [8, 1, 7, 0, 6, 7] = V [8, 1, 6, 1] :=
    (in_context torus1498 [8, 1] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus2126 : V [8, 2, 7, 5, 6] = V [1, 8, 1, 6, 1] := by
  have h0 : V [8, 2, 7, 5, 6] = V [1, 8, 1, 6, 1] :=
    overlap torus1 torus2125 [1] [8, 2, 7, 5, 6] (by decide)
  have hl : V [8, 2, 7, 5, 6] = V [8, 2, 7, 5, 6] :=
    rfl
  have hr : V [1, 8, 1, 6, 1] = V [1, 8, 1, 6, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2127 : V [1, 4, 6, 4, 2, 1] = V [7, 5, 7, 2] := by
  have h0 : V [1, 4, 6, 4, 2, 1] = V [7, 5, 7, 2] :=
    overlap torus7 torus1651 [7] [1, 4, 6, 4, 2, 1] (by decide)
  have hl : V [1, 4, 6, 4, 2, 1] = V [1, 4, 6, 4, 2, 1] :=
    rfl
  have hr : V [7, 5, 7, 2] = V [7, 5, 7, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2128 : V [4, 6, 4, 2, 1] = V [0, 7, 5, 7, 2] := by
  have h0 : V [4, 6, 4, 2, 1] = V [0, 7, 5, 7, 2] :=
    overlap torus0 torus2127 [0] [4, 6, 4, 2, 1] (by decide)
  have hl : V [4, 6, 4, 2, 1] = V [4, 6, 4, 2, 1] :=
    rfl
  have hr : V [0, 7, 5, 7, 2] = V [0, 7, 5, 7, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2129 : V [4, 6, 3, 1, 3] = V [0, 7, 5, 7, 8] := by
  have h0 : V [0, 7, 5, 7, 2, 2, 8] = V [4, 6, 4, 3, 2] :=
    overlap torus2128 torus1435 [4, 6, 4] [2, 8] (by decide)
  have hl : V [0, 7, 5, 7, 2, 2, 8] = V [0, 7, 5, 7, 8] :=
    (in_context torus2 [0, 7, 5, 7] [8])
  have hr : V [4, 6, 4, 3, 2] = V [4, 6, 3, 1, 3] :=
    (in_context torus1444 [4, 6] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2132 : V [3, 0, 6, 4, 6, 7] = V [5, 2, 1, 2] := by
  have h0 : V [3, 0, 6, 4, 6, 7] = V [5, 3, 2, 7, 1, 0, 7, 8] :=
    overlap torus1687 torus1475 [5, 3, 2, 7, 1] [6, 7] (by decide)
  have hl : V [3, 0, 6, 4, 6, 7] = V [3, 0, 6, 4, 6, 7] :=
    rfl
  have hr : V [5, 3, 2, 7, 1, 0, 7, 8] = V [5, 2, 1, 2] :=
    ((in_context torus1 [5, 3, 2, 7] [7, 8]).trans ((in_context torus7 [5, 3, 2] [8]).trans (in_context torus1434 [5] [])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus2133 : V [6, 0, 2, 7, 2, 3] = V [8, 5, 1, 5] := by
  have h0 : V [6, 0, 2, 7, 2, 3] = V [8, 5, 1, 5] :=
    overlap torus1758 torus3 [8, 5, 1, 5] [3] (by decide)
  have hl : V [6, 0, 2, 7, 2, 3] = V [6, 0, 2, 7, 2, 3] :=
    rfl
  have hr : V [8, 5, 1, 5] = V [8, 5, 1, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2138 : V [4, 2, 4, 1, 8, 3] = V [5, 6, 7, 8] := by
  have h0 : V [4, 2, 4, 1, 8, 3] = V [5, 6, 7, 8] :=
    overlap torus1803 torus3 [5, 6, 7, 8] [3] (by decide)
  have hl : V [4, 2, 4, 1, 8, 3] = V [4, 2, 4, 1, 8, 3] :=
    rfl
  have hr : V [5, 6, 7, 8] = V [5, 6, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2140 : V [5, 3, 5, 1, 2, 4] = V [6, 7, 8, 2] := by
  have h0 : V [5, 3, 5, 1, 2, 4] = V [6, 7, 8, 2] :=
    overlap torus1820 torus4 [6, 7, 8, 2] [4] (by decide)
  have hl : V [5, 3, 5, 1, 2, 4] = V [5, 3, 5, 1, 2, 4] :=
    rfl
  have hr : V [6, 7, 8, 2] = V [6, 7, 8, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2141 : V [6, 4, 6, 1, 3, 5] = V [7, 2, 0, 2] := by
  have h0 : V [6, 4, 6, 1, 3, 5] = V [7, 2, 0, 2] :=
    overlap torus1837 torus5 [7, 2, 0, 2] [5] (by decide)
  have hl : V [6, 4, 6, 1, 3, 5] = V [6, 4, 6, 1, 3, 5] :=
    rfl
  have hr : V [7, 2, 0, 2] = V [7, 2, 0, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2142 : V [2, 1, 2, 6, 8, 1] = V [4, 5, 7, 5] := by
  have h0 : V [2, 1, 2, 6, 8, 1] = V [4, 5, 7, 5] :=
    overlap torus1874 torus0 [4, 5, 7, 5] [1] (by decide)
  have hl : V [2, 1, 2, 6, 8, 1] = V [2, 1, 2, 6, 8, 1] :=
    rfl
  have hr : V [4, 5, 7, 5] = V [4, 5, 7, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2143 : V [6, 2, 0, 2, 4, 5, 7, 5] = V [8, 1] := by
  have h0 : V [6, 2, 0, 1, 2, 6, 8, 1] = V [8, 1, 5, 7, 5, 4, 4, 5, 7, 5] :=
    overlap torus1653 torus2142 [8, 1, 5, 7, 5, 4] [1, 2, 6, 8, 1] (by decide)
  have hl : V [6, 2, 0, 1, 2, 6, 8, 1] = V [8, 1] :=
    ((in_context torus0 [6, 2] [2, 6, 8, 1]).trans ((in_context torus2 [6] [6, 8, 1]).trans (in_context torus6 [] [8, 1])))
  have hr : V [8, 1, 5, 7, 5, 4, 4, 5, 7, 5] = V [6, 2, 0, 2, 4, 5, 7, 5] :=
    (in_context torus1743 [] [4, 5, 7, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2144 : V [6, 2, 0, 2, 4, 5, 7] = V [8, 1, 5] := by
  have h0 : V [8, 1, 5] = V [6, 2, 0, 2, 4, 5, 7] :=
    overlap torus2143 torus5 [6, 2, 0, 2, 4, 5, 7] [5] (by decide)
  have hl : V [8, 1, 5] = V [8, 1, 5] :=
    rfl
  have hr : V [6, 2, 0, 2, 4, 5, 7] = V [6, 2, 0, 2, 4, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2146 : V [2, 0, 5, 3, 5, 6] = V [4, 2, 8, 7] := by
  have h0 : V [2, 0, 5, 3, 5, 6] = V [4, 2, 8, 7] :=
    overlap torus4 torus1956 [4] [2, 0, 5, 3, 5, 6] (by decide)
  have hl : V [2, 0, 5, 3, 5, 6] = V [2, 0, 5, 3, 5, 6] :=
    rfl
  have hr : V [4, 2, 8, 7] = V [4, 2, 8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2148 : V [6, 2, 0, 2, 4, 5] = V [8, 1, 5, 7] := by
  have h0 : V [6, 2, 0, 2, 4, 5] = V [8, 1, 5, 7] :=
    overlap torus1972 torus5 [8, 1, 5, 7] [5] (by decide)
  have hl : V [6, 2, 0, 2, 4, 5] = V [6, 2, 0, 2, 4, 5] :=
    rfl
  have hr : V [8, 1, 5, 7] = V [8, 1, 5, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2149 : V [6, 8, 1, 5, 7] = V [2, 0, 2, 4, 5] := by
  have h0 : V [2, 0, 2, 4, 5] = V [6, 8, 1, 5, 7] :=
    overlap torus6 torus2148 [6] [2, 0, 2, 4, 5] (by decide)
  have hl : V [2, 0, 2, 4, 5] = V [2, 0, 2, 4, 5] :=
    rfl
  have hr : V [6, 8, 1, 5, 7] = V [6, 8, 1, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2151 : V [4, 0, 7, 5, 7, 8] = V [6, 3, 1, 3] := by
  have h0 : V [4, 0, 7, 5, 7, 8] = V [6, 3, 1, 3] :=
    overlap torus2106 torus8 [6, 3, 1, 3] [8] (by decide)
  have hl : V [4, 0, 7, 5, 7, 8] = V [4, 0, 7, 5, 7, 8] :=
    rfl
  have hr : V [6, 3, 1, 3] = V [6, 3, 1, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2152 : V [4, 0, 7, 5, 7, 2] = V [6, 4, 2, 1] := by
  have h0 : V [4, 0, 7, 5, 7, 2] = V [6, 4, 2, 1] :=
    overlap torus2106 torus1519 [6] [2] (by decide)
  have hl : V [4, 0, 7, 5, 7, 2] = V [4, 0, 7, 5, 7, 2] :=
    rfl
  have hr : V [6, 4, 2, 1] = V [6, 4, 2, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus2155 : V [3, 0, 6, 4, 6, 5, 7, 1, 4, 6] = V [5, 4] := by
  have h0 : V [5, 2, 1, 2, 2, 0, 2, 4] = V [3, 0, 6, 4, 6, 5, 7, 1, 4, 6] :=
    overlap torus2132 torus1863 [3, 0, 6, 4, 6] [2, 0, 2, 4] (by decide)
  have hl : V [5, 2, 1, 2, 2, 0, 2, 4] = V [5, 4] :=
    ((in_context torus2 [5, 2, 1] [0, 2, 4]).trans ((in_context torus1 [5, 2] [2, 4]).trans (in_context torus2 [5] [4])))
  have hr : V [3, 0, 6, 4, 6, 5, 7, 1, 4, 6] = V [3, 0, 6, 4, 6, 5, 7, 1, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2156 : V [0, 3, 4, 1, 2, 8, 0, 3, 4] = V [1, 2, 8] := by
  have h0 : V [2, 3, 2, 3, 2, 3, 0, 3, 4] = V [3, 2, 3, 2, 3, 1, 2, 8, 3] :=
    overlap torus160 torus1544 [3, 2, 3, 2, 3] [0, 3, 4] (by decide)
  have hl : V [2, 3, 2, 3, 2, 3, 0, 3, 4] = V [1, 2, 8] :=
    ((in_context torus1436 [] [3, 2, 3, 0, 3, 4]).trans ((in_context torus1439 [1, 2, 8] [0, 3, 4]).trans ((in_context torus1447 [1, 2, 8] [3, 4]).trans ((in_context torus3 [1, 2, 8, 4] [4]).trans (in_context torus4 [1, 2, 8] [])))))
  have hr : V [3, 2, 3, 2, 3, 1, 2, 8, 3] = V [0, 3, 4, 1, 2, 8, 0, 3, 4] :=
    ((in_context torus1439 [] [2, 3, 1, 2, 8, 3]).trans ((in_context torus1541 [0, 3, 4, 2] [3]).trans ((in_context torus1544 [0, 3, 4] [2, 3]).trans (in_context torus1439 [0, 3, 4, 1, 2, 8] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2157 : V [0, 3, 4, 1, 2, 8, 3, 2, 4, 3] = V [2, 0] := by
  have h0 : V [1, 2, 8, 1, 3, 2] = V [0, 3, 4, 1, 2, 8, 0, 3, 0, 4, 5, 3] :=
    overlap torus2156 torus1554 [0, 3, 4, 1, 2, 8, 0, 3] [1, 3, 2] (by decide)
  have hl : V [1, 2, 8, 1, 3, 2] = V [2, 0] :=
    ((in_context torus1488 [1] [3, 2]).trans ((in_context torus1 [] [8, 2, 3, 2]).trans ((in_context torus1429 [] [2]).trans (in_context torus2 [2, 0] []))))
  have hr : V [0, 3, 4, 1, 2, 8, 0, 3, 0, 4, 5, 3] = V [0, 3, 4, 1, 2, 8, 3, 2, 4, 3] :=
    ((in_context torus1550 [0, 3, 4, 1, 2, 8, 0] [3]).trans (in_context torus0 [0, 3, 4, 1, 2, 8] [3, 2, 4, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2162 : V [0, 5, 6, 1, 4, 3, 0, 5, 6] = V [1, 4, 3] := by
  have h0 : V [4, 5, 4, 5, 4, 5, 0, 5, 6] = V [5, 4, 5, 4, 5, 1, 4, 3, 5] :=
    overlap torus162 torus1561 [5, 4, 5, 4, 5] [0, 5, 6] (by decide)
  have hl : V [4, 5, 4, 5, 4, 5, 0, 5, 6] = V [1, 4, 3] :=
    ((in_context torus1451 [] [5, 4, 5, 0, 5, 6]).trans ((in_context torus1455 [] [5, 4, 5, 0, 5, 6]).trans ((in_context torus1457 [1, 4, 3] [0, 5, 6]).trans ((in_context torus1465 [1, 4, 3] [5, 6]).trans ((in_context torus5 [1, 4, 3, 6] [6]).trans (in_context torus6 [1, 4, 3] []))))))
  have hr : V [5, 4, 5, 4, 5, 1, 4, 3, 5] = V [0, 5, 6, 1, 4, 3, 0, 5, 6] :=
    ((in_context torus1457 [] [4, 5, 1, 4, 3, 5]).trans ((in_context torus1546 [0, 5, 6, 4] [5]).trans ((in_context torus1561 [0, 5, 6] [4, 5]).trans (in_context torus1457 [0, 5, 6, 1, 4, 3] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2163 : V [0, 5, 6, 1, 4, 3, 5, 4, 6, 5] = V [4, 0] := by
  have h0 : V [1, 4, 3, 1, 5, 4] = V [0, 5, 6, 1, 4, 3, 0, 5, 0, 6, 7, 5] :=
    overlap torus2162 torus1569 [0, 5, 6, 1, 4, 3, 0, 5] [1, 5, 4] (by decide)
  have hl : V [1, 4, 3, 1, 5, 4] = V [4, 0] :=
    ((in_context torus1443 [1] [5, 4]).trans ((in_context torus1 [] [3, 4, 5, 4]).trans (in_context torus1450 [] [])))
  have hr : V [0, 5, 6, 1, 4, 3, 0, 5, 0, 6, 7, 5] = V [0, 5, 6, 1, 4, 3, 5, 4, 6, 5] :=
    ((in_context torus1566 [0, 5, 6, 1, 4, 3, 0] [5]).trans (in_context torus0 [0, 5, 6, 1, 4, 3] [5, 4, 6, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2165 : V [0, 6, 7, 1, 5, 4, 0, 6, 7] = V [1, 5, 4] := by
  have h0 : V [5, 6, 5, 6, 5, 6, 0, 6, 7] = V [6, 5, 6, 5, 6, 1, 5, 4, 6] :=
    overlap torus163 torus1566 [6, 5, 6, 5, 6] [0, 6, 7] (by decide)
  have hl : V [5, 6, 5, 6, 5, 6, 0, 6, 7] = V [1, 5, 4] :=
    ((in_context torus1460 [] [6, 5, 6, 0, 6, 7]).trans ((in_context torus1464 [] [6, 5, 6, 0, 6, 7]).trans ((in_context torus1466 [1, 5, 4] [0, 6, 7]).trans ((in_context torus1474 [1, 5, 4] [6, 7]).trans ((in_context torus6 [1, 5, 4, 7] [7]).trans (in_context torus7 [1, 5, 4] []))))))
  have hr : V [6, 5, 6, 5, 6, 1, 5, 4, 6] = V [0, 6, 7, 1, 5, 4, 0, 6, 7] :=
    ((in_context torus1466 [] [5, 6, 1, 5, 4, 6]).trans ((in_context torus1569 [0, 6, 7, 5] [6]).trans ((in_context torus1566 [0, 6, 7] [5, 6]).trans (in_context torus1466 [0, 6, 7, 1, 5, 4] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2166 : V [0, 6, 7, 1, 5, 4, 6, 5, 7, 6] = V [5, 0] := by
  have h0 : V [1, 5, 4, 1, 6, 5] = V [0, 6, 7, 1, 5, 4, 0, 6, 0, 7, 8, 6] :=
    overlap torus2165 torus1577 [0, 6, 7, 1, 5, 4, 0, 6] [1, 6, 5] (by decide)
  have hl : V [1, 5, 4, 1, 6, 5] = V [5, 0] :=
    ((in_context torus1452 [1] [6, 5]).trans ((in_context torus1 [] [4, 5, 6, 5]).trans (in_context torus1459 [] [])))
  have hr : V [0, 6, 7, 1, 5, 4, 0, 6, 0, 7, 8, 6] = V [0, 6, 7, 1, 5, 4, 6, 5, 7, 6] :=
    ((in_context torus1574 [0, 6, 7, 1, 5, 4, 0] [6]).trans (in_context torus0 [0, 6, 7, 1, 5, 4] [6, 5, 7, 6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2168 : V [0, 7, 8, 1, 6, 5, 0, 7, 8] = V [1, 6, 5] := by
  have h0 : V [6, 7, 6, 7, 6, 7, 0, 7, 8] = V [7, 6, 7, 6, 7, 1, 6, 5, 7] :=
    overlap torus164 torus1574 [7, 6, 7, 6, 7] [0, 7, 8] (by decide)
  have hl : V [6, 7, 6, 7, 6, 7, 0, 7, 8] = V [1, 6, 5] :=
    ((in_context torus1469 [] [7, 6, 7, 0, 7, 8]).trans ((in_context torus1473 [] [7, 6, 7, 0, 7, 8]).trans ((in_context torus1475 [1, 6, 5] [0, 7, 8]).trans ((in_context torus1483 [1, 6, 5] [7, 8]).trans ((in_context torus7 [1, 6, 5, 8] [8]).trans (in_context torus8 [1, 6, 5] []))))))
  have hr : V [7, 6, 7, 6, 7, 1, 6, 5, 7] = V [0, 7, 8, 1, 6, 5, 0, 7, 8] :=
    ((in_context torus1475 [] [6, 7, 1, 6, 5, 7]).trans ((in_context torus1577 [0, 7, 8, 6] [7]).trans ((in_context torus1574 [0, 7, 8] [6, 7]).trans (in_context torus1475 [0, 7, 8, 1, 6, 5] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2169 : V [0, 7, 8, 1, 6, 5, 7, 6, 8, 7] = V [6, 0] := by
  have h0 : V [1, 6, 5, 1, 7, 6] = V [0, 7, 8, 1, 6, 5, 0, 7, 0, 8, 2, 7] :=
    overlap torus2168 torus1585 [0, 7, 8, 1, 6, 5, 0, 7] [1, 7, 6] (by decide)
  have hl : V [1, 6, 5, 1, 7, 6] = V [6, 0] :=
    ((in_context torus1461 [1] [7, 6]).trans ((in_context torus1 [] [5, 6, 7, 6]).trans (in_context torus1468 [] [])))
  have hr : V [0, 7, 8, 1, 6, 5, 0, 7, 0, 8, 2, 7] = V [0, 7, 8, 1, 6, 5, 7, 6, 8, 7] :=
    ((in_context torus1582 [0, 7, 8, 1, 6, 5, 0] [7]).trans (in_context torus0 [0, 7, 8, 1, 6, 5] [7, 6, 8, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2171 : V [0, 8, 2, 1, 7, 6, 0, 8, 2] = V [1, 7, 6] := by
  have h0 : V [7, 8, 7, 8, 7, 8, 0, 8, 2] = V [8, 7, 8, 7, 8, 1, 7, 6, 8] :=
    overlap torus165 torus1582 [8, 7, 8, 7, 8] [0, 8, 2] (by decide)
  have hl : V [7, 8, 7, 8, 7, 8, 0, 8, 2] = V [1, 7, 6] :=
    ((in_context torus1478 [] [8, 7, 8, 0, 8, 2]).trans ((in_context torus1482 [] [8, 7, 8, 0, 8, 2]).trans ((in_context torus1484 [1, 7, 6] [0, 8, 2]).trans ((in_context torus1430 [1, 7, 6, 0] [8, 2]).trans ((in_context torus1433 [1, 7, 6] [8, 2]).trans ((in_context torus8 [1, 7, 6, 2] [2]).trans (in_context torus2 [1, 7, 6] [])))))))
  have hr : V [8, 7, 8, 7, 8, 1, 7, 6, 8] = V [0, 8, 2, 1, 7, 6, 0, 8, 2] :=
    ((in_context torus1484 [] [7, 8, 1, 7, 6, 8]).trans ((in_context torus1585 [0, 8, 2, 7] [8]).trans ((in_context torus1582 [0, 8, 2] [7, 8]).trans (in_context torus1484 [0, 8, 2, 1, 7, 6] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2172 : V [0, 8, 2, 1, 7, 6, 8, 7, 2, 8] = V [7, 0] := by
  have h0 : V [1, 7, 6, 1, 8, 7] = V [0, 8, 2, 1, 7, 6, 0, 8, 0, 2, 3, 8] :=
    overlap torus2171 torus1590 [0, 8, 2, 1, 7, 6, 0, 8] [1, 8, 7] (by decide)
  have hl : V [1, 7, 6, 1, 8, 7] = V [7, 0] :=
    ((in_context torus1470 [1] [8, 7]).trans ((in_context torus1 [] [6, 7, 8, 7]).trans (in_context torus1477 [] [])))
  have hr : V [0, 8, 2, 1, 7, 6, 0, 8, 0, 2, 3, 8] = V [0, 8, 2, 1, 7, 6, 8, 7, 2, 8] :=
    ((in_context torus1586 [0, 8, 2, 1, 7, 6, 0] [8]).trans (in_context torus0 [0, 8, 2, 1, 7, 6] [8, 7, 2, 8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2173 : V [0, 8, 2, 1, 7, 6, 8, 7, 0, 8] = V [7, 2] := by
  have h0 : V [1, 7, 6, 7, 8, 2] = V [0, 8, 2, 1, 7, 6, 0, 1, 8, 7, 0, 8] :=
    overlap torus2171 torus1876 [0, 8, 2, 1, 7, 6, 0] [7, 8, 2] (by decide)
  have hl : V [1, 7, 6, 7, 8, 2] = V [7, 2] :=
    ((in_context torus1475 [1] [8, 2]).trans ((in_context torus1 [] [7, 8, 8, 2]).trans (in_context torus8 [7] [2])))
  have hr : V [0, 8, 2, 1, 7, 6, 0, 1, 8, 7, 0, 8] = V [0, 8, 2, 1, 7, 6, 8, 7, 0, 8] :=
    (in_context torus0 [0, 8, 2, 1, 7, 6] [8, 7, 0, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2174 : V [1, 8, 7, 0, 2, 3, 1, 8, 7] = V [0, 2, 3] := by
  have h0 : V [2, 8, 2, 8, 2, 8, 1, 8, 7] = V [8, 2, 8, 2, 8, 0, 2, 3, 8] :=
    overlap torus166 torus1590 [8, 2, 8, 2, 8] [1, 8, 7] (by decide)
  have hl : V [2, 8, 2, 8, 2, 8, 1, 8, 7] = V [0, 2, 3] :=
    ((in_context torus1428 [] [8, 2, 8, 1, 8, 7]).trans ((in_context torus1487 [0, 2, 3] [1, 8, 7]).trans ((in_context torus1490 [0, 2, 3] [1, 8, 7]).trans ((in_context torus1479 [0, 2, 3, 1] [8, 7]).trans ((in_context torus1 [0, 2, 3] [7, 8, 8, 7]).trans ((in_context torus8 [0, 2, 3, 7] [7]).trans (in_context torus7 [0, 2, 3] [])))))))
  have hr : V [8, 2, 8, 2, 8, 0, 2, 3, 8] = V [1, 8, 7, 0, 2, 3, 1, 8, 7] :=
    ((in_context torus1487 [] [2, 8, 0, 2, 3, 8]).trans ((in_context torus1490 [] [2, 8, 0, 2, 3, 8]).trans ((in_context torus1586 [1, 8, 7, 2] [8]).trans ((in_context torus1590 [1, 8, 7] [2, 8]).trans ((in_context torus1487 [1, 8, 7, 0, 2, 3] []).trans (in_context torus1490 [1, 8, 7, 0, 2, 3] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2178 : V [7, 0, 3, 1, 6, 0, 2, 7, 8] = V [0, 2, 12] := by
  have h0 : V [2, 6, 1, 6, 5, 6, 7, 8, 2, 3, 12] = V [7, 0, 3, 8, 2, 8, 7, 6, 5, 4, 3, 2, 8] :=
    overlap torus1773 torus1402 [7, 0, 3, 8] [5, 6, 7, 8, 2, 3, 12] (by decide)
  have hl : V [2, 6, 1, 6, 5, 6, 7, 8, 2, 3, 12] = V [0, 2, 12] :=
    ((in_context torus1472 [2] [6, 7, 8, 2, 3, 12]).trans ((in_context torus6 [2, 7] [7, 8, 2, 3, 12]).trans ((in_context torus7 [2] [8, 2, 3, 12]).trans ((in_context torus1428 [] [3, 12]).trans (in_context torus3 [0, 2] [12])))))
  have hr : V [7, 0, 3, 8, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [7, 0, 3, 1, 6, 0, 2, 7, 8] :=
    ((in_context torus1487 [7, 0, 3] [7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus1490 [7, 0, 3] [7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus7 [7, 0, 3, 1, 8] [6, 5, 4, 3, 2, 8]).trans ((in_context torus266 [7, 0, 3, 1] [8]).trans ((in_context torus1428 [7, 0, 3, 1, 6] [3, 7, 8]).trans (in_context torus3 [7, 0, 3, 1, 6, 0, 2] [7, 8]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2180 : V [7, 0, 3, 1, 6, 0, 2, 1, 7, 5] = V [2, 12] := by
  have h0 : V [0, 2, 12, 6, 1, 6] = V [7, 0, 3, 1, 6, 0, 2, 7, 7, 1, 7, 5] :=
    overlap torus2178 torus1584 [7, 0, 3, 1, 6, 0, 2, 7] [6, 1, 6] (by decide)
  have hl : V [0, 2, 12, 6, 1, 6] = V [2, 12] :=
    ((in_context torus72 [0, 2] [1, 6]).trans ((in_context torus2 [0] [12, 1, 6]).trans ((in_context torus94 [0] [6]).trans ((in_context torus0 [] [12, 6]).trans (in_context torus72 [] [])))))
  have hr : V [7, 0, 3, 1, 6, 0, 2, 7, 7, 1, 7, 5] = V [7, 0, 3, 1, 6, 0, 2, 1, 7, 5] :=
    (in_context torus7 [7, 0, 3, 1, 6, 0, 2] [1, 7, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2183 : V [8, 0, 4, 2, 3, 8, 3, 1, 7] = V [3, 8, 2] := by
  have h0 : V [3, 7, 1, 7, 6, 7, 2] = V [8, 0, 4, 2, 3, 8, 3, 1, 7] :=
    overlap torus1790 torus1783 [8, 0, 4, 2] [6, 7, 2] (by decide)
  have hl : V [3, 7, 1, 7, 6, 7, 2] = V [3, 8, 2] :=
    ((in_context torus1481 [3] [7, 2]).trans (in_context torus7 [3, 8] [2]))
  have hr : V [8, 0, 4, 2, 3, 8, 3, 1, 7] = V [8, 0, 4, 2, 3, 8, 3, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2184 : V [0, 3, 8, 3, 2, 4, 1, 8, 3] = V [7, 2, 8] := by
  have h0 : V [7, 2, 7, 6, 5, 5, 6, 7, 8] = V [3, 2, 3, 4, 8, 3, 2, 4, 1, 8, 3] :=
    overlap torus287 torus1805 [3, 2, 3, 4, 8, 3] [5, 6, 7, 8] (by decide)
  have hl : V [7, 2, 7, 6, 5, 5, 6, 7, 8] = V [7, 2, 8] :=
    ((in_context torus1471 [7, 2] [5, 6, 7, 8]).trans ((in_context torus1772 [] [5, 6, 7, 8]).trans ((in_context torus1675 [] [7, 8]).trans (in_context torus7 [7, 2] [8]))))
  have hr : V [3, 2, 3, 4, 8, 3, 2, 4, 1, 8, 3] = V [0, 3, 8, 3, 2, 4, 1, 8, 3] :=
    ((in_context torus1439 [] [4, 8, 3, 2, 4, 1, 8, 3]).trans (in_context torus4 [0, 3] [8, 3, 2, 4, 1, 8, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2188 : V [5, 0, 8, 1, 4, 0, 7, 5, 6] = V [0, 7, 12] := by
  have h0 : V [7, 4, 1, 4, 3, 4, 5, 6, 7, 8, 12] = V [5, 0, 8, 6, 7, 6, 5, 4, 3, 2, 8, 7, 6] :=
    overlap torus1891 torus1405 [5, 0, 8, 6] [3, 4, 5, 6, 7, 8, 12] (by decide)
  have hl : V [7, 4, 1, 4, 3, 4, 5, 6, 7, 8, 12] = V [0, 7, 12] :=
    ((in_context torus1454 [7] [4, 5, 6, 7, 8, 12]).trans ((in_context torus4 [7, 5] [5, 6, 7, 8, 12]).trans ((in_context torus5 [7] [6, 7, 8, 12]).trans ((in_context torus1475 [] [8, 12]).trans (in_context torus8 [0, 7] [12])))))
  have hr : V [5, 0, 8, 6, 7, 6, 5, 4, 3, 2, 8, 7, 6] = V [5, 0, 8, 1, 4, 0, 7, 5, 6] :=
    ((in_context torus1469 [5, 0, 8] [5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1473 [5, 0, 8] [5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus5 [5, 0, 8, 1, 6] [4, 3, 2, 8, 7, 6]).trans ((in_context torus226 [5, 0, 8, 1] [6]).trans ((in_context torus1475 [5, 0, 8, 1, 4] [8, 5, 6]).trans (in_context torus8 [5, 0, 8, 1, 4, 0, 7] [5, 6]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2189 : V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 4] = V [12] := by
  have h0 : V [0, 7, 12, 4, 1] = V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 4] :=
    overlap torus2188 torus1595 [5, 0, 8, 1, 4, 0, 7] [4, 1] (by decide)
  have hl : V [0, 7, 12, 4, 1] = V [12] :=
    ((in_context torus60 [0, 7] [1]).trans ((in_context torus7 [0] [12, 1]).trans ((in_context torus94 [0] []).trans (in_context torus0 [] [12]))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 4] = V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2190 : V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3] = V [7, 12] := by
  have h0 : V [0, 7, 12, 4, 1, 4] = V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1, 5, 3] :=
    overlap torus2188 torus1568 [5, 0, 8, 1, 4, 0, 7, 5] [4, 1, 4] (by decide)
  have hl : V [0, 7, 12, 4, 1, 4] = V [7, 12] :=
    ((in_context torus60 [0, 7] [1, 4]).trans ((in_context torus7 [0] [12, 1, 4]).trans ((in_context torus94 [0] [4]).trans ((in_context torus0 [] [12, 4]).trans (in_context torus60 [] [])))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1, 5, 3] = V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3] :=
    (in_context torus5 [5, 0, 8, 1, 4, 0, 7] [1, 5, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2192 : V [0, 6, 4, 6, 5, 7, 1, 4, 6] = V [3, 5, 4] := by
  have h0 : V [3, 5, 2, 2, 4] = V [0, 6, 4, 6, 5, 7, 1, 4, 6] :=
    overlap torus1969 torus1863 [0, 6, 4, 6] [2, 4] (by decide)
  have hl : V [3, 5, 2, 2, 4] = V [3, 5, 4] :=
    (in_context torus2 [3, 5] [4])
  have hr : V [0, 6, 4, 6, 5, 7, 1, 4, 6] = V [0, 6, 4, 6, 5, 7, 1, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2193 : V [4, 6, 1, 3, 0, 5, 8, 6, 0] = V [7, 0, 2] := by
  have h0 : V [6, 7, 8, 2, 3, 3, 2, 7, 2] = V [4, 7, 6, 5, 6, 3, 0, 5, 8, 6, 0] :=
    overlap torus197 torus1975 [4, 7, 6, 5, 6, 3] [3, 2, 7, 2] (by decide)
  have hl : V [6, 7, 8, 2, 3, 3, 2, 7, 2] = V [7, 0, 2] :=
    ((in_context torus1429 [6, 7] [3, 2, 7, 2]).trans ((in_context torus1839 [] [3, 2, 7, 2]).trans ((in_context torus1649 [4] [2]).trans (in_context torus4 [] [7, 0, 2]))))
  have hr : V [4, 7, 6, 5, 6, 3, 0, 5, 8, 6, 0] = V [4, 6, 1, 3, 0, 5, 8, 6, 0] :=
    ((in_context torus1471 [4] [6, 3, 0, 5, 8, 6, 0]).trans (in_context torus6 [4, 6, 1] [3, 0, 5, 8, 6, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2194 : V [5, 7, 4, 1, 2, 0, 5, 3, 6] = V [0, 8, 1] := by
  have h0 : V [0, 8, 6, 6, 1] = V [5, 7, 4, 1, 2, 0, 5, 3, 6] :=
    overlap torus1885 torus2000 [5, 7, 4, 1] [6, 1] (by decide)
  have hl : V [0, 8, 6, 6, 1] = V [0, 8, 1] :=
    (in_context torus6 [0, 8] [1])
  have hr : V [5, 7, 4, 1, 2, 0, 5, 3, 6] = V [5, 7, 4, 1, 2, 0, 5, 3, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2195 : V [8, 0, 4, 1, 7, 0, 3, 8, 2] = V [0, 3, 12] := by
  have h0 : V [3, 7, 1, 7, 5, 5, 6, 7, 8, 2, 3, 4, 12] = V [8, 0, 4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 2] :=
    overlap torus2001 torus1413 [8, 0, 4, 2] [5, 6, 7, 8, 2, 3, 4, 12] (by decide)
  have hl : V [3, 7, 1, 7, 5, 5, 6, 7, 8, 2, 3, 4, 12] = V [0, 3, 12] :=
    ((in_context torus5 [3, 7, 1, 7] [6, 7, 8, 2, 3, 4, 12]).trans ((in_context torus1481 [3] [7, 8, 2, 3, 4, 12]).trans ((in_context torus7 [3, 8] [8, 2, 3, 4, 12]).trans ((in_context torus8 [3] [2, 3, 4, 12]).trans ((in_context torus1439 [] [4, 12]).trans (in_context torus4 [0, 3] [12]))))))
  have hr : V [8, 0, 4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [8, 0, 4, 1, 7, 0, 3, 8, 2] :=
    ((in_context torus1436 [8, 0, 4] [8, 7, 6, 5, 4, 3, 2]).trans ((in_context torus8 [8, 0, 4, 1, 2] [7, 6, 5, 4, 3, 2]).trans ((in_context torus1471 [8, 0, 4, 1, 2] [4, 3, 2]).trans ((in_context torus1982 [8, 0, 4, 1, 2] [2]).trans (in_context torus2 [8, 0, 4, 1] [7, 0, 3, 8, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2196 : V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [12] := by
  have h0 : V [0, 3, 12, 7, 1] = V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] :=
    overlap torus2195 torus1598 [8, 0, 4, 1, 7, 0, 3] [7, 1] (by decide)
  have hl : V [0, 3, 12, 7, 1] = V [12] :=
    ((in_context torus78 [0, 3] [1]).trans ((in_context torus3 [0] [12, 1]).trans ((in_context torus94 [0] []).trans (in_context torus0 [] [12]))))
  have hr : V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2197 : V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6] = V [3, 12] := by
  have h0 : V [12, 7] = V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6] :=
    overlap torus2196 torus7 [8, 0, 4, 1, 7, 0, 3, 1, 8, 6] [7] (by decide)
  have hl : V [12, 7] = V [3, 12] :=
    (in_context torus78 [] [])
  have hr : V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6] = V [8, 0, 4, 1, 7, 0, 3, 1, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2199 : V [7, 2, 1, 6, 0, 8, 4, 2, 0] = V [3, 0, 5] := by
  have h0 : V [2, 3, 4, 5, 5, 3, 5] = V [7, 2, 1, 6, 0, 8, 4, 2, 0] :=
    overlap torus1768 torus2042 [7, 2, 1, 6] [5, 3, 5] (by decide)
  have hl : V [2, 3, 4, 5, 5, 3, 5] = V [3, 0, 5] :=
    ((in_context torus5 [2, 3, 4] [3, 5]).trans (in_context torus1441 [] [5]))
  have hr : V [7, 2, 1, 6, 0, 8, 4, 2, 0] = V [7, 2, 1, 6, 0, 8, 4, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2200 : V [5, 7, 1, 4, 0, 6, 2, 7, 0] = V [8, 0, 3] := by
  have h0 : V [7, 8, 2, 3, 4, 4, 3, 8, 3] = V [5, 8, 7, 6, 7, 4, 0, 6, 2, 7, 0] :=
    overlap torus217 torus2044 [5, 8, 7, 6, 7, 4] [4, 3, 8, 3] (by decide)
  have hl : V [7, 8, 2, 3, 4, 4, 3, 8, 3] = V [8, 0, 3] :=
    ((in_context torus1429 [7] [4, 4, 3, 8, 3]).trans ((in_context torus1863 [] [4, 3, 8, 3]).trans ((in_context torus1661 [5] [3]).trans (in_context torus5 [] [8, 0, 3]))))
  have hr : V [5, 8, 7, 6, 7, 4, 0, 6, 2, 7, 0] = V [5, 7, 1, 4, 0, 6, 2, 7, 0] :=
    ((in_context torus1480 [5] [7, 4, 0, 6, 2, 7, 0]).trans (in_context torus7 [5, 7, 1] [4, 0, 6, 2, 7, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2201 : V [6, 8, 1, 5, 0, 7, 3, 8, 0] = V [2, 0, 4] := by
  have h0 : V [8, 2, 3, 4, 5, 5, 4, 2, 4] = V [6, 2, 8, 7, 8, 5, 0, 7, 3, 8, 0] :=
    overlap torus237 torus2046 [6, 2, 8, 7, 8, 5] [5, 4, 2, 4] (by decide)
  have hl : V [8, 2, 3, 4, 5, 5, 4, 2, 4] = V [2, 0, 4] :=
    ((in_context torus1429 [] [4, 5, 5, 4, 2, 4]).trans ((in_context torus5 [2, 0, 2, 4] [4, 2, 4]).trans ((in_context torus4 [2, 0, 2] [2, 4]).trans (in_context torus2 [2, 0] [4]))))
  have hr : V [6, 2, 8, 7, 8, 5, 0, 7, 3, 8, 0] = V [6, 8, 1, 5, 0, 7, 3, 8, 0] :=
    ((in_context torus1484 [6, 2] [5, 0, 7, 3, 8, 0]).trans (in_context torus1491 [6] [5, 0, 7, 3, 8, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2202 : V [4, 1, 8, 3, 2, 4, 2, 0, 5] = V [2, 4, 3] := by
  have h0 : V [2, 4, 5, 7, 7, 5, 3] = V [4, 1, 8, 3, 2, 4, 2, 0, 5] :=
    overlap torus2048 torus2037 [4, 1, 8, 3] [7, 5, 3] (by decide)
  have hl : V [2, 4, 5, 7, 7, 5, 3] = V [2, 4, 3] :=
    ((in_context torus7 [2, 4, 5] [5, 3]).trans (in_context torus5 [2, 4] [3]))
  have hr : V [4, 1, 8, 3, 2, 4, 2, 0, 5] = V [4, 1, 8, 3, 2, 4, 2, 0, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2203 : V [8, 6, 0, 2, 1, 7, 4, 6, 1] = V [5, 1, 3] := by
  have h0 : V [5, 1, 5, 3, 2, 2, 3, 5, 3] = V [8, 6, 0, 2, 1, 7, 4, 6, 1] :=
    overlap torus1981 torus2057 [8, 6, 0, 2] [2, 3, 5, 3] (by decide)
  have hl : V [5, 1, 5, 3, 2, 2, 3, 5, 3] = V [5, 1, 3] :=
    ((in_context torus2 [5, 1, 5, 3] [3, 5, 3]).trans ((in_context torus3 [5, 1, 5] [5, 3]).trans (in_context torus5 [5, 1] [3])))
  have hr : V [8, 6, 0, 2, 1, 7, 4, 6, 1] = V [8, 6, 0, 2, 1, 7, 4, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2204 : V [2, 4, 1, 8, 0, 3, 6, 4, 0] = V [5, 0, 7] := by
  have h0 : V [4, 5, 6, 7, 8, 8, 7, 5, 7] = V [2, 5, 4, 3, 4, 8, 0, 3, 6, 4, 0] :=
    overlap torus298 torus2059 [2, 5, 4, 3, 4, 8] [8, 7, 5, 7] (by decide)
  have hl : V [4, 5, 6, 7, 8, 8, 7, 5, 7] = V [5, 0, 7] :=
    ((in_context torus1805 [] [8, 7, 5, 7]).trans ((in_context torus1792 [2, 4] [7]).trans ((in_context torus4 [2] [2, 5, 0, 7]).trans (in_context torus2 [] [5, 0, 7]))))
  have hr : V [2, 5, 4, 3, 4, 8, 0, 3, 6, 4, 0] = V [2, 4, 1, 8, 0, 3, 6, 4, 0] :=
    ((in_context torus1453 [2] [4, 8, 0, 3, 6, 4, 0]).trans (in_context torus4 [2, 4, 1] [8, 0, 3, 6, 4, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2207 : V [7, 5, 0, 8, 1, 6, 3, 5, 1] = V [4, 1, 2] := by
  have h0 : V [4, 1, 4, 2, 2, 4, 2] = V [7, 5, 0, 8, 1, 6, 3, 5, 1] :=
    overlap torus2064 torus2041 [7, 5, 0, 8] [2, 4, 2] (by decide)
  have hl : V [4, 1, 4, 2, 2, 4, 2] = V [4, 1, 2] :=
    ((in_context torus2 [4, 1, 4] [4, 2]).trans (in_context torus4 [4, 1] [2]))
  have hr : V [7, 5, 0, 8, 1, 6, 3, 5, 1] = V [7, 5, 0, 8, 1, 6, 3, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2208 : V [4, 1, 8, 0, 5, 1, 2, 4, 12] = V [1, 2, 7] := by
  have h0 : V [2, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 8, 7] = V [4, 1, 8, 3, 2, 3, 4, 5, 6, 7, 8, 2, 12] :=
    overlap torus2074 torus1404 [4, 1, 8, 3] [7, 6, 5, 4, 3, 2, 8, 7] (by decide)
  have hl : V [2, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 8, 7] = V [1, 2, 7] :=
    ((in_context torus7 [2, 4, 5, 6] [6, 5, 4, 3, 2, 8, 7]).trans ((in_context torus6 [2, 4, 5] [5, 4, 3, 2, 8, 7]).trans ((in_context torus5 [2, 4] [4, 3, 2, 8, 7]).trans ((in_context torus4 [2] [3, 2, 8, 7]).trans ((in_context torus1436 [] [8, 7]).trans (in_context torus8 [1, 2] [7]))))))
  have hr : V [4, 1, 8, 3, 2, 3, 4, 5, 6, 7, 8, 2, 12] = V [4, 1, 8, 0, 5, 1, 2, 4, 12] :=
    ((in_context torus1439 [4, 1, 8] [4, 5, 6, 7, 8, 2, 12]).trans ((in_context torus4 [4, 1, 8, 0, 3] [5, 6, 7, 8, 2, 12]).trans ((in_context torus1823 [4, 1, 8, 0, 3] [12]).trans (in_context torus3 [4, 1, 8, 0] [5, 1, 2, 4, 12]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2209 : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 12] = V [1, 2] := by
  have h0 : V [1, 2, 7, 7] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 12] :=
    overlap torus2208 torus78 [4, 1, 8, 0, 5, 1, 2, 4] [7] (by decide)
  have hl : V [1, 2, 7, 7] = V [1, 2] :=
    (in_context torus7 [1, 2] [])
  have hr : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 12] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2210 : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 12] = V [1] := by
  have h0 : V [1, 2, 2] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 12] :=
    overlap torus2209 torus48 [4, 1, 8, 0, 5, 1, 2, 4, 3] [2] (by decide)
  have hl : V [1, 2, 2] = V [1] :=
    (in_context torus2 [1] [])
  have hr : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 12] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2211 : V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5, 12] = V [] := by
  have h0 : V [1, 0] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 0, 12] :=
    overlap torus2210 torus93 [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] [0] (by decide)
  have hl : V [1, 0] = V [] :=
    (in_context torus1 [] [])
  have hr : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5, 0, 12] = V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5, 12] :=
    (in_context torus1564 [4, 1, 8, 0, 5, 1, 2] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2212 : V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5] = V [11] := by
  have h0 : V [11] = V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5] :=
    overlap torus2211 torus29 [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5] [11] (by decide)
  have hl : V [11] = V [11] :=
    rfl
  have hr : V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5] = V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2214 : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] = V [1, 11] := by
  have h0 : V [1, 11] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] :=
    overlap torus2210 torus29 [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] [11] (by decide)
  have hl : V [1, 11] = V [1, 11] :=
    rfl
  have hr : V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] = V [4, 1, 8, 0, 5, 1, 2, 4, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2215 : V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6] = V [2, 11] := by
  have h0 : V [11, 5] = V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6] :=
    overlap torus2212 torus5 [4, 1, 8, 0, 5, 1, 2, 0, 4, 6] [5] (by decide)
  have hl : V [11, 5] = V [2, 11] :=
    (in_context torus65 [] [])
  have hr : V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6] = V [4, 1, 8, 0, 5, 1, 2, 0, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2217 : V [4, 1, 8, 0, 5, 1, 2, 4, 3] = V [1, 2, 11] := by
  have h0 : V [2, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 8, 11] = V [4, 1, 8, 3, 2, 3, 4, 5, 6, 7, 8, 2, 3] :=
    overlap torus2074 torus1427 [4, 1, 8, 3] [7, 6, 5, 4, 3, 2, 8, 11] (by decide)
  have hl : V [2, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 8, 11] = V [1, 2, 11] :=
    ((in_context torus7 [2, 4, 5, 6] [6, 5, 4, 3, 2, 8, 11]).trans ((in_context torus6 [2, 4, 5] [5, 4, 3, 2, 8, 11]).trans ((in_context torus5 [2, 4] [4, 3, 2, 8, 11]).trans ((in_context torus4 [2] [3, 2, 8, 11]).trans ((in_context torus1436 [] [8, 11]).trans (in_context torus8 [1, 2] [11]))))))
  have hr : V [4, 1, 8, 3, 2, 3, 4, 5, 6, 7, 8, 2, 3] = V [4, 1, 8, 0, 5, 1, 2, 4, 3] :=
    ((in_context torus1439 [4, 1, 8] [4, 5, 6, 7, 8, 2, 3]).trans ((in_context torus4 [4, 1, 8, 0, 3] [5, 6, 7, 8, 2, 3]).trans ((in_context torus1823 [4, 1, 8, 0, 3] [3]).trans (in_context torus3 [4, 1, 8, 0] [5, 1, 2, 4, 3]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2220 : V [8, 3, 1, 7, 0, 2, 5, 3, 0] = V [4, 0, 6] := by
  have h0 : V [3, 4, 5, 6, 7, 7, 6, 4, 6] = V [8, 3, 1, 7, 0, 2, 5, 3, 0] :=
    overlap torus2054 torus2100 [8, 3, 1, 7] [7, 6, 4, 6] (by decide)
  have hl : V [3, 4, 5, 6, 7, 7, 6, 4, 6] = V [4, 0, 6] :=
    ((in_context torus7 [3, 4, 5, 6] [6, 4, 6]).trans ((in_context torus6 [3, 4, 5] [4, 6]).trans (in_context torus1450 [] [6])))
  have hr : V [8, 3, 1, 7, 0, 2, 5, 3, 0] = V [8, 3, 1, 7, 0, 2, 5, 3, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2226 : V [2, 0, 5, 1, 8, 0, 4, 2, 3] = V [0, 4, 12] := by
  have h0 : V [4, 2, 8, 7, 7, 8, 2, 3, 4, 5, 12] = V [2, 0, 5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] :=
    overlap torus2146 torus1411 [2, 0, 5, 3] [7, 8, 2, 3, 4, 5, 12] (by decide)
  have hl : V [4, 2, 8, 7, 7, 8, 2, 3, 4, 5, 12] = V [0, 4, 12] :=
    ((in_context torus7 [4, 2, 8] [8, 2, 3, 4, 5, 12]).trans ((in_context torus8 [4, 2] [2, 3, 4, 5, 12]).trans ((in_context torus2 [4] [3, 4, 5, 12]).trans ((in_context torus1448 [] [5, 12]).trans (in_context torus5 [0, 4] [12])))))
  have hr : V [2, 0, 5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] = V [2, 0, 5, 1, 8, 0, 4, 2, 3] :=
    ((in_context torus1442 [2, 0, 5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus1446 [2, 0, 5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus2 [2, 0, 5, 1, 3] [8, 7, 6, 5, 4, 3]).trans ((in_context torus1480 [2, 0, 5, 1, 3] [5, 4, 3]).trans ((in_context torus1989 [2, 0, 5, 1, 3] [3]).trans (in_context torus3 [2, 0, 5, 1] [8, 0, 4, 2, 3]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2227 : V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7, 8] = V [12] := by
  have h0 : V [0, 4, 12, 8, 1] = V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7, 8] :=
    overlap torus2226 torus1591 [2, 0, 5, 1, 8, 0, 4] [8, 1] (by decide)
  have hl : V [0, 4, 12, 8, 1] = V [12] :=
    ((in_context torus84 [0, 4] [1]).trans ((in_context torus4 [0] [12, 1]).trans ((in_context torus94 [0] []).trans (in_context torus0 [] [12]))))
  have hr : V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7, 8] = V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2228 : V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7] = V [4, 12] := by
  have h0 : V [12, 8] = V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7] :=
    overlap torus2227 torus8 [2, 0, 5, 1, 8, 0, 4, 1, 2, 7] [8] (by decide)
  have hl : V [12, 8] = V [4, 12] :=
    (in_context torus84 [] [])
  have hr : V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7] = V [2, 0, 5, 1, 8, 0, 4, 1, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2241 : V [0, 5, 6, 1, 4, 3, 5, 1, 4] = V [4, 5, 3] := by
  have h0 : V [1, 4, 3, 4, 3] = V [0, 5, 6, 1, 4, 3, 0, 1, 5, 1, 4] :=
    overlap torus2162 torus1613 [0, 5, 6, 1, 4, 3, 0] [4, 3] (by decide)
  have hl : V [1, 4, 3, 4, 3] = V [4, 5, 3] :=
    ((in_context torus1448 [1] [3]).trans (in_context torus1 [] [4, 5, 3]))
  have hr : V [0, 5, 6, 1, 4, 3, 0, 1, 5, 1, 4] = V [0, 5, 6, 1, 4, 3, 5, 1, 4] :=
    (in_context torus0 [0, 5, 6, 1, 4, 3] [5, 1, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2246 : V [0, 6, 7, 1, 5, 4, 6, 5, 0] = V [5, 7, 6] := by
  have h0 : V [5, 0, 7, 8, 7] = V [0, 6, 7, 1, 5, 4, 6, 5, 7, 7, 0] :=
    overlap torus2166 torus1477 [0, 6, 7, 1, 5, 4, 6, 5, 7] [7, 8, 7] (by decide)
  have hl : V [5, 0, 7, 8, 7] = V [5, 7, 6] :=
    ((in_context torus1478 [5, 0] []).trans ((in_context torus1566 [] [0]).trans ((in_context torus1572 [1] []).trans (in_context torus1 [] [5, 7, 6]))))
  have hr : V [0, 6, 7, 1, 5, 4, 6, 5, 7, 7, 0] = V [0, 6, 7, 1, 5, 4, 6, 5, 0] :=
    (in_context torus7 [0, 6, 7, 1, 5, 4, 6, 5] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2249 : V [0, 7, 8, 1, 6, 5, 7, 1, 6] = V [6, 7, 5] := by
  have h0 : V [1, 6, 5, 6, 5] = V [0, 7, 8, 1, 6, 5, 0, 1, 7, 1, 6] :=
    overlap torus2168 torus1616 [0, 7, 8, 1, 6, 5, 0] [6, 5] (by decide)
  have hl : V [1, 6, 5, 6, 5] = V [6, 7, 5] :=
    ((in_context torus1466 [1] [5]).trans (in_context torus1 [] [6, 7, 5]))
  have hr : V [0, 7, 8, 1, 6, 5, 0, 1, 7, 1, 6] = V [0, 7, 8, 1, 6, 5, 7, 1, 6] :=
    (in_context torus0 [0, 7, 8, 1, 6, 5] [7, 1, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2251 : V [0, 8, 2, 1, 7, 6, 8, 7, 2] = V [7, 0, 8] := by
  have h0 : V [1, 7, 6, 8, 2] = V [0, 8, 2, 1, 7, 6, 0, 8, 0, 2, 3] :=
    overlap torus2171 torus1428 [0, 8, 2, 1, 7, 6, 0, 8] [8, 2] (by decide)
  have hl : V [1, 7, 6, 8, 2] = V [7, 0, 8] :=
    (in_context torus1527 [] [])
  have hr : V [0, 8, 2, 1, 7, 6, 0, 8, 0, 2, 3] = V [0, 8, 2, 1, 7, 6, 8, 7, 2] :=
    ((in_context torus1586 [0, 8, 2, 1, 7, 6, 0] []).trans (in_context torus0 [0, 8, 2, 1, 7, 6] [8, 7, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2252 : V [0, 8, 2, 1, 7, 6, 8, 6, 7] = V [7, 8, 1] := by
  have h0 : V [1, 7, 6, 7, 1] = V [0, 8, 2, 1, 7, 6, 0, 1, 8, 6, 7] :=
    overlap torus2171 torus1598 [0, 8, 2, 1, 7, 6, 0] [7, 1] (by decide)
  have hl : V [1, 7, 6, 7, 1] = V [7, 8, 1] :=
    ((in_context torus1475 [1] [1]).trans (in_context torus1 [] [7, 8, 1]))
  have hr : V [0, 8, 2, 1, 7, 6, 0, 1, 8, 6, 7] = V [0, 8, 2, 1, 7, 6, 8, 6, 7] :=
    (in_context torus0 [0, 8, 2, 1, 7, 6] [8, 6, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2256 : V [1, 8, 7, 0, 2, 3, 8, 3, 2] = V [2, 8, 0] := by
  have h0 : V [0, 2, 3, 2, 0] = V [1, 8, 7, 0, 2, 3, 1, 0, 8, 3, 2] :=
    overlap torus2174 torus1593 [1, 8, 7, 0, 2, 3, 1] [2, 0] (by decide)
  have hl : V [0, 2, 3, 2, 0] = V [2, 8, 0] :=
    (in_context torus1433 [] [0])
  have hr : V [1, 8, 7, 0, 2, 3, 1, 0, 8, 3, 2] = V [1, 8, 7, 0, 2, 3, 8, 3, 2] :=
    (in_context torus1 [1, 8, 7, 0, 2, 3] [8, 3, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2257 : V [1, 8, 7, 0, 2, 3, 8, 0, 2] = V [2, 8, 3] := by
  have h0 : V [0, 2, 3, 2, 3] = V [1, 8, 7, 0, 2, 3, 1, 0, 8, 0, 2] :=
    overlap torus2174 torus1617 [1, 8, 7, 0, 2, 3, 1] [2, 3] (by decide)
  have hl : V [0, 2, 3, 2, 3] = V [2, 8, 3] :=
    (in_context torus1433 [] [3])
  have hr : V [1, 8, 7, 0, 2, 3, 1, 0, 8, 0, 2] = V [1, 8, 7, 0, 2, 3, 8, 0, 2] :=
    (in_context torus1 [1, 8, 7, 0, 2, 3] [8, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2259 : V [7, 0, 3, 1, 6, 0, 2, 1, 7] = V [2, 8, 12] := by
  have h0 : V [0, 2, 12, 7, 6] = V [7, 0, 3, 1, 6, 0, 2, 7, 7, 1, 7] :=
    overlap torus2178 torus1480 [7, 0, 3, 1, 6, 0, 2, 7] [7, 6] (by decide)
  have hl : V [0, 2, 12, 7, 6] = V [2, 8, 12] :=
    ((in_context torus78 [0, 2] [6]).trans ((in_context torus72 [0, 2, 3] []).trans (in_context torus1433 [] [12])))
  have hr : V [7, 0, 3, 1, 6, 0, 2, 7, 7, 1, 7] = V [7, 0, 3, 1, 6, 0, 2, 1, 7] :=
    (in_context torus7 [7, 0, 3, 1, 6, 0, 2] [1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2260 : V [5, 0, 8, 1, 4, 0, 7, 1, 5] = V [7, 6, 12] := by
  have h0 : V [0, 7, 12, 5, 4] = V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1, 5] :=
    overlap torus2188 torus1462 [5, 0, 8, 1, 4, 0, 7, 5] [5, 4] (by decide)
  have hl : V [0, 7, 12, 5, 4] = V [7, 6, 12] :=
    ((in_context torus66 [0, 7] [4]).trans ((in_context torus60 [0, 7, 8] []).trans ((in_context torus1478 [0] [12]).trans (in_context torus1474 [] [12]))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1, 5] = V [5, 0, 8, 1, 4, 0, 7, 1, 5] :=
    (in_context torus5 [5, 0, 8, 1, 4, 0, 7] [1, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2261 : V [8, 0, 4, 1, 7, 0, 3, 1, 8] = V [3, 2, 12] := by
  have h0 : V [3, 12, 6] = V [8, 0, 4, 1, 7, 0, 3, 1, 8] :=
    overlap torus2197 torus6 [8, 0, 4, 1, 7, 0, 3, 1, 8] [6] (by decide)
  have hl : V [3, 12, 6] = V [3, 2, 12] :=
    (in_context torus72 [3] [])
  have hr : V [8, 0, 4, 1, 7, 0, 3, 1, 8] = V [8, 0, 4, 1, 7, 0, 3, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2262 : V [4, 1, 8, 0, 5, 1, 2, 0, 4] = V [2, 3, 11] := by
  have h0 : V [2, 11, 6] = V [4, 1, 8, 0, 5, 1, 2, 0, 4] :=
    overlap torus2215 torus6 [4, 1, 8, 0, 5, 1, 2, 0, 4] [6] (by decide)
  have hl : V [2, 11, 6] = V [2, 3, 11] :=
    (in_context torus71 [2] [])
  have hr : V [4, 1, 8, 0, 5, 1, 2, 0, 4] = V [4, 1, 8, 0, 5, 1, 2, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2264 : V [2, 0, 5, 1, 8, 0, 4, 1, 2] = V [4, 3, 12] := by
  have h0 : V [0, 4, 12, 2, 8] = V [2, 0, 5, 1, 8, 0, 4, 2, 2, 1, 2] :=
    overlap torus2226 torus1434 [2, 0, 5, 1, 8, 0, 4, 2] [2, 8] (by decide)
  have hl : V [0, 4, 12, 2, 8] = V [4, 3, 12] :=
    ((in_context torus48 [0, 4] [8]).trans ((in_context torus84 [0, 4, 5] []).trans ((in_context torus1451 [0] [12]).trans (in_context torus1447 [] [12]))))
  have hr : V [2, 0, 5, 1, 8, 0, 4, 2, 2, 1, 2] = V [2, 0, 5, 1, 8, 0, 4, 1, 2] :=
    (in_context torus2 [2, 0, 5, 1, 8, 0, 4] [1, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2265 : V [1, 8, 7, 0, 2, 3, 8, 2] = V [0, 2, 3, 8] := by
  have h0 : V [2, 8, 2, 8, 2, 8, 8, 2] = V [8, 2, 8, 2, 8, 0, 2, 3] :=
    overlap torus166 torus1428 [8, 2, 8, 2, 8] [8, 2] (by decide)
  have hl : V [2, 8, 2, 8, 2, 8, 8, 2] = V [0, 2, 3, 8] :=
    ((in_context torus1428 [] [8, 2, 8, 8, 2]).trans ((in_context torus8 [0, 2, 3, 8, 2] [2]).trans (in_context torus2 [0, 2, 3, 8] [])))
  have hr : V [8, 2, 8, 2, 8, 0, 2, 3] = V [1, 8, 7, 0, 2, 3, 8, 2] :=
    ((in_context torus1428 [8] [8, 0, 2, 3]).trans ((in_context torus1586 [] [8, 0, 2, 3]).trans ((in_context torus1586 [1, 8, 7, 2] []).trans (in_context torus1590 [1, 8, 7] [2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2266 : V [0, 3, 4, 1, 2, 8, 3, 2] = V [1, 2, 8, 3] := by
  have h0 : V [2, 3, 2, 3, 2, 3, 3, 2] = V [3, 2, 3, 2, 3, 1, 2, 8] :=
    overlap torus160 torus1436 [3, 2, 3, 2, 3] [3, 2] (by decide)
  have hl : V [2, 3, 2, 3, 2, 3, 3, 2] = V [1, 2, 8, 3] :=
    ((in_context torus1436 [] [3, 2, 3, 3, 2]).trans ((in_context torus3 [1, 2, 8, 3, 2] [2]).trans (in_context torus2 [1, 2, 8, 3] [])))
  have hr : V [3, 2, 3, 2, 3, 1, 2, 8] = V [0, 3, 4, 1, 2, 8, 3, 2] :=
    ((in_context torus1436 [3] [3, 1, 2, 8]).trans ((in_context torus1541 [] [3, 1, 2, 8]).trans ((in_context torus1541 [0, 3, 4, 2] []).trans (in_context torus1544 [0, 3, 4] [2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2268 : V [0, 4, 5, 1, 3, 2, 4, 3] = V [1, 3, 2, 4] := by
  have h0 : V [3, 4, 3, 4, 3, 4, 4, 3] = V [4, 3, 4, 3, 4, 2, 3, 0] :=
    overlap torus161 torus1442 [4, 3, 4, 3, 4] [4, 3] (by decide)
  have hl : V [3, 4, 3, 4, 3, 4, 4, 3] = V [1, 3, 2, 4] :=
    ((in_context torus1442 [] [4, 3, 4, 4, 3]).trans ((in_context torus4 [2, 3, 0, 4, 3] [3]).trans ((in_context torus3 [2, 3, 0, 4] []).trans (in_context torus1446 [] [4]))))
  have hr : V [4, 3, 4, 3, 4, 2, 3, 0] = V [0, 4, 5, 1, 3, 2, 4, 3] :=
    ((in_context torus1442 [4] [4, 2, 3, 0]).trans ((in_context torus1446 [4] [4, 2, 3, 0]).trans ((in_context torus1554 [] [4, 2, 3, 0]).trans ((in_context torus1446 [0, 4, 5, 3, 4] []).trans ((in_context torus1554 [0, 4, 5, 3] []).trans (in_context torus1550 [0, 4, 5] [3]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2274 : V [0, 6, 7, 1, 5, 4, 6, 5] = V [1, 5, 4, 6] := by
  have h0 : V [5, 6, 5, 6, 5, 6, 6, 5] = V [6, 5, 6, 5, 6, 4, 5, 0] :=
    overlap torus163 torus1460 [6, 5, 6, 5, 6] [6, 5] (by decide)
  have hl : V [5, 6, 5, 6, 5, 6, 6, 5] = V [1, 5, 4, 6] :=
    ((in_context torus1460 [] [6, 5, 6, 6, 5]).trans ((in_context torus6 [4, 5, 0, 6, 5] [5]).trans ((in_context torus5 [4, 5, 0, 6] []).trans (in_context torus1464 [] [6]))))
  have hr : V [6, 5, 6, 5, 6, 4, 5, 0] = V [0, 6, 7, 1, 5, 4, 6, 5] :=
    ((in_context torus1460 [6] [6, 4, 5, 0]).trans ((in_context torus1464 [6] [6, 4, 5, 0]).trans ((in_context torus1569 [] [6, 4, 5, 0]).trans ((in_context torus1464 [0, 6, 7, 5, 6] []).trans ((in_context torus1569 [0, 6, 7, 5] []).trans (in_context torus1566 [0, 6, 7] [5]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2282 : V [8, 7, 0, 2, 3, 1, 8, 7] = V [0, 0, 2, 3] := by
  have h0 : V [0, 8, 2, 2, 8, 2, 8, 2] = V [8, 7, 2, 8, 2, 8, 2, 8] :=
    overlap torus1484 torus166 [8, 7] [2, 8, 2, 8, 2] (by decide)
  have hl : V [0, 8, 2, 2, 8, 2, 8, 2] = V [0, 0, 2, 3] :=
    ((in_context torus2 [0, 8] [8, 2, 8, 2]).trans ((in_context torus8 [0] [2, 8, 2]).trans (in_context torus1428 [0] [])))
  have hr : V [8, 7, 2, 8, 2, 8, 2, 8] = V [8, 7, 0, 2, 3, 1, 8, 7] :=
    ((in_context torus1428 [8, 7] [8, 2, 8]).trans ((in_context torus1487 [8, 7, 0, 2, 3] []).trans (in_context torus1490 [8, 7, 0, 2, 3] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2304 : V [0, 3, 8, 3, 2, 4, 1, 8] = V [7, 2, 8, 3] := by
  have h0 : V [7, 2, 7, 7, 8, 3] = V [0, 3, 8, 3, 2, 5, 4, 3, 4, 8] :=
    overlap torus1675 torus297 [0, 3, 8, 3] [7, 8, 3] (by decide)
  have hl : V [7, 2, 7, 7, 8, 3] = V [7, 2, 8, 3] :=
    (in_context torus7 [7, 2] [8, 3])
  have hr : V [0, 3, 8, 3, 2, 5, 4, 3, 4, 8] = V [0, 3, 8, 3, 2, 4, 1, 8] :=
    ((in_context torus1453 [0, 3, 8, 3, 2] [4, 8]).trans (in_context torus4 [0, 3, 8, 3, 2, 4, 1] [8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2310 : V [7, 1, 6, 3, 1, 3, 7, 2] = V [0, 7, 6, 0] := by
  have h0 : V [0, 7, 8, 6, 6, 8, 6, 0] = V [7, 1, 6, 3, 1, 3, 7, 2] :=
    overlap torus1577 torus1762 [7, 1, 6] [6, 8, 6, 0] (by decide)
  have hl : V [0, 7, 8, 6, 6, 8, 6, 0] = V [0, 7, 6, 0] :=
    ((in_context torus6 [0, 7, 8] [8, 6, 0]).trans (in_context torus8 [0, 7] [6, 0]))
  have hr : V [7, 1, 6, 3, 1, 3, 7, 2] = V [7, 1, 6, 3, 1, 3, 7, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2312 : V [7, 2, 1, 6, 0, 8, 4, 2] = V [3, 0, 5, 1] := by
  have h0 : V [2, 3, 4, 5, 5, 3, 6, 5, 4, 5] = V [7, 2, 1, 6, 8, 7, 8, 2, 4, 2] :=
    overlap torus1768 torus173 [7, 2, 1, 6, 8] [5, 3, 6, 5, 4, 5] (by decide)
  have hl : V [2, 3, 4, 5, 5, 3, 6, 5, 4, 5] = V [3, 0, 5, 1] :=
    ((in_context torus5 [2, 3, 4] [3, 6, 5, 4, 5]).trans ((in_context torus1441 [] [6, 5, 4, 5]).trans ((in_context torus1462 [3, 0] [5]).trans (in_context torus5 [3, 0, 5, 1] []))))
  have hr : V [7, 2, 1, 6, 8, 7, 8, 2, 4, 2] = V [7, 2, 1, 6, 0, 8, 4, 2] :=
    ((in_context torus1484 [7, 2, 1, 6] [2, 4, 2]).trans (in_context torus2 [7, 2, 1, 6, 0, 8] [4, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2318 : V [5, 7, 1, 4, 0, 6, 2, 7] = V [8, 0, 3, 1] := by
  have h0 : V [7, 8, 2, 3, 4, 4, 3, 8, 3, 1] = V [5, 8, 7, 6, 7, 4, 0, 6, 2, 7] :=
    overlap torus217 torus1782 [5, 8, 7, 6, 7, 4] [4, 3, 8, 3, 1] (by decide)
  have hl : V [7, 8, 2, 3, 4, 4, 3, 8, 3, 1] = V [8, 0, 3, 1] :=
    ((in_context torus1429 [7] [4, 4, 3, 8, 3, 1]).trans ((in_context torus4 [7, 2, 0, 2] [3, 8, 3, 1]).trans ((in_context torus1438 [7] [8, 3, 1]).trans (in_context torus1486 [] [3, 1]))))
  have hr : V [5, 8, 7, 6, 7, 4, 0, 6, 2, 7] = V [5, 7, 1, 4, 0, 6, 2, 7] :=
    ((in_context torus1480 [5] [7, 4, 0, 6, 2, 7]).trans (in_context torus7 [5, 7, 1] [4, 0, 6, 2, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2320 : V [0, 4, 2, 3, 8, 3, 1, 7] = V [8, 3, 8, 2] := by
  have h0 : V [8, 3, 8, 7, 6, 6, 7, 2] = V [4, 3, 4, 5, 2, 3, 8, 3, 1, 7] :=
    overlap torus307 torus1783 [4, 3, 4, 5, 2] [6, 7, 2] (by decide)
  have hl : V [8, 3, 8, 7, 6, 6, 7, 2] = V [8, 3, 8, 2] :=
    ((in_context torus1480 [8, 3] [6, 7, 2]).trans ((in_context torus1481 [8, 3] [7, 2]).trans (in_context torus7 [8, 3, 8] [2])))
  have hr : V [4, 3, 4, 5, 2, 3, 8, 3, 1, 7] = V [0, 4, 2, 3, 8, 3, 1, 7] :=
    ((in_context torus1448 [] [5, 2, 3, 8, 3, 1, 7]).trans (in_context torus5 [0, 4] [2, 3, 8, 3, 1, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2322 : V [8, 3, 1, 7, 0, 2, 5, 3] = V [4, 0, 6, 1] := by
  have h0 : V [3, 4, 5, 6, 6, 4, 7, 6, 5, 6] = V [8, 3, 1, 7, 2, 8, 2, 3, 5, 3] :=
    overlap torus1786 torus193 [8, 3, 1, 7, 2] [6, 4, 7, 6, 5, 6] (by decide)
  have hl : V [3, 4, 5, 6, 6, 4, 7, 6, 5, 6] = V [4, 0, 6, 1] :=
    ((in_context torus6 [3, 4, 5] [4, 7, 6, 5, 6]).trans ((in_context torus1450 [] [7, 6, 5, 6]).trans ((in_context torus1471 [4, 0] [6]).trans (in_context torus6 [4, 0, 6, 1] []))))
  have hr : V [8, 3, 1, 7, 2, 8, 2, 3, 5, 3] = V [8, 3, 1, 7, 0, 2, 5, 3] :=
    ((in_context torus1428 [8, 3, 1, 7] [3, 5, 3]).trans (in_context torus3 [8, 3, 1, 7, 0, 2] [5, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2323 : V [8, 0, 4, 2, 3, 8, 3, 1] = V [3, 8, 2, 7] := by
  have h0 : V [3, 7, 1, 7, 6, 7, 2, 7] = V [8, 0, 4, 2, 4, 4, 3, 8, 3, 1] :=
    overlap torus1790 torus1781 [8, 0, 4, 2, 4] [6, 7, 2, 7] (by decide)
  have hl : V [3, 7, 1, 7, 6, 7, 2, 7] = V [3, 8, 2, 7] :=
    ((in_context torus1481 [3] [7, 2, 7]).trans (in_context torus7 [3, 8] [2, 7]))
  have hr : V [8, 0, 4, 2, 4, 4, 3, 8, 3, 1] = V [8, 0, 4, 2, 3, 8, 3, 1] :=
    (in_context torus4 [8, 0, 4, 2] [3, 8, 3, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2324 : V [2, 1, 8, 5, 1, 5, 2, 4] = V [0, 2, 8, 0] := by
  have h0 : V [0, 2, 3, 8, 8, 3, 8, 0] = V [2, 1, 8, 5, 1, 5, 2, 4] :=
    overlap torus1590 torus1796 [2, 1, 8] [8, 3, 8, 0] (by decide)
  have hl : V [0, 2, 3, 8, 8, 3, 8, 0] = V [0, 2, 8, 0] :=
    ((in_context torus8 [0, 2, 3] [3, 8, 0]).trans (in_context torus3 [0, 2] [8, 0]))
  have hr : V [2, 1, 8, 5, 1, 5, 2, 4] = V [2, 1, 8, 5, 1, 5, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2325 : V [6, 8, 1, 5, 0, 7, 3, 8] = V [2, 0, 4, 1] := by
  have h0 : V [8, 2, 3, 4, 5, 5, 4, 2, 4, 1] = V [6, 2, 8, 7, 8, 5, 0, 7, 3, 8] :=
    overlap torus237 torus1802 [6, 2, 8, 7, 8, 5] [5, 4, 2, 4, 1] (by decide)
  have hl : V [8, 2, 3, 4, 5, 5, 4, 2, 4, 1] = V [2, 0, 4, 1] :=
    ((in_context torus1429 [] [4, 5, 5, 4, 2, 4, 1]).trans ((in_context torus5 [2, 0, 2, 4] [4, 2, 4, 1]).trans ((in_context torus4 [2, 0, 2] [2, 4, 1]).trans (in_context torus2 [2, 0] [4, 1]))))
  have hr : V [6, 2, 8, 7, 8, 5, 0, 7, 3, 8] = V [6, 8, 1, 5, 0, 7, 3, 8] :=
    ((in_context torus1484 [6, 2] [5, 0, 7, 3, 8]).trans (in_context torus1491 [6] [5, 0, 7, 3, 8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2328 : V [0, 6, 4, 5, 3, 5, 1, 2] = V [3, 5, 3, 4] := by
  have h0 : V [3, 5, 3, 2, 8, 7, 7, 8, 2, 4] = V [6, 5, 6, 7, 4, 5, 3, 5, 1, 2] :=
    overlap torus204 torus1820 [6, 5, 6, 7, 4] [7, 8, 2, 4] (by decide)
  have hl : V [3, 5, 3, 2, 8, 7, 7, 8, 2, 4] = V [3, 5, 3, 4] :=
    ((in_context torus1434 [3, 5] [7, 7, 8, 2, 4]).trans ((in_context torus7 [3, 5, 2, 1, 2] [8, 2, 4]).trans ((in_context torus1435 [3, 5] [2, 4]).trans (in_context torus2 [3, 5, 3] [4]))))
  have hr : V [6, 5, 6, 7, 4, 5, 3, 5, 1, 2] = V [0, 6, 4, 5, 3, 5, 1, 2] :=
    ((in_context torus1466 [] [7, 4, 5, 3, 5, 1, 2]).trans (in_context torus7 [0, 6] [4, 5, 3, 5, 1, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2329 : V [0, 7, 5, 6, 4, 6, 1, 3] = V [4, 6, 4, 5] := by
  have h0 : V [4, 6, 4, 3, 2, 8, 2, 0, 2, 5] = V [7, 6, 7, 8, 5, 6, 4, 6, 1, 3] :=
    overlap torus224 torus1837 [7, 6, 7, 8, 5] [2, 0, 2, 5] (by decide)
  have hl : V [4, 6, 4, 3, 2, 8, 2, 0, 2, 5] = V [4, 6, 4, 5] :=
    ((in_context torus1444 [4, 6] [8, 2, 0, 2, 5]).trans ((in_context torus1519 [4, 6] [0, 2, 5]).trans ((in_context torus1 [4, 6, 4, 2] [2, 5]).trans (in_context torus2 [4, 6, 4] [5]))))
  have hr : V [7, 6, 7, 8, 5, 6, 4, 6, 1, 3] = V [0, 7, 5, 6, 4, 6, 1, 3] :=
    ((in_context torus1475 [] [8, 5, 6, 4, 6, 1, 3]).trans (in_context torus8 [0, 7] [5, 6, 4, 6, 1, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2330 : V [5, 1, 2, 4, 3, 5, 3, 0] = V [3, 5, 4, 6] := by
  have h0 : V [3, 5, 7, 0, 1, 7, 4, 6] = V [5, 1, 2, 4, 2, 2, 3, 5, 3, 0] :=
    overlap torus1732 torus1842 [5, 1, 2, 4, 2] [1, 7, 4, 6] (by decide)
  have hl : V [3, 5, 7, 0, 1, 7, 4, 6] = V [3, 5, 4, 6] :=
    ((in_context torus0 [3, 5, 7] [7, 4, 6]).trans (in_context torus7 [3, 5] [4, 6]))
  have hr : V [5, 1, 2, 4, 2, 2, 3, 5, 3, 0] = V [5, 1, 2, 4, 3, 5, 3, 0] :=
    (in_context torus2 [5, 1, 2, 4] [3, 5, 3, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2333 : V [4, 1, 4, 2, 8, 7, 5, 7] = V [5, 6, 4, 0] := by
  have h0 : V [5, 4, 4, 6, 4, 0] = V [4, 1, 4, 2, 8, 7, 5, 7] :=
    overlap torus1454 torus1856 [4, 1, 4] [4, 6, 4, 0] (by decide)
  have hl : V [5, 4, 4, 6, 4, 0] = V [5, 6, 4, 0] :=
    (in_context torus4 [5] [6, 4, 0])
  have hr : V [4, 1, 4, 2, 8, 7, 5, 7] = V [4, 1, 4, 2, 8, 7, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2336 : V [6, 1, 5, 2, 1, 2, 6, 8] = V [0, 6, 5, 0] := by
  have h0 : V [0, 6, 7, 5, 5, 7, 5, 0] = V [6, 1, 5, 2, 1, 2, 6, 8] :=
    overlap torus1569 torus1874 [6, 1, 5] [5, 7, 5, 0] (by decide)
  have hl : V [0, 6, 7, 5, 5, 7, 5, 0] = V [0, 6, 5, 0] :=
    ((in_context torus5 [0, 6, 7] [7, 5, 0]).trans (in_context torus7 [0, 6] [5, 0]))
  have hr : V [6, 1, 5, 2, 1, 2, 6, 8] = V [6, 1, 5, 2, 1, 2, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2337 : V [5, 7, 4, 1, 2, 0, 5, 3] = V [0, 8, 1, 6] := by
  have h0 : V [0, 8, 6, 6, 1, 6] = V [5, 7, 4, 1, 4, 2, 7, 1, 7, 5] :=
    overlap torus1885 torus1584 [5, 7, 4, 1, 4, 2] [6, 1, 6] (by decide)
  have hl : V [0, 8, 6, 6, 1, 6] = V [0, 8, 1, 6] :=
    (in_context torus6 [0, 8] [1, 6])
  have hr : V [5, 7, 4, 1, 4, 2, 7, 1, 7, 5] = V [5, 7, 4, 1, 2, 0, 5, 3] :=
    (in_context torus1683 [5, 7, 4, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2338 : V [5, 0, 8, 6, 7, 5, 7, 1] = V [7, 5, 6, 4] := by
  have h0 : V [7, 5, 4, 2, 2, 4, 6, 4] = V [5, 0, 8, 6, 7, 5, 7, 1] :=
    overlap torus1886 torus1736 [5, 0, 8, 6] [2, 4, 6, 4] (by decide)
  have hl : V [7, 5, 4, 2, 2, 4, 6, 4] = V [7, 5, 6, 4] :=
    ((in_context torus2 [7, 5, 4] [4, 6, 4]).trans (in_context torus4 [7, 5] [6, 4]))
  have hr : V [5, 0, 8, 6, 7, 5, 7, 1] = V [5, 0, 8, 6, 7, 5, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2340 : V [4, 2, 0, 5, 1, 3, 7, 2] = V [8, 1, 6, 0] := by
  have h0 : V [8, 1, 6, 0] = V [4, 2, 0, 5, 3, 3, 1, 3, 7, 2] :=
    overlap torus1953 torus1762 [4, 2, 0, 5, 3] [6, 0] (by decide)
  have hl : V [8, 1, 6, 0] = V [8, 1, 6, 0] :=
    rfl
  have hr : V [4, 2, 0, 5, 3, 3, 1, 3, 7, 2] = V [4, 2, 0, 5, 1, 3, 7, 2] :=
    (in_context torus3 [4, 2, 0, 5] [1, 3, 7, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2341 : V [3, 5, 1, 2, 0, 4, 7, 5] = V [6, 0, 8, 1] := by
  have h0 : V [5, 6, 7, 6, 2, 8, 7, 8] = V [3, 5, 1, 2, 4, 2, 2, 3, 4, 5, 7, 5] :=
    overlap torus1958 torus235 [3, 5, 1, 2, 4, 2] [6, 2, 8, 7, 8] (by decide)
  have hl : V [5, 6, 7, 6, 2, 8, 7, 8] = V [6, 0, 8, 1] :=
    ((in_context torus1468 [] [2, 8, 7, 8]).trans ((in_context torus1484 [6, 0, 2] []).trans (in_context torus1491 [6, 0] [])))
  have hr : V [3, 5, 1, 2, 4, 2, 2, 3, 4, 5, 7, 5] = V [3, 5, 1, 2, 0, 4, 7, 5] :=
    ((in_context torus2 [3, 5, 1, 2, 4] [3, 4, 5, 7, 5]).trans ((in_context torus1448 [3, 5, 1, 2] [5, 7, 5]).trans (in_context torus5 [3, 5, 1, 2, 0, 4] [7, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2343 : V [0, 6, 4, 6, 5, 7, 1, 4] = V [3, 5, 4, 6] := by
  have h0 : V [3, 5, 2, 2, 4, 6] = V [0, 6, 4, 6, 5, 7, 1, 4] :=
    overlap torus1969 torus1861 [0, 6, 4, 6] [2, 4, 6] (by decide)
  have hl : V [3, 5, 2, 2, 4, 6] = V [3, 5, 4, 6] :=
    (in_context torus2 [3, 5] [4, 6])
  have hr : V [0, 6, 4, 6, 5, 7, 1, 4] = V [0, 6, 4, 6, 5, 7, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2344 : V [6, 4, 6, 5, 7, 1, 4, 6] = V [1, 3, 5, 4] := by
  have h0 : V [1, 3, 5, 2, 2, 4] = V [6, 4, 6, 5, 7, 1, 4, 6] :=
    overlap torus1970 torus1863 [6, 4, 6] [2, 4] (by decide)
  have hl : V [1, 3, 5, 2, 2, 4] = V [1, 3, 5, 4] :=
    (in_context torus2 [1, 3, 5] [4])
  have hr : V [6, 4, 6, 5, 7, 1, 4, 6] = V [6, 4, 6, 5, 7, 1, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2350 : V [5, 1, 2, 0, 6, 1, 3, 5] = V [1, 3, 8, 11] := by
  have h0 : V [3, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 8, 11] = V [5, 1, 2, 4, 3, 4, 5, 6, 7, 8, 2, 3] :=
    overlap torus2018 torus1426 [5, 1, 2, 4] [8, 7, 6, 5, 4, 3, 2, 8, 11] (by decide)
  have hl : V [3, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 8, 11] = V [1, 3, 8, 11] :=
    ((in_context torus8 [3, 5, 6, 7] [7, 6, 5, 4, 3, 2, 8, 11]).trans ((in_context torus7 [3, 5, 6] [6, 5, 4, 3, 2, 8, 11]).trans ((in_context torus6 [3, 5] [5, 4, 3, 2, 8, 11]).trans ((in_context torus5 [3] [4, 3, 2, 8, 11]).trans ((in_context torus1442 [] [2, 8, 11]).trans ((in_context torus1446 [] [2, 8, 11]).trans (in_context torus2 [1, 3] [8, 11])))))))
  have hr : V [5, 1, 2, 4, 3, 4, 5, 6, 7, 8, 2, 3] = V [5, 1, 2, 0, 6, 1, 3, 5] :=
    ((in_context torus1448 [5, 1, 2] [5, 6, 7, 8, 2, 3]).trans ((in_context torus5 [5, 1, 2, 0, 4] [6, 7, 8, 2, 3]).trans ((in_context torus1429 [5, 1, 2, 0, 4, 6, 7] []).trans ((in_context torus1839 [5, 1, 2, 0, 4] []).trans (in_context torus4 [5, 1, 2, 0] [6, 1, 3, 5])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2351 : V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [11] := by
  have h0 : V [1, 3, 8, 11, 4, 6, 0] = V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] :=
    overlap torus2350 torus1572 [5, 1, 2, 0, 6, 1, 3] [4, 6, 0] (by decide)
  have hl : V [1, 3, 8, 11, 4, 6, 0] = V [11] :=
    ((in_context torus59 [1, 3, 8] [6, 0]).trans ((in_context torus8 [1, 3] [11, 6, 0]).trans ((in_context torus71 [1, 3] [0]).trans ((in_context torus3 [1] [11, 0]).trans ((in_context torus91 [1] []).trans (in_context torus1 [] [11]))))))
  have hr : V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2352 : V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] = V [3, 11] := by
  have h0 : V [11, 6] = V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] :=
    overlap torus2351 torus6 [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] [6] (by decide)
  have hl : V [11, 6] = V [3, 11] :=
    (in_context torus71 [] [])
  have hr : V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] = V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2356 : V [0, 5, 1, 8, 0, 4, 2, 3] = V [2, 0, 4, 12] := by
  have h0 : V [2, 4, 2, 2, 3, 4, 5, 12] = V [0, 5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] :=
    overlap torus2019 torus1411 [0, 5, 3] [2, 3, 4, 5, 12] (by decide)
  have hl : V [2, 4, 2, 2, 3, 4, 5, 12] = V [2, 0, 4, 12] :=
    ((in_context torus2 [2, 4] [3, 4, 5, 12]).trans ((in_context torus1448 [2] [5, 12]).trans (in_context torus5 [2, 0, 4] [12])))
  have hr : V [0, 5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] = V [0, 5, 1, 8, 0, 4, 2, 3] :=
    ((in_context torus1442 [0, 5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus1446 [0, 5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus2 [0, 5, 1, 3] [8, 7, 6, 5, 4, 3]).trans ((in_context torus1480 [0, 5, 1, 3] [5, 4, 3]).trans ((in_context torus1989 [0, 5, 1, 3] [3]).trans (in_context torus3 [0, 5, 1] [8, 0, 4, 2, 3]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2358 : V [0, 5, 3, 4, 2, 4, 1, 8] = V [2, 4, 2, 3] := by
  have h0 : V [2, 4, 2, 3] = V [0, 5, 3, 4, 2, 4, 1, 8] :=
    overlap torus2019 torus1803 [0, 5, 3] [3] (by decide)
  have hl : V [2, 4, 2, 3] = V [2, 4, 2, 3] :=
    rfl
  have hr : V [0, 5, 3, 4, 2, 4, 1, 8] = V [0, 5, 3, 4, 2, 4, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2360 : V [6, 1, 3, 0, 7, 1, 4, 6] = V [1, 4, 2, 11] := by
  have h0 : V [4, 6, 7, 8, 2, 2, 8, 7, 6, 5, 4, 3, 2, 11] = V [6, 1, 3, 5, 4, 5, 6, 7, 8, 2, 3, 4] :=
    overlap torus2022 torus1424 [6, 1, 3, 5] [2, 8, 7, 6, 5, 4, 3, 2, 11] (by decide)
  have hl : V [4, 6, 7, 8, 2, 2, 8, 7, 6, 5, 4, 3, 2, 11] = V [1, 4, 2, 11] :=
    ((in_context torus2 [4, 6, 7, 8] [8, 7, 6, 5, 4, 3, 2, 11]).trans ((in_context torus8 [4, 6, 7] [7, 6, 5, 4, 3, 2, 11]).trans ((in_context torus7 [4, 6] [6, 5, 4, 3, 2, 11]).trans ((in_context torus6 [4] [5, 4, 3, 2, 11]).trans ((in_context torus1451 [] [3, 2, 11]).trans ((in_context torus1455 [] [3, 2, 11]).trans (in_context torus3 [1, 4] [2, 11])))))))
  have hr : V [6, 1, 3, 5, 4, 5, 6, 7, 8, 2, 3, 4] = V [6, 1, 3, 0, 7, 1, 4, 6] :=
    ((in_context torus1457 [6, 1, 3] [6, 7, 8, 2, 3, 4]).trans ((in_context torus6 [6, 1, 3, 0, 5] [7, 8, 2, 3, 4]).trans ((in_context torus1429 [6, 1, 3, 0, 5, 7] [4]).trans ((in_context torus1863 [6, 1, 3, 0, 5] []).trans (in_context torus5 [6, 1, 3, 0] [7, 1, 4, 6])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2361 : V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 7] = V [11] := by
  have h0 : V [1, 4, 2, 11, 5, 7, 0] = V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 7] :=
    overlap torus2360 torus1580 [6, 1, 3, 0, 7, 1, 4] [5, 7, 0] (by decide)
  have hl : V [1, 4, 2, 11, 5, 7, 0] = V [11] :=
    ((in_context torus65 [1, 4, 2] [7, 0]).trans ((in_context torus2 [1, 4] [11, 7, 0]).trans ((in_context torus77 [1, 4] [0]).trans ((in_context torus4 [1] [11, 0]).trans ((in_context torus91 [1] []).trans (in_context torus1 [] [11]))))))
  have hr : V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 7] = V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2362 : V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] = V [4, 11] := by
  have h0 : V [11, 7] = V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] :=
    overlap torus2361 torus7 [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] [7] (by decide)
  have hl : V [11, 7] = V [4, 11] :=
    (in_context torus77 [] [])
  have hr : V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] = V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2364 : V [7, 1, 4, 0, 8, 1, 5, 7] = V [1, 5, 3, 11] := by
  have h0 : V [5, 7, 2, 0, 2, 3, 2, 8, 7, 6, 5, 4, 3, 11] = V [7, 1, 4, 6, 5, 6, 7, 8, 2, 3, 4, 5] :=
    overlap torus2024 torus1422 [7, 1, 4, 6] [3, 2, 8, 7, 6, 5, 4, 3, 11] (by decide)
  have hl : V [5, 7, 2, 0, 2, 3, 2, 8, 7, 6, 5, 4, 3, 11] = V [1, 5, 3, 11] :=
    ((in_context torus1438 [5, 7] [2, 8, 7, 6, 5, 4, 3, 11]).trans ((in_context torus2 [5, 7, 8] [8, 7, 6, 5, 4, 3, 11]).trans ((in_context torus8 [5, 7] [7, 6, 5, 4, 3, 11]).trans ((in_context torus7 [5] [6, 5, 4, 3, 11]).trans ((in_context torus1460 [] [4, 3, 11]).trans ((in_context torus1464 [] [4, 3, 11]).trans (in_context torus4 [1, 5] [3, 11])))))))
  have hr : V [7, 1, 4, 6, 5, 6, 7, 8, 2, 3, 4, 5] = V [7, 1, 4, 0, 8, 1, 5, 7] :=
    ((in_context torus1466 [7, 1, 4] [7, 8, 2, 3, 4, 5]).trans ((in_context torus7 [7, 1, 4, 0, 6] [8, 2, 3, 4, 5]).trans ((in_context torus238 [7, 1, 4, 0] []).trans ((in_context torus1484 [7, 1, 4, 0, 2] [5, 7]).trans (in_context torus1491 [7, 1, 4, 0] [5, 7])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2365 : V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [11] := by
  have h0 : V [1, 5, 3, 11, 6, 8, 0] = V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 8] :=
    overlap torus2364 torus1588 [7, 1, 4, 0, 8, 1, 5] [6, 8, 0] (by decide)
  have hl : V [1, 5, 3, 11, 6, 8, 0] = V [11] :=
    ((in_context torus71 [1, 5, 3] [8, 0]).trans ((in_context torus3 [1, 5] [11, 8, 0]).trans ((in_context torus83 [1, 5] [0]).trans ((in_context torus5 [1] [11, 0]).trans ((in_context torus91 [1] []).trans (in_context torus1 [] [11]))))))
  have hr : V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2366 : V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] = V [5, 11] := by
  have h0 : V [11, 8] = V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] :=
    overlap torus2365 torus8 [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] [8] (by decide)
  have hl : V [11, 8] = V [5, 11] :=
    (in_context torus83 [] [])
  have hr : V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] = V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2367 : V [7, 1, 4, 0, 8, 1, 5, 0, 7] = V [5, 6, 11] := by
  have h0 : V [5, 11, 2] = V [7, 1, 4, 0, 8, 1, 5, 0, 7] :=
    overlap torus2366 torus2 [7, 1, 4, 0, 8, 1, 5, 0, 7] [2] (by decide)
  have hl : V [5, 11, 2] = V [5, 6, 11] :=
    (in_context torus47 [5] [])
  have hr : V [7, 1, 4, 0, 8, 1, 5, 0, 7] = V [7, 1, 4, 0, 8, 1, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2373 : V [7, 1, 4, 0, 6, 2, 7, 0] = V [5, 8, 0, 3] := by
  have h0 : V [5, 7, 8, 2, 3, 4, 4, 3, 8, 3] = V [8, 7, 6, 7, 4, 0, 6, 2, 7, 0] :=
    overlap torus218 torus2044 [8, 7, 6, 7, 4] [4, 3, 8, 3] (by decide)
  have hl : V [5, 7, 8, 2, 3, 4, 4, 3, 8, 3] = V [5, 8, 0, 3] :=
    ((in_context torus1429 [5, 7] [4, 4, 3, 8, 3]).trans ((in_context torus1863 [5] [4, 3, 8, 3]).trans ((in_context torus5 [] [7, 1, 4, 6, 4, 3, 8, 3]).trans (in_context torus1661 [] [3]))))
  have hr : V [8, 7, 6, 7, 4, 0, 6, 2, 7, 0] = V [7, 1, 4, 0, 6, 2, 7, 0] :=
    ((in_context torus1480 [] [7, 4, 0, 6, 2, 7, 0]).trans (in_context torus7 [7, 1] [4, 0, 6, 2, 7, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2376 : V [6, 0, 2, 1, 7, 4, 6, 1] = V [8, 5, 1, 3] := by
  have h0 : V [8, 6, 5, 4, 3, 3, 5, 3] = V [6, 2, 8, 2, 3, 1, 7, 4, 6, 1] :=
    overlap torus267 torus2057 [6, 2, 8, 2, 3] [3, 5, 3] (by decide)
  have hl : V [8, 6, 5, 4, 3, 3, 5, 3] = V [8, 5, 1, 3] :=
    ((in_context torus1462 [8] [3, 3, 5, 3]).trans ((in_context torus1758 [] [3, 5, 3]).trans ((in_context torus1748 [6] [3]).trans (in_context torus6 [] [8, 5, 1, 3]))))
  have hr : V [6, 2, 8, 2, 3, 1, 7, 4, 6, 1] = V [6, 0, 2, 1, 7, 4, 6, 1] :=
    ((in_context torus1428 [6] [3, 1, 7, 4, 6, 1]).trans (in_context torus3 [6, 0, 2] [1, 7, 4, 6, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2377 : V [4, 1, 8, 0, 3, 6, 4, 0] = V [2, 5, 0, 7] := by
  have h0 : V [2, 4, 5, 6, 7, 8, 8, 7, 5, 7] = V [5, 4, 3, 4, 8, 0, 3, 6, 4, 0] :=
    overlap torus299 torus2059 [5, 4, 3, 4, 8] [8, 7, 5, 7] (by decide)
  have hl : V [2, 4, 5, 6, 7, 8, 8, 7, 5, 7] = V [2, 5, 0, 7] :=
    ((in_context torus1805 [2] [8, 7, 5, 7]).trans ((in_context torus2 [] [4, 1, 8, 3, 8, 7, 5, 7]).trans ((in_context torus1792 [4] [7]).trans (in_context torus4 [] [2, 5, 0, 7]))))
  have hr : V [5, 4, 3, 4, 8, 0, 3, 6, 4, 0] = V [4, 1, 8, 0, 3, 6, 4, 0] :=
    ((in_context torus1453 [] [4, 8, 0, 3, 6, 4, 0]).trans (in_context torus4 [4, 1] [8, 0, 3, 6, 4, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2379 : V [7, 5, 0, 8, 1, 6, 3, 5] = V [4, 1, 2, 0] := by
  have h0 : V [4, 1, 4, 2, 2, 4, 2, 0] = V [7, 5, 0, 8, 6, 6, 1, 6, 3, 5] :=
    overlap torus2064 torus1813 [7, 5, 0, 8, 6] [2, 4, 2, 0] (by decide)
  have hl : V [4, 1, 4, 2, 2, 4, 2, 0] = V [4, 1, 2, 0] :=
    ((in_context torus2 [4, 1, 4] [4, 2, 0]).trans (in_context torus4 [4, 1] [2, 0]))
  have hr : V [7, 5, 0, 8, 6, 6, 1, 6, 3, 5] = V [7, 5, 0, 8, 1, 6, 3, 5] :=
    (in_context torus6 [7, 5, 0, 8] [1, 6, 3, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2381 : V [2, 1, 6, 0, 3, 1, 7, 2] = V [1, 7, 5, 11] := by
  have h0 : V [7, 2, 3, 4, 4, 3, 2, 8, 7, 6, 5, 11] = V [2, 1, 6, 8, 7, 8, 2, 3, 4, 5, 6, 7] :=
    overlap torus2081 torus1418 [2, 1, 6, 8] [4, 3, 2, 8, 7, 6, 5, 11] (by decide)
  have hl : V [7, 2, 3, 4, 4, 3, 2, 8, 7, 6, 5, 11] = V [1, 7, 5, 11] :=
    ((in_context torus4 [7, 2, 3] [3, 2, 8, 7, 6, 5, 11]).trans ((in_context torus3 [7, 2] [2, 8, 7, 6, 5, 11]).trans ((in_context torus2 [7] [8, 7, 6, 5, 11]).trans ((in_context torus1478 [] [6, 5, 11]).trans ((in_context torus1482 [] [6, 5, 11]).trans (in_context torus6 [1, 7] [5, 11]))))))
  have hr : V [2, 1, 6, 8, 7, 8, 2, 3, 4, 5, 6, 7] = V [2, 1, 6, 0, 3, 1, 7, 2] :=
    ((in_context torus1484 [2, 1, 6] [2, 3, 4, 5, 6, 7]).trans ((in_context torus2 [2, 1, 6, 0, 8] [3, 4, 5, 6, 7]).trans ((in_context torus278 [2, 1, 6, 0] []).trans ((in_context torus1444 [2, 1, 6, 0] [3, 7, 2]).trans (in_context torus3 [2, 1, 6, 0, 3, 1] [7, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2382 : V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4, 3] = V [11] := by
  have h0 : V [1, 7, 5, 11, 8, 3, 0] = V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4, 3] :=
    overlap torus2381 torus1545 [2, 1, 6, 0, 3, 1, 7] [8, 3, 0] (by decide)
  have hl : V [1, 7, 5, 11, 8, 3, 0] = V [11] :=
    ((in_context torus83 [1, 7, 5] [3, 0]).trans ((in_context torus5 [1, 7] [11, 3, 0]).trans ((in_context torus53 [1, 7] [0]).trans ((in_context torus7 [1] [11, 0]).trans ((in_context torus91 [1] []).trans (in_context torus1 [] [11]))))))
  have hr : V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4, 3] = V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2383 : V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4] = V [7, 11] := by
  have h0 : V [11, 3] = V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4] :=
    overlap torus2382 torus3 [2, 1, 6, 0, 3, 1, 7, 0, 2, 4] [3] (by decide)
  have hl : V [11, 3] = V [7, 11] :=
    (in_context torus53 [] [])
  have hr : V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4] = V [2, 1, 6, 0, 3, 1, 7, 0, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2384 : V [2, 1, 6, 0, 3, 1, 7, 0, 2] = V [7, 8, 11] := by
  have h0 : V [7, 11, 4] = V [2, 1, 6, 0, 3, 1, 7, 0, 2] :=
    overlap torus2383 torus4 [2, 1, 6, 0, 3, 1, 7, 0, 2] [4] (by decide)
  have hl : V [7, 11, 4] = V [7, 8, 11] :=
    (in_context torus59 [7] [])
  have hr : V [2, 1, 6, 0, 3, 1, 7, 0, 2] = V [2, 1, 6, 0, 3, 1, 7, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2388 : V [3, 1, 7, 0, 4, 1, 8, 3] = V [1, 8, 6, 11] := by
  have h0 : V [8, 3, 4, 5, 5, 4, 3, 2, 8, 7, 6, 11] = V [3, 1, 7, 2, 8, 2, 3, 4, 5, 6, 7, 8] :=
    overlap torus2087 torus1416 [3, 1, 7, 2] [5, 4, 3, 2, 8, 7, 6, 11] (by decide)
  have hl : V [8, 3, 4, 5, 5, 4, 3, 2, 8, 7, 6, 11] = V [1, 8, 6, 11] :=
    ((in_context torus5 [8, 3, 4] [4, 3, 2, 8, 7, 6, 11]).trans ((in_context torus4 [8, 3] [3, 2, 8, 7, 6, 11]).trans ((in_context torus3 [8] [2, 8, 7, 6, 11]).trans ((in_context torus1487 [] [7, 6, 11]).trans ((in_context torus1490 [] [7, 6, 11]).trans (in_context torus7 [1, 8] [6, 11]))))))
  have hr : V [3, 1, 7, 2, 8, 2, 3, 4, 5, 6, 7, 8] = V [3, 1, 7, 0, 4, 1, 8, 3] :=
    ((in_context torus1428 [3, 1, 7] [3, 4, 5, 6, 7, 8]).trans ((in_context torus3 [3, 1, 7, 0, 2] [4, 5, 6, 7, 8]).trans ((in_context torus1805 [3, 1, 7, 0, 2] []).trans (in_context torus2 [3, 1, 7, 0] [4, 1, 8, 3]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2389 : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 4] = V [11] := by
  have h0 : V [1, 8, 6, 11, 2, 4, 0] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 4] :=
    overlap torus2388 torus1559 [3, 1, 7, 0, 4, 1, 8] [2, 4, 0] (by decide)
  have hl : V [1, 8, 6, 11, 2, 4, 0] = V [11] :=
    ((in_context torus47 [1, 8, 6] [4, 0]).trans ((in_context torus6 [1, 8] [11, 4, 0]).trans ((in_context torus59 [1, 8] [0]).trans ((in_context torus8 [1] [11, 0]).trans ((in_context torus91 [1] []).trans (in_context torus1 [] [11]))))))
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 4] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2390 : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] = V [8, 11] := by
  have h0 : V [11, 4] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] :=
    overlap torus2389 torus4 [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] [4] (by decide)
  have hl : V [11, 4] = V [8, 11] :=
    (in_context torus59 [] [])
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2391 : V [3, 1, 7, 0, 4, 1, 8, 0, 3] = V [8, 2, 11] := by
  have h0 : V [8, 11, 5] = V [3, 1, 7, 0, 4, 1, 8, 0, 3] :=
    overlap torus2390 torus5 [3, 1, 7, 0, 4, 1, 8, 0, 3] [5] (by decide)
  have hl : V [8, 11, 5] = V [8, 2, 11] :=
    (in_context torus65 [8] [])
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 3] = V [3, 1, 7, 0, 4, 1, 8, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2395 : V [6, 1, 3, 5, 4, 6, 4, 0] = V [4, 6, 5, 7] := by
  have h0 : V [4, 6, 7, 2, 0, 1, 2, 7, 5, 7] = V [6, 1, 3, 5, 4, 6, 4, 0] :=
    overlap torus1968 torus2108 [6, 1, 3, 5] [1, 2, 7, 5, 7] (by decide)
  have hl : V [4, 6, 7, 2, 0, 1, 2, 7, 5, 7] = V [4, 6, 5, 7] :=
    ((in_context torus0 [4, 6, 7, 2] [2, 7, 5, 7]).trans ((in_context torus2 [4, 6, 7] [7, 5, 7]).trans (in_context torus7 [4, 6] [5, 7])))
  have hr : V [6, 1, 3, 5, 4, 6, 4, 0] = V [6, 1, 3, 5, 4, 6, 4, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2396 : V [7, 1, 4, 6, 5, 7, 5, 0] = V [5, 7, 6, 8] := by
  have h0 : V [5, 7, 8, 3, 0, 1, 3, 8, 6, 8] = V [7, 1, 4, 6, 5, 7, 5, 0] :=
    overlap torus2075 torus2114 [7, 1, 4, 6] [1, 3, 8, 6, 8] (by decide)
  have hl : V [5, 7, 8, 3, 0, 1, 3, 8, 6, 8] = V [5, 7, 6, 8] :=
    ((in_context torus0 [5, 7, 8, 3] [3, 8, 6, 8]).trans ((in_context torus3 [5, 7, 8] [8, 6, 8]).trans (in_context torus8 [5, 7] [6, 8])))
  have hr : V [7, 1, 4, 6, 5, 7, 5, 0] = V [7, 1, 4, 6, 5, 7, 5, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2399 : V [6, 0, 2, 7, 8, 6, 8, 1] = V [8, 6, 7, 5] := by
  have h0 : V [8, 6, 5, 4, 3, 3, 4, 5, 7, 5] = V [6, 2, 8, 2, 3, 7, 8, 6, 8, 1] :=
    overlap torus267 torus2118 [6, 2, 8, 2, 3, 7] [3, 4, 5, 7, 5] (by decide)
  have hl : V [8, 6, 5, 4, 3, 3, 4, 5, 7, 5] = V [8, 6, 7, 5] :=
    ((in_context torus1462 [8] [3, 3, 4, 5, 7, 5]).trans ((in_context torus1758 [] [3, 4, 5, 7, 5]).trans ((in_context torus1638 [6] [7, 5]).trans (in_context torus6 [] [8, 6, 7, 5]))))
  have hr : V [6, 2, 8, 2, 3, 7, 8, 6, 8, 1] = V [6, 0, 2, 7, 8, 6, 8, 1] :=
    ((in_context torus1428 [6] [3, 7, 8, 6, 8, 1]).trans (in_context torus3 [6, 0, 2] [7, 8, 6, 8, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2401 : V [3, 0, 6, 1, 4, 8, 3, 1] = V [5, 2, 1, 7] := by
  have h0 : V [5, 2, 1, 2, 2, 7] = V [3, 0, 6, 1, 4, 8, 3, 1] :=
    overlap torus2132 torus2089 [3, 0, 6] [2, 7] (by decide)
  have hl : V [5, 2, 1, 2, 2, 7] = V [5, 2, 1, 7] :=
    (in_context torus2 [5, 2, 1] [7])
  have hr : V [3, 0, 6, 1, 4, 8, 3, 1] = V [3, 0, 6, 1, 4, 8, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2404 : V [6, 4, 6, 1, 3, 4, 1, 4] = V [7, 8, 3, 0] := by
  have h0 : V [7, 2, 0, 2, 4, 3] = V [6, 4, 6, 1, 3, 4, 1, 4] :=
    overlap torus2141 torus1453 [6, 4, 6, 1, 3] [4, 3] (by decide)
  have hl : V [7, 2, 0, 2, 4, 3] = V [7, 8, 3, 0] :=
    ((in_context torus1863 [] [3]).trans ((in_context torus2075 [5] []).trans (in_context torus5 [] [7, 8, 3, 0])))
  have hr : V [6, 4, 6, 1, 3, 4, 1, 4] = V [6, 4, 6, 1, 3, 4, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2406 : V [2, 0, 5, 1, 8, 0, 4, 2] = V [0, 4, 6, 12] := by
  have h0 : V [4, 2, 8, 7, 7, 8, 2, 3, 4, 5, 6, 12] = V [2, 0, 5, 3, 5, 5, 4, 3, 2, 8, 7, 6, 5, 4] :=
    overlap torus2146 torus1409 [2, 0, 5, 3, 5] [7, 8, 2, 3, 4, 5, 6, 12] (by decide)
  have hl : V [4, 2, 8, 7, 7, 8, 2, 3, 4, 5, 6, 12] = V [0, 4, 6, 12] :=
    ((in_context torus7 [4, 2, 8] [8, 2, 3, 4, 5, 6, 12]).trans ((in_context torus8 [4, 2] [2, 3, 4, 5, 6, 12]).trans ((in_context torus2 [4] [3, 4, 5, 6, 12]).trans ((in_context torus1448 [] [5, 6, 12]).trans (in_context torus5 [0, 4] [6, 12])))))
  have hr : V [2, 0, 5, 3, 5, 5, 4, 3, 2, 8, 7, 6, 5, 4] = V [2, 0, 5, 1, 8, 0, 4, 2] :=
    ((in_context torus5 [2, 0, 5, 3] [4, 3, 2, 8, 7, 6, 5, 4]).trans ((in_context torus1442 [2, 0, 5] [2, 8, 7, 6, 5, 4]).trans ((in_context torus1446 [2, 0, 5] [2, 8, 7, 6, 5, 4]).trans ((in_context torus2 [2, 0, 5, 1, 3] [8, 7, 6, 5, 4]).trans ((in_context torus1480 [2, 0, 5, 1, 3] [5, 4]).trans ((in_context torus1989 [2, 0, 5, 1, 3] []).trans (in_context torus3 [2, 0, 5, 1] [8, 0, 4, 2])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2407 : V [2, 0, 5, 1, 3, 7, 2, 1] = V [4, 8, 1, 6] := by
  have h0 : V [4, 2, 8, 7, 8, 6] = V [2, 0, 5, 1, 3, 7, 2, 1] :=
    overlap torus2146 torus2083 [2, 0, 5] [8, 6] (by decide)
  have hl : V [4, 2, 8, 7, 8, 6] = V [4, 8, 1, 6] :=
    ((in_context torus1484 [4, 2] [6]).trans (in_context torus1491 [4] [6]))
  have hr : V [2, 0, 5, 1, 3, 7, 2, 1] = V [2, 0, 5, 1, 3, 7, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2408 : V [4, 0, 7, 1, 3, 0, 6, 4] = V [0, 6, 8, 12] := by
  have h0 : V [6, 3, 1, 3, 2, 3, 4, 5, 6, 7, 8, 12] = V [4, 0, 7, 5, 7, 7, 6, 5, 4, 3, 2, 8, 7, 6] :=
    overlap torus2151 torus1405 [4, 0, 7, 5, 7] [2, 3, 4, 5, 6, 7, 8, 12] (by decide)
  have hl : V [6, 3, 1, 3, 2, 3, 4, 5, 6, 7, 8, 12] = V [0, 6, 8, 12] :=
    ((in_context torus1445 [6] [3, 4, 5, 6, 7, 8, 12]).trans ((in_context torus3 [6, 4] [4, 5, 6, 7, 8, 12]).trans ((in_context torus4 [6] [5, 6, 7, 8, 12]).trans ((in_context torus1466 [] [7, 8, 12]).trans (in_context torus7 [0, 6] [8, 12])))))
  have hr : V [4, 0, 7, 5, 7, 7, 6, 5, 4, 3, 2, 8, 7, 6] = V [4, 0, 7, 1, 3, 0, 6, 4] :=
    ((in_context torus7 [4, 0, 7, 5] [6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1460 [4, 0, 7] [4, 3, 2, 8, 7, 6]).trans ((in_context torus1464 [4, 0, 7] [4, 3, 2, 8, 7, 6]).trans ((in_context torus4 [4, 0, 7, 1, 5] [3, 2, 8, 7, 6]).trans ((in_context torus206 [4, 0, 7, 1] []).trans ((in_context torus1466 [4, 0, 7, 1, 3] [7, 4]).trans (in_context torus7 [4, 0, 7, 1, 3, 0, 6] [4])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2409 : V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2, 3] = V [12] := by
  have h0 : V [0, 6, 8, 12, 5, 3, 1] = V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2, 3] :=
    overlap torus2408 torus1594 [4, 0, 7, 1, 3, 0, 6] [5, 3, 1] (by decide)
  have hl : V [0, 6, 8, 12, 5, 3, 1] = V [12] :=
    ((in_context torus66 [0, 6, 8] [3, 1]).trans ((in_context torus8 [0, 6] [12, 3, 1]).trans ((in_context torus54 [0, 6] [1]).trans ((in_context torus6 [0] [12, 1]).trans ((in_context torus94 [0] []).trans (in_context torus0 [] [12]))))))
  have hr : V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2, 3] = V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2410 : V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2] = V [6, 12] := by
  have h0 : V [12, 3] = V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2] :=
    overlap torus2409 torus3 [4, 0, 7, 1, 3, 0, 6, 1, 4, 2] [3] (by decide)
  have hl : V [12, 3] = V [6, 12] :=
    (in_context torus54 [] [])
  have hr : V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2] = V [4, 0, 7, 1, 3, 0, 6, 1, 4, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2411 : V [4, 0, 7, 1, 3, 0, 6, 1, 4] = V [6, 5, 12] := by
  have h0 : V [12, 5, 3, 0, 6, 4, 6, 7, 8] = V [4, 0, 7, 1, 3, 0, 6, 1, 4] :=
    overlap torus2409 torus1851 [4, 0, 7, 1, 3, 0, 6, 1, 4] [5, 3, 0, 6, 4, 6, 7, 8] (by decide)
  have hl : V [12, 5, 3, 0, 6, 4, 6, 7, 8] = V [6, 5, 12] :=
    ((in_context torus66 [] [3, 0, 6, 4, 6, 7, 8]).trans ((in_context torus54 [8] [0, 6, 4, 6, 7, 8]).trans ((in_context torus93 [8, 6] [6, 4, 6, 7, 8]).trans ((in_context torus72 [8, 6, 0] [4, 6, 7, 8]).trans ((in_context torus60 [8, 6, 0, 2] [6, 7, 8]).trans ((in_context torus1981 [] [12, 6, 7, 8]).trans ((in_context torus72 [5, 1, 5, 3, 2] [7, 8]).trans ((in_context torus2 [5, 1, 5, 3] [12, 7, 8]).trans ((in_context torus78 [5, 1, 5, 3] [8]).trans ((in_context torus3 [5, 1, 5] [12, 8]).trans ((in_context torus84 [5, 1, 5] []).trans (in_context torus1463 [] [12]))))))))))))
  have hr : V [4, 0, 7, 1, 3, 0, 6, 1, 4] = V [4, 0, 7, 1, 3, 0, 6, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2412 : V [4, 0, 7, 1, 5, 2, 4, 1] = V [6, 3, 1, 8] := by
  have h0 : V [6, 3, 1, 3, 3, 8] = V [4, 0, 7, 1, 5, 2, 4, 1] :=
    overlap torus2151 torus2068 [4, 0, 7] [3, 8] (by decide)
  have hl : V [6, 3, 1, 3, 3, 8] = V [6, 3, 1, 8] :=
    (in_context torus3 [6, 3, 1] [8])
  have hr : V [4, 0, 7, 1, 5, 2, 4, 1] = V [4, 0, 7, 1, 5, 2, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2413 : V [0, 3, 4, 1, 2, 8, 0, 3] = V [1, 2, 8, 4] := by
  have h0 : V [1, 2, 8, 4] = V [0, 3, 4, 1, 2, 8, 0, 3] :=
    overlap torus2156 torus4 [0, 3, 4, 1, 2, 8, 0, 3] [4] (by decide)
  have hl : V [1, 2, 8, 4] = V [1, 2, 8, 4] :=
    rfl
  have hr : V [0, 3, 4, 1, 2, 8, 0, 3] = V [0, 3, 4, 1, 2, 8, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2422 : V [0, 5, 6, 1, 4, 3, 5, 1] = V [4, 5, 3, 4] := by
  have h0 : V [1, 4, 3, 0, 4, 5] = V [0, 5, 6, 1, 4, 3, 0, 5, 5, 1, 5, 1] :=
    overlap torus2162 torus1567 [0, 5, 6, 1, 4, 3, 0, 5] [0, 4, 5] (by decide)
  have hl : V [1, 4, 3, 0, 4, 5] = V [4, 5, 3, 4] :=
    ((in_context torus1550 [1, 4] []).trans ((in_context torus1554 [1] [4]).trans (in_context torus1 [] [4, 5, 3, 4])))
  have hr : V [0, 5, 6, 1, 4, 3, 0, 5, 5, 1, 5, 1] = V [0, 5, 6, 1, 4, 3, 5, 1] :=
    ((in_context torus5 [0, 5, 6, 1, 4, 3, 0] [1, 5, 1]).trans (in_context torus0 [0, 5, 6, 1, 4, 3] [5, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2429 : V [0, 7, 8, 1, 6, 5, 0, 7] = V [1, 6, 5, 8] := by
  have h0 : V [1, 6, 5, 8] = V [0, 7, 8, 1, 6, 5, 0, 7] :=
    overlap torus2168 torus8 [0, 7, 8, 1, 6, 5, 0, 7] [8] (by decide)
  have hl : V [1, 6, 5, 8] = V [1, 6, 5, 8] :=
    rfl
  have hr : V [0, 7, 8, 1, 6, 5, 0, 7] = V [0, 7, 8, 1, 6, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2430 : V [0, 7, 8, 1, 6, 5, 7, 1] = V [6, 7, 5, 6] := by
  have h0 : V [1, 6, 5, 0, 6, 7] = V [0, 7, 8, 1, 6, 5, 0, 7, 7, 1, 7, 1] :=
    overlap torus2168 torus1583 [0, 7, 8, 1, 6, 5, 0, 7] [0, 6, 7] (by decide)
  have hl : V [1, 6, 5, 0, 6, 7] = V [6, 7, 5, 6] :=
    ((in_context torus1566 [1, 6] []).trans ((in_context torus1569 [1] [6]).trans (in_context torus1 [] [6, 7, 5, 6])))
  have hr : V [0, 7, 8, 1, 6, 5, 0, 7, 7, 1, 7, 1] = V [0, 7, 8, 1, 6, 5, 7, 1] :=
    ((in_context torus7 [0, 7, 8, 1, 6, 5, 0] [1, 7, 1]).trans (in_context torus0 [0, 7, 8, 1, 6, 5] [7, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2432 : V [0, 7, 8, 1, 6, 5, 8, 7] = V [1, 6, 5, 0] := by
  have h0 : V [1, 6, 5, 0] = V [0, 7, 8, 1, 6, 5, 0, 1, 8, 7] :=
    overlap torus2168 torus1490 [0, 7, 8, 1, 6, 5, 0] [0] (by decide)
  have hl : V [1, 6, 5, 0] = V [1, 6, 5, 0] :=
    rfl
  have hr : V [0, 7, 8, 1, 6, 5, 0, 1, 8, 7] = V [0, 7, 8, 1, 6, 5, 8, 7] :=
    (in_context torus0 [0, 7, 8, 1, 6, 5] [8, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2433 : V [0, 8, 2, 1, 7, 6, 0, 8] = V [1, 7, 6, 2] := by
  have h0 : V [1, 7, 6, 2] = V [0, 8, 2, 1, 7, 6, 0, 8] :=
    overlap torus2171 torus2 [0, 8, 2, 1, 7, 6, 0, 8] [2] (by decide)
  have hl : V [1, 7, 6, 2] = V [1, 7, 6, 2] :=
    rfl
  have hr : V [0, 8, 2, 1, 7, 6, 0, 8] = V [0, 8, 2, 1, 7, 6, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2435 : V [7, 0, 4, 1, 8, 3, 2, 12] = V [0, 3, 1, 8] := by
  have h0 : V [7, 2, 7, 6, 5, 4, 3, 2, 8, 7] = V [0, 8, 2, 1, 7, 6, 8, 7, 0, 2, 3, 4, 5, 6, 7, 8, 2, 12] :=
    overlap torus2173 torus1404 [0, 8, 2, 1, 7, 6, 8, 7, 0] [7, 6, 5, 4, 3, 2, 8, 7] (by decide)
  have hl : V [7, 2, 7, 6, 5, 4, 3, 2, 8, 7] = V [0, 3, 1, 8] :=
    ((in_context torus285 [] [3, 2, 8, 7]).trans ((in_context torus1439 [] [4, 8, 3, 3, 2, 8, 7]).trans ((in_context torus4 [0, 3] [8, 3, 3, 2, 8, 7]).trans ((in_context torus3 [0, 3, 8] [2, 8, 7]).trans ((in_context torus1487 [0, 3] [7]).trans ((in_context torus1490 [0, 3] [7]).trans (in_context torus7 [0, 3, 1, 8] [])))))))
  have hr : V [0, 8, 2, 1, 7, 6, 8, 7, 0, 2, 3, 4, 5, 6, 7, 8, 2, 12] = V [7, 0, 4, 1, 8, 3, 2, 12] :=
    ((in_context torus1805 [0, 8, 2, 1, 7, 6, 8, 7, 0, 2, 3] [2, 12]).trans ((in_context torus1433 [0, 8, 2, 1, 7, 6, 8, 7] [4, 1, 8, 3, 2, 12]).trans (in_context torus2172 [] [4, 1, 8, 3, 2, 12])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2436 : V [7, 0, 4, 1, 8, 3, 2, 4, 12] = V [0, 3, 1] := by
  have h0 : V [0, 3, 1, 8, 8] = V [7, 0, 4, 1, 8, 3, 2, 4, 12] :=
    overlap torus2435 torus84 [7, 0, 4, 1, 8, 3, 2] [8] (by decide)
  have hl : V [0, 3, 1, 8, 8] = V [0, 3, 1] :=
    (in_context torus8 [0, 3, 1] [])
  have hr : V [7, 0, 4, 1, 8, 3, 2, 4, 12] = V [7, 0, 4, 1, 8, 3, 2, 4, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2437 : V [7, 0, 4, 1, 8, 0, 3, 5, 4, 12] = V [0, 3] := by
  have h0 : V [0, 3, 1, 0] = V [7, 0, 4, 1, 8, 3, 2, 4, 0, 12] :=
    overlap torus2436 torus93 [7, 0, 4, 1, 8, 3, 2, 4] [0] (by decide)
  have hl : V [0, 3, 1, 0] = V [0, 3] :=
    (in_context torus1 [0, 3] [])
  have hr : V [7, 0, 4, 1, 8, 3, 2, 4, 0, 12] = V [7, 0, 4, 1, 8, 0, 3, 5, 4, 12] :=
    (in_context torus1559 [7, 0, 4, 1, 8] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2442 : V [7, 0, 4, 1, 8, 0, 3, 5, 12] = V [0, 3, 8] := by
  have h0 : V [0, 3, 8] = V [7, 0, 4, 1, 8, 0, 3, 5, 4, 4, 12] :=
    overlap torus2437 torus84 [7, 0, 4, 1, 8, 0, 3, 5, 4] [8] (by decide)
  have hl : V [0, 3, 8] = V [0, 3, 8] :=
    rfl
  have hr : V [7, 0, 4, 1, 8, 0, 3, 5, 4, 4, 12] = V [7, 0, 4, 1, 8, 0, 3, 5, 12] :=
    (in_context torus4 [7, 0, 4, 1, 8, 0, 3, 5] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2443 : V [1, 8, 7, 0, 2, 3, 1, 8] = V [0, 2, 3, 7] := by
  have h0 : V [0, 2, 3, 7] = V [1, 8, 7, 0, 2, 3, 1, 8] :=
    overlap torus2174 torus7 [1, 8, 7, 0, 2, 3, 1, 8] [7] (by decide)
  have hl : V [0, 2, 3, 7] = V [0, 2, 3, 7] :=
    rfl
  have hr : V [1, 8, 7, 0, 2, 3, 1, 8] = V [1, 8, 7, 0, 2, 3, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2446 : V [7, 0, 3, 1, 8, 6, 7, 5] = V [0, 4, 1, 12] := by
  have h0 : V [0, 2, 12, 6, 2, 8, 7, 8] = V [7, 0, 3, 1, 6, 0, 2, 7, 2, 3, 4, 5, 7, 5] :=
    overlap torus2178 torus235 [7, 0, 3, 1, 6, 0, 2, 7] [6, 2, 8, 7, 8] (by decide)
  have hl : V [0, 2, 12, 6, 2, 8, 7, 8] = V [0, 4, 1, 12] :=
    ((in_context torus72 [0, 2] [2, 8, 7, 8]).trans ((in_context torus2 [0] [12, 2, 8, 7, 8]).trans ((in_context torus48 [0] [8, 7, 8]).trans ((in_context torus84 [0, 5] [7, 8]).trans ((in_context torus78 [0, 5, 4] [8]).trans ((in_context torus1453 [0] [12, 8]).trans ((in_context torus84 [0, 4, 1, 4] []).trans (in_context torus4 [0, 4, 1] [12]))))))))
  have hr : V [7, 0, 3, 1, 6, 0, 2, 7, 2, 3, 4, 5, 7, 5] = V [7, 0, 3, 1, 8, 6, 7, 5] :=
    ((in_context torus2133 [7, 0, 3, 1] [4, 5, 7, 5]).trans ((in_context torus1463 [7, 0, 3, 1, 8] [5, 7, 5]).trans (in_context torus5 [7, 0, 3, 1, 8, 6] [7, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2449 : V [5, 0, 8, 1, 4, 0, 7, 1] = V [7, 6, 8, 12] := by
  have h0 : V [0, 7, 12, 0, 5, 6] = V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1] :=
    overlap torus2188 torus1497 [5, 0, 8, 1, 4, 0, 7, 5] [0, 5, 6] (by decide)
  have hl : V [0, 7, 12, 0, 5, 6] = V [7, 6, 8, 12] :=
    ((in_context torus93 [0, 7] [5, 6]).trans ((in_context torus66 [0, 7, 0] [6]).trans ((in_context torus72 [0, 7, 0, 8] []).trans ((in_context torus1582 [0] [12]).trans (in_context torus0 [] [7, 6, 8, 12])))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 5, 5, 1] = V [5, 0, 8, 1, 4, 0, 7, 1] :=
    (in_context torus5 [5, 0, 8, 1, 4, 0, 7] [1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2451 : V [4, 6, 1, 3, 0, 5, 8, 6] = V [7, 0, 2, 1] := by
  have h0 : V [7, 0, 2, 1] = V [4, 6, 1, 3, 0, 5, 8, 6] :=
    overlap torus2193 torus0 [4, 6, 1, 3, 0, 5, 8, 6] [1] (by decide)
  have hl : V [7, 0, 2, 1] = V [7, 0, 2, 1] :=
    rfl
  have hr : V [4, 6, 1, 3, 0, 5, 8, 6] = V [4, 6, 1, 3, 0, 5, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2454 : V [4, 1, 8, 3, 2, 4, 2, 0] = V [2, 4, 3, 5] := by
  have h0 : V [2, 4, 3, 5] = V [4, 1, 8, 3, 2, 4, 2, 0] :=
    overlap torus2202 torus5 [4, 1, 8, 3, 2, 4, 2, 0] [5] (by decide)
  have hl : V [2, 4, 3, 5] = V [2, 4, 3, 5] :=
    rfl
  have hr : V [4, 1, 8, 3, 2, 4, 2, 0] = V [4, 1, 8, 3, 2, 4, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2457 : V [4, 1, 8, 0, 5, 1, 2, 0] = V [2, 3, 8, 11] := by
  have h0 : V [1, 2, 11, 4, 5, 4] = V [4, 1, 8, 0, 5, 1, 2, 4, 4, 0] :=
    overlap torus2217 torus1450 [4, 1, 8, 0, 5, 1, 2, 4] [4, 5, 4] (by decide)
  have hl : V [1, 2, 11, 4, 5, 4] = V [2, 3, 8, 11] :=
    ((in_context torus59 [1, 2] [5, 4]).trans ((in_context torus65 [1, 2, 8] [4]).trans ((in_context torus1428 [1] [11, 4]).trans ((in_context torus1 [] [2, 3, 11, 4]).trans (in_context torus59 [2, 3] [])))))
  have hr : V [4, 1, 8, 0, 5, 1, 2, 4, 4, 0] = V [4, 1, 8, 0, 5, 1, 2, 0] :=
    (in_context torus4 [4, 1, 8, 0, 5, 1, 2] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2461 : V [0, 8, 2, 1, 7, 6, 8, 6] = V [7, 8, 1, 7] := by
  have h0 : V [7, 8, 1, 7] = V [0, 8, 2, 1, 7, 6, 8, 6] :=
    overlap torus2252 torus7 [0, 8, 2, 1, 7, 6, 8, 6] [7] (by decide)
  have hl : V [7, 8, 1, 7] = V [7, 8, 1, 7] :=
    rfl
  have hr : V [0, 8, 2, 1, 7, 6, 8, 6] = V [0, 8, 2, 1, 7, 6, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2465 : V [4, 1, 8, 0, 3, 5, 4, 6] = V [1, 7, 0, 11] := by
  have h0 : V [1, 2, 11, 5, 3, 0] = V [4, 1, 8, 0, 3, 5, 4, 6] :=
    overlap torus2217 torus2330 [4, 1, 8, 0] [5, 3, 0] (by decide)
  have hl : V [1, 2, 11, 5, 3, 0] = V [1, 7, 0, 11] :=
    ((in_context torus65 [1, 2] [3, 0]).trans ((in_context torus2 [1] [11, 3, 0]).trans ((in_context torus53 [1] [0]).trans (in_context torus91 [1, 7] []))))
  have hr : V [4, 1, 8, 0, 3, 5, 4, 6] = V [4, 1, 8, 0, 3, 5, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2466 : V [0, 5, 1, 3, 8, 2, 7, 0, 11] = V [2, 0, 6] := by
  have h0 : V [2, 4, 2, 3, 0, 3, 5, 4, 6] = V [0, 5, 3, 4, 2, 1, 7, 0, 11] :=
    overlap torus2358 torus2465 [0, 5, 3, 4, 2] [0, 3, 5, 4, 6] (by decide)
  have hl : V [2, 4, 2, 3, 0, 3, 5, 4, 6] = V [2, 0, 6] :=
    ((in_context torus1446 [2, 4] [3, 5, 4, 6]).trans ((in_context torus1554 [2] [3, 5, 4, 6]).trans ((in_context torus3 [2, 0, 4, 5] [5, 4, 6]).trans ((in_context torus5 [2, 0, 4] [4, 6]).trans (in_context torus4 [2, 0] [6])))))
  have hr : V [0, 5, 3, 4, 2, 1, 7, 0, 11] = V [0, 5, 1, 3, 8, 2, 7, 0, 11] :=
    (in_context torus1592 [0, 5] [7, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2467 : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 11] = V [2, 0] := by
  have h0 : V [2, 0, 6, 6] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 11] :=
    overlap torus2466 torus71 [0, 5, 1, 3, 8, 2, 7, 0] [6] (by decide)
  have hl : V [2, 0, 6, 6] = V [2, 0] :=
    (in_context torus6 [2, 0] [])
  have hr : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 11] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2468 : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1, 11] = V [2] := by
  have h0 : V [2, 0, 1] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1, 11] :=
    overlap torus2467 torus92 [0, 5, 1, 3, 8, 2, 7, 0, 3] [1] (by decide)
  have hl : V [2, 0, 1] = V [2] :=
    (in_context torus0 [2] [])
  have hr : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1, 11] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2471 : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1] = V [2, 12] := by
  have h0 : V [2, 12] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1] :=
    overlap torus2468 torus24 [0, 5, 1, 3, 8, 2, 7, 0, 3, 1] [12] (by decide)
  have hl : V [2, 12] = V [2, 12] :=
    rfl
  have hr : V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1] = V [0, 5, 1, 3, 8, 2, 7, 0, 3, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2472 : V [0, 5, 1, 3, 8, 2, 7, 0, 3] = V [2, 0, 12] := by
  have h0 : V [2, 0, 12] = V [0, 5, 1, 3, 8, 2, 7, 0, 3] :=
    overlap torus2467 torus24 [0, 5, 1, 3, 8, 2, 7, 0, 3] [12] (by decide)
  have hl : V [2, 0, 12] = V [2, 0, 12] :=
    rfl
  have hr : V [0, 5, 1, 3, 8, 2, 7, 0, 3] = V [0, 5, 1, 3, 8, 2, 7, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2475 : V [7, 1, 4, 0, 8, 1, 5, 0] = V [5, 6, 4, 11] := by
  have h0 : V [1, 5, 3, 11, 6, 7, 8, 7] = V [7, 1, 4, 0, 8, 1, 5, 3, 2, 3, 4, 3] :=
    overlap torus2364 torus126 [7, 1, 4, 0, 8, 1, 5] [6, 7, 8, 7] (by decide)
  have hl : V [1, 5, 3, 11, 6, 7, 8, 7] = V [5, 6, 4, 11] :=
    ((in_context torus71 [1, 5, 3] [7, 8, 7]).trans ((in_context torus3 [1, 5] [11, 7, 8, 7]).trans ((in_context torus77 [1, 5] [8, 7]).trans ((in_context torus83 [1, 5, 4] [7]).trans ((in_context torus1457 [1] [11, 7]).trans ((in_context torus1 [] [5, 6, 11, 7]).trans (in_context torus77 [5, 6] [])))))))
  have hr : V [7, 1, 4, 0, 8, 1, 5, 3, 2, 3, 4, 3] = V [7, 1, 4, 0, 8, 1, 5, 0] :=
    ((in_context torus143 [7, 1, 4, 0, 8, 1, 5] []).trans ((in_context torus1428 [7, 1, 4, 0, 8, 1, 5] [3, 2]).trans ((in_context torus3 [7, 1, 4, 0, 8, 1, 5, 0, 2] [2]).trans (in_context torus2 [7, 1, 4, 0, 8, 1, 5, 0] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2476 : V [2, 1, 6, 0, 3, 1, 7, 0] = V [7, 8, 6, 11] := by
  have h0 : V [7, 8, 11, 2] = V [2, 1, 6, 0, 3, 1, 7, 0] :=
    overlap torus2384 torus2 [2, 1, 6, 0, 3, 1, 7, 0] [2] (by decide)
  have hl : V [7, 8, 11, 2] = V [7, 8, 6, 11] :=
    (in_context torus47 [7, 8] [])
  have hr : V [2, 1, 6, 0, 3, 1, 7, 0] = V [2, 1, 6, 0, 3, 1, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2477 : V [3, 1, 7, 0, 4, 1, 8, 0] = V [8, 2, 7, 11] := by
  have h0 : V [1, 8, 6, 11, 2, 3, 4, 3] = V [3, 1, 7, 0, 4, 1, 8, 2, 8, 2, 3, 2] :=
    overlap torus2388 torus143 [3, 1, 7, 0, 4, 1, 8] [2, 3, 4, 3] (by decide)
  have hl : V [1, 8, 6, 11, 2, 3, 4, 3] = V [8, 2, 7, 11] :=
    ((in_context torus47 [1, 8, 6] [3, 4, 3]).trans ((in_context torus6 [1, 8] [11, 3, 4, 3]).trans ((in_context torus53 [1, 8] [4, 3]).trans ((in_context torus59 [1, 8, 7] [3]).trans ((in_context torus1484 [1] [11, 3]).trans ((in_context torus1 [] [8, 2, 11, 3]).trans (in_context torus53 [8, 2] [])))))))
  have hr : V [3, 1, 7, 0, 4, 1, 8, 2, 8, 2, 3, 2] = V [3, 1, 7, 0, 4, 1, 8, 0] :=
    ((in_context torus142 [3, 1, 7, 0, 4, 1] [2]).trans ((in_context torus1486 [3, 1, 7, 0, 4, 1] [2, 2]).trans (in_context torus2 [3, 1, 7, 0, 4, 1, 8, 0] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2478 : V [5, 1, 2, 0, 4, 6, 5, 7] = V [1, 8, 0, 11] := by
  have h0 : V [1, 3, 8, 11, 4, 6, 4, 0] = V [5, 1, 2, 0, 4, 6, 5, 7] :=
    overlap torus2350 torus2395 [5, 1, 2, 0] [4, 6, 4, 0] (by decide)
  have hl : V [1, 3, 8, 11, 4, 6, 4, 0] = V [1, 8, 0, 11] :=
    ((in_context torus59 [1, 3, 8] [6, 4, 0]).trans ((in_context torus8 [1, 3] [11, 6, 4, 0]).trans ((in_context torus71 [1, 3] [4, 0]).trans ((in_context torus3 [1] [11, 4, 0]).trans ((in_context torus59 [1] [0]).trans (in_context torus91 [1, 8] []))))))
  have hr : V [5, 1, 2, 0, 4, 6, 5, 7] = V [5, 1, 2, 0, 4, 6, 5, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2479 : V [0, 6, 1, 4, 2, 3, 8, 0, 11] = V [3, 0, 7] := by
  have h0 : V [3, 5, 3, 4, 0, 4, 6, 5, 7] = V [0, 6, 4, 5, 3, 1, 8, 0, 11] :=
    overlap torus2328 torus2478 [0, 6, 4, 5, 3] [0, 4, 6, 5, 7] (by decide)
  have hl : V [3, 5, 3, 4, 0, 4, 6, 5, 7] = V [3, 0, 7] :=
    ((in_context torus1455 [3, 5] [4, 6, 5, 7]).trans ((in_context torus1546 [3] [4, 6, 5, 7]).trans ((in_context torus4 [3, 0, 5, 6] [6, 5, 7]).trans ((in_context torus6 [3, 0, 5] [5, 7]).trans (in_context torus5 [3, 0] [7])))))
  have hr : V [0, 6, 4, 5, 3, 1, 8, 0, 11] = V [0, 6, 1, 4, 2, 3, 8, 0, 11] :=
    (in_context torus1594 [0, 6] [8, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2480 : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 11] = V [3, 0] := by
  have h0 : V [3, 0, 7, 7] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 11] :=
    overlap torus2479 torus77 [0, 6, 1, 4, 2, 3, 8, 0] [7] (by decide)
  have hl : V [3, 0, 7, 7] = V [3, 0] :=
    (in_context torus7 [3, 0] [])
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 11] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2481 : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 11] = V [3] := by
  have h0 : V [3, 0, 1] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 11] :=
    overlap torus2480 torus92 [0, 6, 1, 4, 2, 3, 8, 0, 4] [1] (by decide)
  have hl : V [3, 0, 1] = V [3] :=
    (in_context torus0 [3] [])
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 11] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2482 : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 7, 11] = V [] := by
  have h0 : V [3, 3] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 7, 11] :=
    overlap torus2481 torus53 [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] [3] (by decide)
  have hl : V [3, 3] = V [] :=
    (in_context torus3 [] [])
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 7, 11] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1, 7, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2484 : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] = V [3, 12] := by
  have h0 : V [3, 12] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] :=
    overlap torus2481 torus24 [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] [12] (by decide)
  have hl : V [3, 12] = V [3, 12] :=
    rfl
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] = V [0, 6, 1, 4, 2, 3, 8, 0, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2485 : V [0, 6, 1, 4, 2, 3, 8, 0, 4] = V [3, 0, 12] := by
  have h0 : V [3, 0, 12] = V [0, 6, 1, 4, 2, 3, 8, 0, 4] :=
    overlap torus2480 torus24 [0, 6, 1, 4, 2, 3, 8, 0, 4] [12] (by decide)
  have hl : V [3, 0, 12] = V [3, 0, 12] :=
    rfl
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 4] = V [0, 6, 1, 4, 2, 3, 8, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2486 : V [6, 1, 3, 0, 5, 7, 6, 8] = V [1, 2, 0, 11] := by
  have h0 : V [1, 4, 2, 11, 5, 7, 5, 0] = V [6, 1, 3, 0, 5, 7, 6, 8] :=
    overlap torus2360 torus2396 [6, 1, 3, 0] [5, 7, 5, 0] (by decide)
  have hl : V [1, 4, 2, 11, 5, 7, 5, 0] = V [1, 2, 0, 11] :=
    ((in_context torus65 [1, 4, 2] [7, 5, 0]).trans ((in_context torus2 [1, 4] [11, 7, 5, 0]).trans ((in_context torus77 [1, 4] [5, 0]).trans ((in_context torus4 [1] [11, 5, 0]).trans ((in_context torus65 [1] [0]).trans (in_context torus91 [1, 2] []))))))
  have hr : V [6, 1, 3, 0, 5, 7, 6, 8] = V [6, 1, 3, 0, 5, 7, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2492 : V [0, 7, 1, 5, 3, 4, 2, 0, 11] = V [4, 0, 8] := by
  have h0 : V [4, 6, 4, 5, 0, 5, 7, 6, 8] = V [0, 7, 5, 6, 4, 1, 2, 0, 11] :=
    overlap torus2329 torus2486 [0, 7, 5, 6, 4] [0, 5, 7, 6, 8] (by decide)
  have hl : V [4, 6, 4, 5, 0, 5, 7, 6, 8] = V [4, 0, 8] :=
    ((in_context torus1464 [4, 6] [5, 7, 6, 8]).trans ((in_context torus1569 [4] [5, 7, 6, 8]).trans ((in_context torus5 [4, 0, 6, 7] [7, 6, 8]).trans ((in_context torus7 [4, 0, 6] [6, 8]).trans (in_context torus6 [4, 0] [8])))))
  have hr : V [0, 7, 5, 6, 4, 1, 2, 0, 11] = V [0, 7, 1, 5, 3, 4, 2, 0, 11] :=
    (in_context torus1595 [0, 7] [2, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2495 : V [7, 0, 4, 1, 8, 3, 2, 4] = V [0, 3, 1, 11] := by
  have h0 : V [0, 3, 1, 11] = V [7, 0, 4, 1, 8, 3, 2, 4] :=
    overlap torus2436 torus29 [7, 0, 4, 1, 8, 3, 2, 4] [11] (by decide)
  have hl : V [0, 3, 1, 11] = V [0, 3, 1, 11] :=
    rfl
  have hr : V [7, 0, 4, 1, 8, 3, 2, 4] = V [7, 0, 4, 1, 8, 3, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2497 : V [3, 1, 7, 0, 2, 4, 3, 5] = V [1, 6, 0, 11] := by
  have h0 : V [1, 8, 6, 11, 2, 4, 2, 0] = V [3, 1, 7, 0, 2, 4, 3, 5] :=
    overlap torus2388 torus2454 [3, 1, 7, 0] [2, 4, 2, 0] (by decide)
  have hl : V [1, 8, 6, 11, 2, 4, 2, 0] = V [1, 6, 0, 11] :=
    ((in_context torus47 [1, 8, 6] [4, 2, 0]).trans ((in_context torus6 [1, 8] [11, 4, 2, 0]).trans ((in_context torus59 [1, 8] [2, 0]).trans ((in_context torus8 [1] [11, 2, 0]).trans ((in_context torus47 [1] [0]).trans (in_context torus91 [1, 6] []))))))
  have hr : V [3, 1, 7, 0, 2, 4, 3, 5] = V [3, 1, 7, 0, 2, 4, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2499 : V [0, 5, 1, 3, 8, 2, 7, 0] = V [2, 0, 6, 12] := by
  have h0 : V [2, 0, 6, 12] = V [0, 5, 1, 3, 8, 2, 7, 0] :=
    overlap torus2466 torus24 [0, 5, 1, 3, 8, 2, 7, 0] [12] (by decide)
  have hl : V [2, 0, 6, 12] = V [2, 0, 6, 12] :=
    rfl
  have hr : V [0, 5, 1, 3, 8, 2, 7, 0] = V [0, 5, 1, 3, 8, 2, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2501 : V [0, 6, 1, 4, 2, 3, 8, 0] = V [3, 0, 7, 12] := by
  have h0 : V [3, 0, 7, 12] = V [0, 6, 1, 4, 2, 3, 8, 0] :=
    overlap torus2479 torus24 [0, 6, 1, 4, 2, 3, 8, 0] [12] (by decide)
  have hl : V [3, 0, 7, 12] = V [3, 0, 7, 12] :=
    rfl
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0] = V [0, 6, 1, 4, 2, 3, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2502 : V [0, 6, 1, 4, 2, 3, 8, 11] = V [3, 0, 7, 1] := by
  have h0 : V [3, 0, 7, 1] = V [0, 6, 1, 4, 2, 3, 8, 0, 1, 11] :=
    overlap torus2479 torus92 [0, 6, 1, 4, 2, 3, 8, 0] [1] (by decide)
  have hl : V [3, 0, 7, 1] = V [3, 0, 7, 1] :=
    rfl
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 1, 11] = V [0, 6, 1, 4, 2, 3, 8, 11] :=
    (in_context torus0 [0, 6, 1, 4, 2, 3, 8] [11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2504 : V [5, 3, 0, 6, 1, 2, 0, 11] = V [4, 6, 0, 8] := by
  have h0 : V [5, 3, 3, 0, 5, 7, 6, 8] = V [2, 1, 2, 7, 6, 4, 1, 2, 0, 11] :=
    overlap torus1629 torus2486 [2, 1, 2, 7, 6, 4] [3, 0, 5, 7, 6, 8] (by decide)
  have hl : V [5, 3, 3, 0, 5, 7, 6, 8] = V [4, 6, 0, 8] :=
    ((in_context torus3 [5] [0, 5, 7, 6, 8]).trans ((in_context torus1458 [] [7, 6, 8]).trans (in_context torus1468 [4] [8])))
  have hr : V [2, 1, 2, 7, 6, 4, 1, 2, 0, 11] = V [5, 3, 0, 6, 1, 2, 0, 11] :=
    (in_context torus2093 [] [1, 2, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2507 : V [0, 7, 1, 5, 3, 4, 2, 0] = V [4, 0, 8, 12] := by
  have h0 : V [4, 0, 8, 12] = V [0, 7, 1, 5, 3, 4, 2, 0] :=
    overlap torus2492 torus24 [0, 7, 1, 5, 3, 4, 2, 0] [12] (by decide)
  have hl : V [4, 0, 8, 12] = V [4, 0, 8, 12] :=
    rfl
  have hr : V [0, 7, 1, 5, 3, 4, 2, 0] = V [0, 7, 1, 5, 3, 4, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2508 : V [3, 8, 2, 7, 0, 3, 1, 11] = V [0, 5, 1, 2] := by
  have h0 : V [3, 8, 2, 0, 4, 1, 8, 3, 2, 4] = V [8, 0, 4, 2, 3, 8, 3, 1, 0, 3, 1, 11] :=
    overlap torus2183 torus2495 [8, 0, 4, 2, 3, 8, 3, 1] [0, 4, 1, 8, 3, 2, 4] (by decide)
  have hl : V [3, 8, 2, 0, 4, 1, 8, 3, 2, 4] = V [0, 5, 1, 2] :=
    ((in_context torus1430 [3] [4, 1, 8, 3, 2, 4]).trans ((in_context torus1439 [] [2, 4, 1, 8, 3, 2, 4]).trans ((in_context torus2138 [0, 3] [2, 4]).trans ((in_context torus176 [0, 3] []).trans ((in_context torus3 [0] [6, 5, 4, 5, 2]).trans ((in_context torus1462 [0] [5, 2]).trans (in_context torus5 [0, 5, 1] [2])))))))
  have hr : V [8, 0, 4, 2, 3, 8, 3, 1, 0, 3, 1, 11] = V [3, 8, 2, 7, 0, 3, 1, 11] :=
    (in_context torus2323 [] [0, 3, 1, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2509 : V [3, 8, 2, 7, 0, 3, 1, 6, 11] = V [0, 5, 1] := by
  have h0 : V [0, 5, 1, 2, 2] = V [3, 8, 2, 7, 0, 3, 1, 6, 11] :=
    overlap torus2508 torus47 [3, 8, 2, 7, 0, 3, 1] [2] (by decide)
  have hl : V [0, 5, 1, 2, 2] = V [0, 5, 1] :=
    (in_context torus2 [0, 5, 1] [])
  have hr : V [3, 8, 2, 7, 0, 3, 1, 6, 11] = V [3, 8, 2, 7, 0, 3, 1, 6, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2510 : V [3, 8, 2, 7, 0, 3, 1, 6, 0, 11] = V [0, 5] := by
  have h0 : V [0, 5, 1, 0] = V [3, 8, 2, 7, 0, 3, 1, 6, 0, 11] :=
    overlap torus2509 torus91 [3, 8, 2, 7, 0, 3, 1, 6] [0] (by decide)
  have hl : V [0, 5, 1, 0] = V [0, 5] :=
    (in_context torus1 [0, 5] [])
  have hr : V [3, 8, 2, 7, 0, 3, 1, 6, 0, 11] = V [3, 8, 2, 7, 0, 3, 1, 6, 0, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2511 : V [3, 8, 2, 7, 0, 3, 1, 6, 0] = V [0, 5, 12] := by
  have h0 : V [0, 5, 12] = V [3, 8, 2, 7, 0, 3, 1, 6, 0] :=
    overlap torus2510 torus24 [3, 8, 2, 7, 0, 3, 1, 6, 0] [12] (by decide)
  have hl : V [0, 5, 12] = V [0, 5, 12] :=
    rfl
  have hr : V [3, 8, 2, 7, 0, 3, 1, 6, 0] = V [3, 8, 2, 7, 0, 3, 1, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2512 : V [3, 0, 5, 1, 2, 0, 6, 12] = V [8, 2, 7, 0] := by
  have h0 : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0] = V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 6, 12] :=
    overlap torus2199 torus2499 [7, 2, 1, 6, 0, 8, 4, 2] [5, 1, 3, 8, 2, 7, 0] (by decide)
  have hl : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0] = V [8, 2, 7, 0] :=
    ((in_context torus5 [3, 0] [1, 3, 8, 2, 7, 0]).trans ((in_context torus0 [3] [3, 8, 2, 7, 0]).trans (in_context torus3 [] [8, 2, 7, 0])))
  have hr : V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 6, 12] = V [3, 0, 5, 1, 2, 0, 6, 12] :=
    (in_context torus2312 [] [2, 0, 6, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2517 : V [4, 0, 6, 1, 3, 0, 7, 12] = V [2, 3, 8, 0] := by
  have h0 : V [4, 0, 6, 6, 1, 4, 2, 3, 8, 0] = V [8, 3, 1, 7, 0, 2, 5, 3, 3, 0, 7, 12] :=
    overlap torus2220 torus2501 [8, 3, 1, 7, 0, 2, 5, 3] [6, 1, 4, 2, 3, 8, 0] (by decide)
  have hl : V [4, 0, 6, 6, 1, 4, 2, 3, 8, 0] = V [2, 3, 8, 0] :=
    ((in_context torus6 [4, 0] [1, 4, 2, 3, 8, 0]).trans ((in_context torus0 [4] [4, 2, 3, 8, 0]).trans (in_context torus4 [] [2, 3, 8, 0])))
  have hr : V [8, 3, 1, 7, 0, 2, 5, 3, 3, 0, 7, 12] = V [4, 0, 6, 1, 3, 0, 7, 12] :=
    (in_context torus2322 [] [3, 0, 7, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2522 : V [0, 7, 1, 3, 0, 6, 4, 5] = V [4, 0, 6, 12] := by
  have h0 : V [4, 0, 8, 12, 5, 3] = V [0, 7, 1, 5, 3, 2, 7, 1, 7, 5] :=
    overlap torus2507 torus1999 [0, 7, 1, 5, 3] [5, 3] (by decide)
  have hl : V [4, 0, 8, 12, 5, 3] = V [4, 0, 6, 12] :=
    ((in_context torus66 [4, 0, 8] [3]).trans ((in_context torus8 [4, 0] [12, 3]).trans (in_context torus54 [4, 0] [])))
  have hr : V [0, 7, 1, 5, 3, 2, 7, 1, 7, 5] = V [0, 7, 1, 3, 0, 6, 4, 5] :=
    (in_context torus1687 [0, 7, 1] [5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2525 : V [3, 8, 2, 7, 0, 3, 1, 6] = V [0, 5, 1, 12] := by
  have h0 : V [0, 5, 1, 12] = V [3, 8, 2, 7, 0, 3, 1, 6] :=
    overlap torus2509 torus24 [3, 8, 2, 7, 0, 3, 1, 6] [12] (by decide)
  have hl : V [0, 5, 1, 12] = V [0, 5, 1, 12] :=
    rfl
  have hr : V [3, 8, 2, 7, 0, 3, 1, 6] = V [3, 8, 2, 7, 0, 3, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2527 : V [7, 0, 2, 4, 3, 5, 1, 12] = V [0, 3, 1, 6] := by
  have h0 : V [7, 2, 8, 8, 2, 7, 0, 3, 1, 6] = V [0, 3, 8, 3, 2, 4, 1, 8, 0, 5, 1, 12] :=
    overlap torus2184 torus2525 [0, 3, 8, 3, 2, 4, 1, 8] [8, 2, 7, 0, 3, 1, 6] (by decide)
  have hl : V [7, 2, 8, 8, 2, 7, 0, 3, 1, 6] = V [0, 3, 1, 6] :=
    ((in_context torus8 [7, 2] [2, 7, 0, 3, 1, 6]).trans ((in_context torus2 [7] [7, 0, 3, 1, 6]).trans (in_context torus7 [] [0, 3, 1, 6])))
  have hr : V [0, 3, 8, 3, 2, 4, 1, 8, 0, 5, 1, 12] = V [7, 0, 2, 4, 3, 5, 1, 12] :=
    ((in_context torus2304 [] [0, 5, 1, 12]).trans (in_context torus1545 [7] [5, 1, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2538 : V [8, 5, 1, 5, 2, 1, 2] = V [6, 0, 2, 7, 8] := by
  have h0 : V [6, 2, 8, 2, 3, 7, 8] = V [8, 6, 5, 4, 2, 1, 2] :=
    overlap torus266 torus1434 [8, 6, 5, 4] [8] (by decide)
  have hl : V [6, 2, 8, 2, 3, 7, 8] = V [6, 0, 2, 7, 8] :=
    ((in_context torus1428 [6] [3, 7, 8]).trans (in_context torus3 [6, 0, 2] [7, 8]))
  have hr : V [8, 6, 5, 4, 2, 1, 2] = V [8, 5, 1, 5, 2, 1, 2] :=
    (in_context torus1462 [8] [2, 1, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2545 : V [4, 1, 2, 8, 0, 3, 4] = V [3, 1, 1, 2, 8] := by
  have h0 : V [3, 1, 3, 3, 2, 3, 2] = V [4, 2, 3, 2, 3, 2, 3] :=
    overlap torus1444 torus160 [4] [3, 2, 3, 2] (by decide)
  have hl : V [3, 1, 3, 3, 2, 3, 2] = V [3, 1, 1, 2, 8] :=
    ((in_context torus3 [3, 1] [2, 3, 2]).trans (in_context torus1436 [3, 1] []))
  have hr : V [4, 2, 3, 2, 3, 2, 3] = V [4, 1, 2, 8, 0, 3, 4] :=
    ((in_context torus1436 [4] [3, 2, 3]).trans (in_context torus1439 [4, 1, 2, 8] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2554 : V [5, 1, 3, 2, 0, 4, 5] = V [4, 1, 1, 3, 2] := by
  have h0 : V [4, 1, 4, 4, 3, 4, 3] = V [5, 3, 4, 3, 4, 3, 4] :=
    overlap torus1453 torus161 [5] [4, 3, 4, 3] (by decide)
  have hl : V [4, 1, 4, 4, 3, 4, 3] = V [4, 1, 1, 3, 2] :=
    ((in_context torus4 [4, 1] [3, 4, 3]).trans ((in_context torus1442 [4, 1] []).trans (in_context torus1446 [4, 1] [])))
  have hr : V [5, 3, 4, 3, 4, 3, 4] = V [5, 1, 3, 2, 0, 4, 5] :=
    ((in_context torus1442 [5] [4, 3, 4]).trans ((in_context torus1446 [5] [4, 3, 4]).trans (in_context torus1448 [5, 1, 3, 2] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2555 : V [5, 1, 3, 2, 4, 3, 5, 4] = V [4, 1, 3, 0] := by
  have h0 : V [4, 1, 1, 3, 2, 1, 4, 3] = V [5, 1, 3, 2, 0, 4, 0, 5, 6, 4] :=
    overlap torus2554 torus1546 [5, 1, 3, 2, 0, 4] [1, 4, 3] (by decide)
  have hl : V [4, 1, 1, 3, 2, 1, 4, 3] = V [4, 1, 3, 0] :=
    ((in_context torus1432 [4, 1, 1] [4, 3]).trans ((in_context torus1 [4, 1] [2, 3, 4, 3]).trans (in_context torus1441 [4, 1] [])))
  have hr : V [5, 1, 3, 2, 0, 4, 0, 5, 6, 4] = V [5, 1, 3, 2, 4, 3, 5, 4] :=
    ((in_context torus1561 [5, 1, 3, 2, 0] [4]).trans (in_context torus0 [5, 1, 3, 2] [4, 3, 5, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2566 : V [6, 1, 4, 3, 0, 5, 6] = V [5, 1, 1, 4, 3] := by
  have h0 : V [5, 1, 5, 5, 4, 5, 4] = V [6, 4, 5, 4, 5, 4, 5] :=
    overlap torus1462 torus162 [6] [5, 4, 5, 4] (by decide)
  have hl : V [5, 1, 5, 5, 4, 5, 4] = V [5, 1, 1, 4, 3] :=
    ((in_context torus5 [5, 1] [4, 5, 4]).trans ((in_context torus1451 [5, 1] []).trans (in_context torus1455 [5, 1] [])))
  have hr : V [6, 4, 5, 4, 5, 4, 5] = V [6, 1, 4, 3, 0, 5, 6] :=
    ((in_context torus1451 [6] [5, 4, 5]).trans ((in_context torus1455 [6] [5, 4, 5]).trans (in_context torus1457 [6, 1, 4, 3] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2567 : V [6, 1, 4, 3, 5, 4, 6, 5] = V [5, 1, 4, 0] := by
  have h0 : V [5, 1, 1, 4, 3, 1, 5, 4] = V [6, 1, 4, 3, 0, 5, 0, 6, 7, 5] :=
    overlap torus2566 torus1569 [6, 1, 4, 3, 0, 5] [1, 5, 4] (by decide)
  have hl : V [5, 1, 1, 4, 3, 1, 5, 4] = V [5, 1, 4, 0] :=
    ((in_context torus1443 [5, 1, 1] [5, 4]).trans ((in_context torus1 [5, 1] [3, 4, 5, 4]).trans (in_context torus1450 [5, 1] [])))
  have hr : V [6, 1, 4, 3, 0, 5, 0, 6, 7, 5] = V [6, 1, 4, 3, 5, 4, 6, 5] :=
    ((in_context torus1566 [6, 1, 4, 3, 0] [5]).trans (in_context torus0 [6, 1, 4, 3] [5, 4, 6, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2569 : V [3, 0, 5, 6, 1, 4, 3, 0] = V [4, 0, 6, 5] := by
  have h0 : V [3, 5, 4, 1, 4, 3, 5, 4, 6, 5] = V [0, 6, 4, 6, 5, 7, 1, 4, 5, 1, 4, 0] :=
    overlap torus2192 torus2567 [0, 6, 4, 6, 5, 7, 1, 4] [1, 4, 3, 5, 4, 6, 5] (by decide)
  have hl : V [3, 5, 4, 1, 4, 3, 5, 4, 6, 5] = V [4, 0, 6, 5] :=
    ((in_context torus1452 [3] [4, 3, 5, 4, 6, 5]).trans ((in_context torus1550 [] [4, 3, 5, 4, 6, 5]).trans ((in_context torus4 [1, 3, 2] [3, 5, 4, 6, 5]).trans ((in_context torus1439 [1] [5, 4, 6, 5]).trans ((in_context torus1 [] [3, 4, 5, 4, 6, 5]).trans (in_context torus1450 [] [6, 5]))))))
  have hr : V [0, 6, 4, 6, 5, 7, 1, 4, 5, 1, 4, 0] = V [3, 0, 5, 6, 1, 4, 3, 0] :=
    ((in_context torus2343 [] [5, 1, 4, 0]).trans ((in_context torus1461 [3, 5, 4] [4, 0]).trans ((in_context torus1561 [3, 5] [4, 0]).trans ((in_context torus1546 [3] [5, 4, 0]).trans ((in_context torus1451 [3, 0, 5, 6] [0]).trans (in_context torus1455 [3, 0, 5, 6] [0]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2571 : V [3, 0, 5, 6, 4, 5, 3, 4] = V [4, 0, 5, 1] := by
  have h0 : V [4, 0, 6, 5, 4, 5] = V [3, 0, 5, 6, 1, 4, 1, 3, 2, 4] :=
    overlap torus2569 torus1550 [3, 0, 5, 6, 1, 4] [4, 5] (by decide)
  have hl : V [4, 0, 6, 5, 4, 5] = V [4, 0, 5, 1] :=
    ((in_context torus1462 [4, 0] [5]).trans (in_context torus5 [4, 0, 5, 1] []))
  have hr : V [3, 0, 5, 6, 1, 4, 1, 3, 2, 4] = V [3, 0, 5, 6, 4, 5, 3, 4] :=
    ((in_context torus1554 [3, 0, 5, 6, 1] [4]).trans (in_context torus1 [3, 0, 5, 6] [4, 5, 3, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2603 : V [1, 8, 7, 0, 2, 3, 8] = V [0, 2, 3, 8, 2] := by
  have h0 : V [2, 8, 2, 8, 2, 8, 8] = V [8, 2, 8, 2, 7, 8, 0] :=
    overlap torus166 torus1487 [8, 2, 8, 2] [8] (by decide)
  have hl : V [2, 8, 2, 8, 2, 8, 8] = V [0, 2, 3, 8, 2] :=
    ((in_context torus1428 [] [8, 2, 8, 8]).trans ((in_context torus1487 [0, 2, 3] [8]).trans ((in_context torus1485 [0, 2, 3, 7] []).trans (in_context torus7 [0, 2, 3] [8, 2]))))
  have hr : V [8, 2, 8, 2, 7, 8, 0] = V [1, 8, 7, 0, 2, 3, 8] :=
    ((in_context torus1487 [] [2, 7, 8, 0]).trans ((in_context torus1490 [] [2, 7, 8, 0]).trans ((in_context torus1490 [1, 8, 7, 2] []).trans (in_context torus1590 [1, 8, 7] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2604 : V [2, 3, 1, 8, 7, 0, 2, 3] = V [1, 1, 8, 7] := by
  have h0 : V [1, 2, 7, 8, 8, 7, 0, 2, 3, 8] = V [2, 3, 8, 0, 2, 3, 8, 2] :=
    overlap torus1591 torus2603 [2, 3, 8] [8, 7, 0, 2, 3, 8] (by decide)
  have hl : V [1, 2, 7, 8, 8, 7, 0, 2, 3, 8] = V [1, 1, 8, 7] :=
    ((in_context torus8 [1, 2, 7] [7, 0, 2, 3, 8]).trans ((in_context torus7 [1, 2] [0, 2, 3, 8]).trans ((in_context torus1438 [1] [8]).trans ((in_context torus1487 [1] []).trans (in_context torus1490 [1] [])))))
  have hr : V [2, 3, 8, 0, 2, 3, 8, 2] = V [2, 3, 1, 8, 7, 0, 2, 3] :=
    ((in_context torus1586 [2, 3] [8, 2]).trans (in_context torus1428 [2, 3, 1, 8, 7] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2605 : V [2, 3, 1, 8, 7, 2, 8, 3, 2] = V [1, 8, 0] := by
  have h0 : V [1, 1, 8, 7, 1, 2, 8] = V [2, 3, 1, 8, 7, 0, 2, 0, 3, 4, 2] :=
    overlap torus2604 torus1541 [2, 3, 1, 8, 7, 0, 2] [1, 2, 8] (by decide)
  have hl : V [1, 1, 8, 7, 1, 2, 8] = V [1, 8, 0] :=
    ((in_context torus1479 [1, 1] [2, 8]).trans ((in_context torus1 [1] [7, 8, 2, 8]).trans (in_context torus1486 [1] [])))
  have hr : V [2, 3, 1, 8, 7, 0, 2, 0, 3, 4, 2] = V [2, 3, 1, 8, 7, 2, 8, 3, 2] :=
    (in_context torus1517 [2, 3, 1, 8, 7] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2610 : V [2, 3, 1, 8, 7, 2, 8, 0] = V [1, 8, 3, 2] := by
  have h0 : V [1, 8, 0, 3, 4, 3] = V [2, 3, 1, 8, 7, 2, 8, 3, 3, 0] :=
    overlap torus2605 torus1441 [2, 3, 1, 8, 7, 2, 8, 3] [3, 4, 3] (by decide)
  have hl : V [1, 8, 0, 3, 4, 3] = V [1, 8, 3, 2] :=
    ((in_context torus1442 [1, 8, 0] []).trans ((in_context torus1586 [1] [0]).trans (in_context torus1558 [1] [])))
  have hr : V [2, 3, 1, 8, 7, 2, 8, 3, 3, 0] = V [2, 3, 1, 8, 7, 2, 8, 0] :=
    (in_context torus3 [2, 3, 1, 8, 7, 2, 8] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2618 : V [0, 3, 2, 0, 5, 3, 5] = V [3, 1, 2, 7, 6] := by
  have h0 : V [3, 1, 2, 7, 6] = V [0, 3, 4, 2, 7, 1, 7] :=
    overlap torus1515 torus1480 [0, 3, 4, 2] [7, 6] (by decide)
  have hl : V [3, 1, 2, 7, 6] = V [3, 1, 2, 7, 6] :=
    rfl
  have hr : V [0, 3, 4, 2, 7, 1, 7] = V [0, 3, 2, 0, 5, 3, 5] :=
    (in_context torus1998 [0, 3] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2653 : V [4, 1, 8, 2, 1, 2, 1] = V [2, 4, 5, 6, 8] := by
  have h0 : V [2, 4, 5, 6, 7, 8, 0, 8, 2] = V [5, 4, 3, 4, 8, 2, 1, 2, 1] :=
    overlap torus299 torus1543 [5, 4, 3, 4, 8] [0, 8, 2] (by decide)
  have hl : V [2, 4, 5, 6, 7, 8, 0, 8, 2] = V [2, 4, 5, 6, 8] :=
    ((in_context torus1490 [2, 4, 5, 6] [8, 2]).trans ((in_context torus1484 [2, 4, 5, 6, 1] [2]).trans ((in_context torus1 [2, 4, 5, 6] [8, 2, 2]).trans (in_context torus2 [2, 4, 5, 6, 8] []))))
  have hr : V [5, 4, 3, 4, 8, 2, 1, 2, 1] = V [4, 1, 8, 2, 1, 2, 1] :=
    ((in_context torus1453 [] [4, 8, 2, 1, 2, 1]).trans (in_context torus4 [4, 1] [8, 2, 1, 2, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2672 : V [6, 2, 0, 2, 5, 0, 6] = V [8, 1, 5, 6, 1] := by
  have h0 : V [2, 8, 7, 8, 5, 7, 0, 6, 7] = V [6, 8, 2, 3, 4, 1, 5, 4, 6] :=
    overlap torus238 torus1566 [6, 8, 2, 3, 4] [0, 6, 7] (by decide)
  have hl : V [2, 8, 7, 8, 5, 7, 0, 6, 7] = V [8, 1, 5, 6, 1] :=
    ((in_context torus1484 [2] [5, 7, 0, 6, 7]).trans ((in_context torus1491 [] [5, 7, 0, 6, 7]).trans (in_context torus1498 [8, 1, 5] [])))
  have hr : V [6, 8, 2, 3, 4, 1, 5, 4, 6] = V [6, 2, 0, 2, 5, 0, 6] :=
    ((in_context torus1429 [6] [4, 1, 5, 4, 6]).trans (in_context torus1508 [6, 2, 0, 2] [6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2674 : V [5, 2, 1, 2, 6, 1, 5] = V [3, 0, 6, 5, 0] := by
  have h0 : V [3, 6, 5, 6, 7, 4, 1, 5, 4] = V [5, 3, 2, 8, 7, 0, 6, 7, 5] :=
    overlap torus206 torus1569 [5, 3, 2, 8, 7] [1, 5, 4] (by decide)
  have hl : V [3, 6, 5, 6, 7, 4, 1, 5, 4] = V [3, 0, 6, 5, 0] :=
    ((in_context torus1466 [3] [7, 4, 1, 5, 4]).trans ((in_context torus7 [3, 0, 6] [4, 1, 5, 4]).trans (in_context torus1508 [3, 0, 6] [])))
  have hr : V [5, 3, 2, 8, 7, 0, 6, 7, 5] = V [5, 2, 1, 2, 6, 1, 5] :=
    ((in_context torus1434 [5] [7, 0, 6, 7, 5]).trans (in_context torus1498 [5, 2, 1, 2] [5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2687 : V [8, 3, 4, 5, 7, 0, 8] = V [3, 1, 7, 8, 1] := by
  have h0 : V [4, 3, 2, 3, 7, 2, 0, 8, 2] = V [8, 3, 4, 5, 6, 1, 7, 6, 8] :=
    overlap torus278 torus1582 [8, 3, 4, 5, 6] [0, 8, 2] (by decide)
  have hl : V [4, 3, 2, 3, 7, 2, 0, 8, 2] = V [3, 1, 7, 8, 1] :=
    ((in_context torus1444 [] [3, 7, 2, 0, 8, 2]).trans ((in_context torus3 [3, 1] [7, 2, 0, 8, 2]).trans (in_context torus1491 [3, 1, 7] [])))
  have hr : V [8, 3, 4, 5, 6, 1, 7, 6, 8] = V [8, 3, 4, 5, 7, 0, 8] :=
    (in_context torus1510 [8, 3, 4, 5] [8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2704 : V [4, 1, 4, 2, 8, 7, 5] = V [5, 6, 4, 0, 7] := by
  have h0 : V [1, 5, 1, 4, 2, 3, 4, 3, 7] = V [5, 6, 4, 7, 6, 7, 8] :=
    overlap torus1613 torus133 [5, 6, 4] [2, 3, 4, 3, 7] (by decide)
  have hl : V [1, 5, 1, 4, 2, 3, 4, 3, 7] = V [5, 6, 4, 0, 7] :=
    ((in_context torus1441 [1, 5, 1, 4] [7]).trans ((in_context torus1546 [1] [0, 7]).trans (in_context torus1 [] [5, 6, 4, 0, 7])))
  have hr : V [5, 6, 4, 7, 6, 7, 8] = V [4, 1, 4, 2, 8, 7, 5] :=
    ((in_context torus207 [5] []).trans (in_context torus1453 [] [2, 8, 7, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2710 : V [7, 1, 4, 6, 5, 7, 5] = V [5, 7, 6, 8, 1] := by
  have h0 : V [5, 7, 6, 2, 8, 7, 8] = V [7, 1, 4, 6, 3, 1, 3, 2, 3, 4, 5, 7, 5] :=
    overlap torus1625 torus235 [7, 1, 4, 6, 3, 1, 3] [6, 2, 8, 7, 8] (by decide)
  have hl : V [5, 7, 6, 2, 8, 7, 8] = V [5, 7, 6, 8, 1] :=
    ((in_context torus1484 [5, 7, 6, 2] []).trans (in_context torus1491 [5, 7, 6] []))
  have hr : V [7, 1, 4, 6, 3, 1, 3, 2, 3, 4, 5, 7, 5] = V [7, 1, 4, 6, 5, 7, 5] :=
    ((in_context torus1445 [7, 1, 4, 6] [3, 4, 5, 7, 5]).trans ((in_context torus3 [7, 1, 4, 6, 4] [4, 5, 7, 5]).trans (in_context torus4 [7, 1, 4, 6] [5, 7, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2711 : V [8, 1, 5, 0, 7, 2, 12] = V [1, 4, 0, 7, 5] := by
  have h0 : V [6, 8, 8, 7, 6, 5, 4, 3, 2, 8, 7] = V [8, 1, 5, 7, 4, 1, 4, 3, 4, 5, 6, 7, 8, 2, 12] :=
    overlap torus1626 torus1403 [8, 1, 5, 7, 4, 1, 4] [8, 7, 6, 5, 4, 3, 2, 8, 7] (by decide)
  have hl : V [6, 8, 8, 7, 6, 5, 4, 3, 2, 8, 7] = V [1, 4, 0, 7, 5] :=
    ((in_context torus8 [6] [7, 6, 5, 4, 3, 2, 8, 7]).trans ((in_context torus1469 [] [5, 4, 3, 2, 8, 7]).trans ((in_context torus1473 [] [5, 4, 3, 2, 8, 7]).trans ((in_context torus5 [1, 6] [4, 3, 2, 8, 7]).trans ((in_context torus226 [1] []).trans ((in_context torus1475 [1, 4] [8, 5]).trans (in_context torus8 [1, 4, 0, 7] [5])))))))
  have hr : V [8, 1, 5, 7, 4, 1, 4, 3, 4, 5, 6, 7, 8, 2, 12] = V [8, 1, 5, 0, 7, 2, 12] :=
    ((in_context torus1454 [8, 1, 5, 7] [4, 5, 6, 7, 8, 2, 12]).trans ((in_context torus4 [8, 1, 5, 7, 5] [5, 6, 7, 8, 2, 12]).trans ((in_context torus5 [8, 1, 5, 7] [6, 7, 8, 2, 12]).trans ((in_context torus1475 [8, 1, 5] [8, 2, 12]).trans (in_context torus8 [8, 1, 5, 0, 7] [2, 12])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2712 : V [8, 1, 5, 0, 7, 2, 8, 12] = V [1, 4, 0, 7] := by
  have h0 : V [1, 4, 0, 7, 5, 5] = V [8, 1, 5, 0, 7, 2, 8, 12] :=
    overlap torus2711 torus66 [8, 1, 5, 0, 7, 2] [5] (by decide)
  have hl : V [1, 4, 0, 7, 5, 5] = V [1, 4, 0, 7] :=
    (in_context torus5 [1, 4, 0, 7] [])
  have hr : V [8, 1, 5, 0, 7, 2, 8, 12] = V [8, 1, 5, 0, 7, 2, 8, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2713 : V [6, 0, 2, 1, 7, 5, 6, 4, 0, 7] = V [0, 12] := by
  have h0 : V [8, 6, 7, 5, 5, 0, 7, 2, 8, 12] = V [6, 0, 2, 7, 8, 6, 1, 4, 0, 7] :=
    overlap torus2399 torus2712 [6, 0, 2, 7, 8, 6] [5, 0, 7, 2, 8, 12] (by decide)
  have hl : V [8, 6, 7, 5, 5, 0, 7, 2, 8, 12] = V [0, 12] :=
    ((in_context torus5 [8, 6, 7] [0, 7, 2, 8, 12]).trans ((in_context torus1482 [8] [7, 2, 8, 12]).trans ((in_context torus1585 [] [7, 2, 8, 12]).trans ((in_context torus7 [0, 8, 2] [2, 8, 12]).trans ((in_context torus2 [0, 8] [8, 12]).trans (in_context torus8 [0] [12]))))))
  have hr : V [6, 0, 2, 7, 8, 6, 1, 4, 0, 7] = V [6, 0, 2, 1, 7, 5, 6, 4, 0, 7] :=
    (in_context torus1597 [6, 0, 2] [4, 0, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2716 : V [6, 0, 2, 1, 7, 5, 6, 4] = V [0, 3, 1, 12] := by
  have h0 : V [0, 12, 8, 7, 6, 7] = V [6, 0, 2, 1, 7, 5, 6, 4, 0, 3, 4, 3, 2, 3] :=
    overlap torus2713 torus129 [6, 0, 2, 1, 7, 5, 6, 4, 0] [8, 7, 6, 7] (by decide)
  have hl : V [0, 12, 8, 7, 6, 7] = V [0, 3, 1, 12] :=
    ((in_context torus84 [0] [7, 6, 7]).trans ((in_context torus78 [0, 4] [6, 7]).trans ((in_context torus72 [0, 4, 3] [7]).trans ((in_context torus1444 [0] [12, 7]).trans ((in_context torus78 [0, 3, 1, 3] []).trans (in_context torus3 [0, 3, 1] [12]))))))
  have hr : V [6, 0, 2, 1, 7, 5, 6, 4, 0, 3, 4, 3, 2, 3] = V [6, 0, 2, 1, 7, 5, 6, 4] :=
    ((in_context torus1495 [6, 0, 2, 1, 7, 5, 6] [3, 2, 3]).trans ((in_context torus1945 [6, 0, 2, 1, 7] [2, 3]).trans ((in_context torus2 [6, 0, 2, 1, 7, 1, 5, 1, 4] [3]).trans ((in_context torus1546 [6, 0, 2, 1, 7, 1] []).trans (in_context torus1 [6, 0, 2, 1, 7] [5, 6, 4])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2717 : V [6, 0, 2, 1, 5, 0, 8, 6, 7, 5] = V [0, 12] := by
  have h0 : V [0, 3, 1, 12, 7, 6, 7, 8] = V [6, 0, 2, 1, 7, 5, 4, 3, 2, 8, 7, 5] :=
    overlap torus2716 torus207 [6, 0, 2, 1, 7, 5] [7, 6, 7, 8] (by decide)
  have hl : V [0, 3, 1, 12, 7, 6, 7, 8] = V [0, 12] :=
    ((in_context torus78 [0, 3, 1] [6, 7, 8]).trans ((in_context torus72 [0, 3, 1, 3] [7, 8]).trans ((in_context torus1445 [0] [12, 7, 8]).trans ((in_context torus78 [0, 4, 3] [8]).trans ((in_context torus3 [0, 4] [12, 8]).trans ((in_context torus84 [0, 4] []).trans (in_context torus4 [0] [12])))))))
  have hr : V [6, 0, 2, 1, 7, 5, 4, 3, 2, 8, 7, 5] = V [6, 0, 2, 1, 5, 0, 8, 6, 7, 5] :=
    ((in_context torus246 [6, 0, 2, 1] [7, 5]).trans ((in_context torus1484 [6, 0, 2, 1, 5] [2, 6, 7, 5]).trans (in_context torus2 [6, 0, 2, 1, 5, 0, 8] [6, 7, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2720 : V [6, 0, 2, 1, 5, 0, 8, 1, 6] = V [8, 7, 12] := by
  have h0 : V [0, 12, 1, 5, 4] = V [6, 0, 2, 1, 5, 0, 8, 6, 7, 6, 5] :=
    overlap torus2717 torus1463 [6, 0, 2, 1, 5, 0, 8, 6, 7] [1, 5, 4] (by decide)
  have hl : V [0, 12, 1, 5, 4] = V [8, 7, 12] :=
    ((in_context torus94 [0] [5, 4]).trans ((in_context torus0 [] [12, 5, 4]).trans ((in_context torus66 [] [4]).trans (in_context torus60 [8] []))))
  have hr : V [6, 0, 2, 1, 5, 0, 8, 6, 7, 6, 5] = V [6, 0, 2, 1, 5, 0, 8, 1, 6] :=
    ((in_context torus1469 [6, 0, 2, 1, 5, 0, 8] [5]).trans ((in_context torus1473 [6, 0, 2, 1, 5, 0, 8] [5]).trans (in_context torus5 [6, 0, 2, 1, 5, 0, 8, 1, 6] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2722 : V [6, 0, 2, 1, 5, 0, 8, 1] = V [8, 7, 2, 12] := by
  have h0 : V [8, 7, 12, 6] = V [6, 0, 2, 1, 5, 0, 8, 1] :=
    overlap torus2720 torus6 [6, 0, 2, 1, 5, 0, 8, 1] [6] (by decide)
  have hl : V [8, 7, 12, 6] = V [8, 7, 2, 12] :=
    (in_context torus72 [8, 7] [])
  have hr : V [6, 0, 2, 1, 5, 0, 8, 1] = V [6, 0, 2, 1, 5, 0, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2724 : V [2, 1, 6, 0, 8, 3, 12] = V [1, 5, 0, 8, 6] := by
  have h0 : V [7, 2, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [2, 1, 6, 8, 5, 1, 5, 4, 5, 6, 7, 8, 2, 3, 12] :=
    overlap torus1631 torus1414 [2, 1, 6, 8, 5, 1, 5] [2, 8, 7, 6, 5, 4, 3, 2, 8] (by decide)
  have hl : V [7, 2, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [1, 5, 0, 8, 6] :=
    ((in_context torus2 [7] [8, 7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus1478 [] [6, 5, 4, 3, 2, 8]).trans ((in_context torus1482 [] [6, 5, 4, 3, 2, 8]).trans ((in_context torus6 [1, 7] [5, 4, 3, 2, 8]).trans ((in_context torus246 [1] []).trans ((in_context torus1484 [1, 5] [2, 6]).trans (in_context torus2 [1, 5, 0, 8] [6])))))))
  have hr : V [2, 1, 6, 8, 5, 1, 5, 4, 5, 6, 7, 8, 2, 3, 12] = V [2, 1, 6, 0, 8, 3, 12] :=
    ((in_context torus1463 [2, 1, 6, 8] [5, 6, 7, 8, 2, 3, 12]).trans ((in_context torus5 [2, 1, 6, 8, 6] [6, 7, 8, 2, 3, 12]).trans ((in_context torus6 [2, 1, 6, 8] [7, 8, 2, 3, 12]).trans ((in_context torus1484 [2, 1, 6] [2, 3, 12]).trans (in_context torus2 [2, 1, 6, 0, 8] [3, 12])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2725 : V [2, 1, 6, 0, 8, 3, 2, 12] = V [1, 5, 0, 8] := by
  have h0 : V [1, 5, 0, 8, 6, 6] = V [2, 1, 6, 0, 8, 3, 2, 12] :=
    overlap torus2724 torus72 [2, 1, 6, 0, 8, 3] [6] (by decide)
  have hl : V [1, 5, 0, 8, 6, 6] = V [1, 5, 0, 8] :=
    (in_context torus6 [1, 5, 0, 8] [])
  have hr : V [2, 1, 6, 0, 8, 3, 2, 12] = V [2, 1, 6, 0, 8, 3, 2, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2727 : V [3, 1, 7, 0, 2, 4, 12] = V [1, 6, 0, 2, 7] := by
  have h0 : V [8, 3, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [3, 1, 7, 2, 6, 1, 6, 5, 6, 7, 8, 2, 3, 4, 12] :=
    overlap torus1632 torus1412 [3, 1, 7, 2, 6, 1, 6] [3, 2, 8, 7, 6, 5, 4, 3, 2] (by decide)
  have hl : V [8, 3, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [1, 6, 0, 2, 7] :=
    ((in_context torus3 [8] [2, 8, 7, 6, 5, 4, 3, 2]).trans ((in_context torus1487 [] [7, 6, 5, 4, 3, 2]).trans ((in_context torus1490 [] [7, 6, 5, 4, 3, 2]).trans ((in_context torus7 [1, 8] [6, 5, 4, 3, 2]).trans ((in_context torus266 [1] []).trans ((in_context torus1428 [1, 6] [3, 7]).trans (in_context torus3 [1, 6, 0, 2] [7])))))))
  have hr : V [3, 1, 7, 2, 6, 1, 6, 5, 6, 7, 8, 2, 3, 4, 12] = V [3, 1, 7, 0, 2, 4, 12] :=
    ((in_context torus1472 [3, 1, 7, 2] [6, 7, 8, 2, 3, 4, 12]).trans ((in_context torus6 [3, 1, 7, 2, 7] [7, 8, 2, 3, 4, 12]).trans ((in_context torus7 [3, 1, 7, 2] [8, 2, 3, 4, 12]).trans ((in_context torus1428 [3, 1, 7] [3, 4, 12]).trans (in_context torus3 [3, 1, 7, 0, 2] [4, 12])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2728 : V [3, 1, 7, 0, 2, 4, 3, 12] = V [1, 6, 0, 2] := by
  have h0 : V [1, 6, 0, 2, 7, 7] = V [3, 1, 7, 0, 2, 4, 3, 12] :=
    overlap torus2727 torus78 [3, 1, 7, 0, 2, 4] [7] (by decide)
  have hl : V [1, 6, 0, 2, 7, 7] = V [1, 6, 0, 2] :=
    (in_context torus7 [1, 6, 0, 2] [])
  have hr : V [3, 1, 7, 0, 2, 4, 3, 12] = V [3, 1, 7, 0, 2, 4, 3, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2729 : V [0, 4, 1, 2, 7, 8, 6, 0, 2] = V [8, 0, 12] := by
  have h0 : V [8, 3, 8, 2, 0, 2, 4, 3, 12] = V [0, 4, 2, 3, 8, 1, 6, 0, 2] :=
    overlap torus2320 torus2728 [0, 4, 2, 3, 8] [0, 2, 4, 3, 12] (by decide)
  have hl : V [8, 3, 8, 2, 0, 2, 4, 3, 12] = V [8, 0, 12] :=
    ((in_context torus1430 [8, 3] [2, 4, 3, 12]).trans ((in_context torus1439 [8] [2, 2, 4, 3, 12]).trans ((in_context torus2 [8, 0, 3, 4] [4, 3, 12]).trans ((in_context torus4 [8, 0, 3] [3, 12]).trans (in_context torus3 [8, 0] [12])))))
  have hr : V [0, 4, 2, 3, 8, 1, 6, 0, 2] = V [0, 4, 1, 2, 7, 8, 6, 0, 2] :=
    (in_context torus1591 [0, 4] [6, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2786 : V [5, 1, 5, 2, 1, 8, 1] = V [8, 6, 0, 2, 8] := by
  have h0 : V [8, 6, 0, 2, 8] = V [5, 1, 5, 2, 1, 8, 1] :=
    overlap torus1744 torus1612 [5, 1, 5] [8] (by decide)
  have hl : V [8, 6, 0, 2, 8] = V [8, 6, 0, 2, 8] :=
    rfl
  have hr : V [5, 1, 5, 2, 1, 8, 1] = V [5, 1, 5, 2, 1, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2814 : V [1, 8, 3, 8, 2, 7, 0] = V [4, 2, 3, 8, 3] := by
  have h0 : V [4, 2, 5, 0, 1, 5, 3, 8, 3] = V [1, 8, 3, 8, 7, 7, 2, 7, 0] :=
    overlap torus1792 torus1778 [1, 8, 3, 8, 7] [1, 5, 3, 8, 3] (by decide)
  have hl : V [4, 2, 5, 0, 1, 5, 3, 8, 3] = V [4, 2, 3, 8, 3] :=
    ((in_context torus0 [4, 2, 5] [5, 3, 8, 3]).trans (in_context torus5 [4, 2] [3, 8, 3]))
  have hr : V [1, 8, 3, 8, 7, 7, 2, 7, 0] = V [1, 8, 3, 8, 2, 7, 0] :=
    (in_context torus7 [1, 8, 3, 8] [2, 7, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2830 : V [8, 3, 2, 4, 1, 8, 3] = V [3, 1, 7, 2, 8] := by
  have h0 : V [3, 1, 7, 2, 7, 7, 8] = V [8, 3, 2, 4, 1, 8, 3] :=
    overlap torus1785 torus1805 [8, 3] [7, 8] (by decide)
  have hl : V [3, 1, 7, 2, 7, 7, 8] = V [3, 1, 7, 2, 8] :=
    (in_context torus7 [3, 1, 7, 2] [8])
  have hr : V [8, 3, 2, 4, 1, 8, 3] = V [8, 3, 2, 4, 1, 8, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2831 : V [8, 3, 2, 4, 1, 8, 0, 5] = V [1, 6, 0, 11] := by
  have h0 : V [3, 1, 7, 2, 8, 2, 3, 4, 3, 5] = V [8, 3, 2, 4, 1, 8, 5, 4, 5, 6] :=
    overlap torus2830 torus115 [8, 3, 2, 4, 1, 8] [2, 3, 4, 3, 5] (by decide)
  have hl : V [3, 1, 7, 2, 8, 2, 3, 4, 3, 5] = V [1, 6, 0, 11] :=
    ((in_context torus1428 [3, 1, 7] [3, 4, 3, 5]).trans ((in_context torus3 [3, 1, 7, 0, 2] [4, 3, 5]).trans (in_context torus2497 [] [])))
  have hr : V [8, 3, 2, 4, 1, 8, 5, 4, 5, 6] = V [8, 3, 2, 4, 1, 8, 0, 5] :=
    ((in_context torus1457 [8, 3, 2, 4, 1, 8] [6]).trans (in_context torus6 [8, 3, 2, 4, 1, 8, 0, 5] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2834 : V [4, 1, 4, 5, 1, 2, 4] = V [0, 5, 7, 8, 2] := by
  have h0 : V [0, 5, 6, 6, 7, 8, 2] = V [5, 4, 3, 5, 1, 2, 4] :=
    overlap torus1457 torus1823 [5, 4] [6, 7, 8, 2] (by decide)
  have hl : V [0, 5, 6, 6, 7, 8, 2] = V [0, 5, 7, 8, 2] :=
    (in_context torus6 [0, 5] [7, 8, 2])
  have hr : V [5, 4, 3, 5, 1, 2, 4] = V [4, 1, 4, 5, 1, 2, 4] :=
    (in_context torus1453 [] [5, 1, 2, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2837 : V [7, 3, 0, 5, 1, 2, 4] = V [2, 1, 6, 0, 8] := by
  have h0 : V [2, 1, 6, 8, 6, 6, 7, 8, 2] = V [7, 2, 3, 4, 3, 5, 1, 2, 4] :=
    overlap torus1767 torus1823 [7, 2, 3, 4] [6, 7, 8, 2] (by decide)
  have hl : V [2, 1, 6, 8, 6, 6, 7, 8, 2] = V [2, 1, 6, 0, 8] :=
    ((in_context torus6 [2, 1, 6, 8] [7, 8, 2]).trans ((in_context torus1484 [2, 1, 6] [2]).trans (in_context torus2 [2, 1, 6, 0, 8] [])))
  have hr : V [7, 2, 3, 4, 3, 5, 1, 2, 4] = V [7, 3, 0, 5, 1, 2, 4] :=
    (in_context torus1441 [7] [5, 1, 2, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2838 : V [1, 2, 3, 1, 7, 2, 6] = V [2, 0, 3, 6, 0] := by
  have h0 : V [2, 0, 3, 6, 0] = V [1, 2, 3, 1, 7, 2, 6] :=
    overlap torus1516 torus1832 [1, 2] [6, 0] (by decide)
  have hl : V [2, 0, 3, 6, 0] = V [2, 0, 3, 6, 0] :=
    rfl
  have hr : V [1, 2, 3, 1, 7, 2, 6] = V [1, 2, 3, 1, 7, 2, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2844 : V [8, 4, 0, 6, 1, 3, 5] = V [3, 1, 7, 0, 2] := by
  have h0 : V [3, 1, 7, 2, 7, 7, 2, 0, 2] = V [8, 3, 4, 5, 4, 6, 1, 3, 5] :=
    overlap torus1785 torus1839 [8, 3, 4, 5] [7, 2, 0, 2] (by decide)
  have hl : V [3, 1, 7, 2, 7, 7, 2, 0, 2] = V [3, 1, 7, 0, 2] :=
    ((in_context torus7 [3, 1, 7, 2] [2, 0, 2]).trans (in_context torus2 [3, 1, 7] [0, 2]))
  have hr : V [8, 3, 4, 5, 4, 6, 1, 3, 5] = V [8, 4, 0, 6, 1, 3, 5] :=
    (in_context torus1450 [8] [6, 1, 3, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2853 : V [6, 1, 6, 7, 1, 4, 6] = V [0, 7, 2, 3, 4] := by
  have h0 : V [0, 7, 8, 2, 0, 2, 4] = V [7, 6, 5, 7, 1, 4, 6] :=
    overlap torus1475 torus1863 [7, 6] [2, 0, 2, 4] (by decide)
  have hl : V [0, 7, 8, 2, 0, 2, 4] = V [0, 7, 2, 3, 4] :=
    ((in_context torus1430 [0, 7] [2, 4]).trans ((in_context torus1436 [0, 7] [2, 4]).trans ((in_context torus1428 [0, 7, 1] [4]).trans (in_context torus1 [0, 7] [2, 3, 4]))))
  have hr : V [7, 6, 5, 7, 1, 4, 6] = V [6, 1, 6, 7, 1, 4, 6] :=
    (in_context torus1471 [] [7, 1, 4, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2860 : V [5, 0, 8, 1, 6, 3, 5] = V [7, 4, 1, 2, 0] := by
  have h0 : V [7, 4, 1, 2, 0] = V [5, 0, 8, 6, 6, 1, 6, 3, 5] :=
    overlap torus1889 torus1813 [5, 0, 8, 6] [2, 0] (by decide)
  have hl : V [7, 4, 1, 2, 0] = V [7, 4, 1, 2, 0] :=
    rfl
  have hr : V [5, 0, 8, 6, 6, 1, 6, 3, 5] = V [5, 0, 8, 1, 6, 3, 5] :=
    (in_context torus6 [5, 0, 8] [1, 6, 3, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2872 : V [6, 1, 2, 0, 5, 3, 4] = V [1, 3, 0, 5, 12] := by
  have h0 : V [1, 3, 5, 3, 3, 4, 5, 6, 12] = V [6, 4, 5, 4, 3, 2, 8, 7, 6, 5, 4] :=
    overlap torus1971 torus1409 [6, 4] [3, 4, 5, 6, 12] (by decide)
  have hl : V [1, 3, 5, 3, 3, 4, 5, 6, 12] = V [1, 3, 0, 5, 12] :=
    ((in_context torus3 [1, 3, 5] [4, 5, 6, 12]).trans ((in_context torus1457 [1, 3] [6, 12]).trans (in_context torus6 [1, 3, 0, 5] [12])))
  have hr : V [6, 4, 5, 4, 3, 2, 8, 7, 6, 5, 4] = V [6, 1, 2, 0, 5, 3, 4] :=
    ((in_context torus1451 [6] [3, 2, 8, 7, 6, 5, 4]).trans ((in_context torus1455 [6] [3, 2, 8, 7, 6, 5, 4]).trans ((in_context torus3 [6, 1, 4] [2, 8, 7, 6, 5, 4]).trans ((in_context torus186 [6, 1] [4]).trans ((in_context torus1457 [6, 1, 2] [6, 3, 4]).trans (in_context torus6 [6, 1, 2, 0, 5] [3, 4]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2893 : V [4, 2, 3, 8, 0, 4, 2] = V [2, 0, 5, 3, 4] := by
  have h0 : V [2, 0, 5, 3, 4] = V [4, 2, 3, 8, 0, 4, 2] :=
    overlap torus1683 torus1989 [4, 2] [4] (by decide)
  have hl : V [2, 0, 5, 3, 4] = V [2, 0, 5, 3, 4] :=
    rfl
  have hr : V [4, 2, 3, 8, 0, 4, 2] = V [4, 2, 3, 8, 0, 4, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2904 : V [5, 1, 8, 0, 4, 2, 3] = V [1, 2, 0, 4, 12] := by
  have h0 : V [1, 2, 4, 2, 2, 3, 4, 5, 12] = V [5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] :=
    overlap torus2020 torus1411 [5, 3] [2, 3, 4, 5, 12] (by decide)
  have hl : V [1, 2, 4, 2, 2, 3, 4, 5, 12] = V [1, 2, 0, 4, 12] :=
    ((in_context torus2 [1, 2, 4] [3, 4, 5, 12]).trans ((in_context torus1448 [1, 2] [5, 12]).trans (in_context torus5 [1, 2, 0, 4] [12])))
  have hr : V [5, 3, 4, 3, 2, 8, 7, 6, 5, 4, 3] = V [5, 1, 8, 0, 4, 2, 3] :=
    ((in_context torus1442 [5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus1446 [5] [2, 8, 7, 6, 5, 4, 3]).trans ((in_context torus2 [5, 1, 3] [8, 7, 6, 5, 4, 3]).trans ((in_context torus1480 [5, 1, 3] [5, 4, 3]).trans ((in_context torus1989 [5, 1, 3] [3]).trans (in_context torus3 [5, 1] [8, 0, 4, 2, 3]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2905 : V [5, 1, 8, 0, 4, 1, 2, 7, 8] = V [1, 2, 12] := by
  have h0 : V [1, 2, 0, 4, 12, 8, 1] = V [5, 1, 8, 0, 4, 1, 2, 7, 8] :=
    overlap torus2904 torus1591 [5, 1, 8, 0, 4] [8, 1] (by decide)
  have hl : V [1, 2, 0, 4, 12, 8, 1] = V [1, 2, 12] :=
    ((in_context torus84 [1, 2, 0, 4] [1]).trans ((in_context torus4 [1, 2, 0] [12, 1]).trans ((in_context torus94 [1, 2, 0] []).trans (in_context torus0 [1, 2] [12]))))
  have hr : V [5, 1, 8, 0, 4, 1, 2, 7, 8] = V [5, 1, 8, 0, 4, 1, 2, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2906 : V [5, 1, 8, 0, 4, 1, 2, 7] = V [1, 2, 4, 12] := by
  have h0 : V [1, 2, 12, 8] = V [5, 1, 8, 0, 4, 1, 2, 7] :=
    overlap torus2905 torus8 [5, 1, 8, 0, 4, 1, 2, 7] [8] (by decide)
  have hl : V [1, 2, 12, 8] = V [1, 2, 4, 12] :=
    (in_context torus84 [1, 2] [])
  have hr : V [5, 1, 8, 0, 4, 1, 2, 7] = V [5, 1, 8, 0, 4, 1, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2907 : V [1, 2, 0, 6, 1, 3, 5, 4, 12] = V [5, 1, 3] := by
  have h0 : V [1, 2, 4, 12, 6, 5, 4, 3, 2, 8, 7, 6, 11] = V [5, 1, 8, 0, 4, 1, 2, 8, 2, 3, 4, 5, 6, 7, 8] :=
    overlap torus2906 torus1416 [5, 1, 8, 0, 4, 1, 2] [6, 5, 4, 3, 2, 8, 7, 6, 11] (by decide)
  have hl : V [1, 2, 4, 12, 6, 5, 4, 3, 2, 8, 7, 6, 11] = V [5, 1, 3] :=
    ((in_context torus72 [1, 2, 4] [5, 4, 3, 2, 8, 7, 6, 11]).trans ((in_context torus66 [1, 2, 4, 2] [4, 3, 2, 8, 7, 6, 11]).trans ((in_context torus60 [1, 2, 4, 2, 8] [3, 2, 8, 7, 6, 11]).trans ((in_context torus2034 [1] [12, 3, 2, 8, 7, 6, 11]).trans ((in_context torus1 [] [5, 3, 5, 6, 12, 3, 2, 8, 7, 6, 11]).trans ((in_context torus54 [5, 3, 5, 6] [2, 8, 7, 6, 11]).trans ((in_context torus6 [5, 3, 5] [12, 2, 8, 7, 6, 11]).trans ((in_context torus48 [5, 3, 5] [8, 7, 6, 11]).trans ((in_context torus5 [5, 3] [12, 8, 7, 6, 11]).trans ((in_context torus84 [5, 3] [7, 6, 11]).trans ((in_context torus78 [5, 3, 4] [6, 11]).trans ((in_context torus1442 [5] [12, 6, 11]).trans ((in_context torus1446 [5] [12, 6, 11]).trans ((in_context torus72 [5, 1, 3, 2] [11]).trans ((in_context torus2 [5, 1, 3] [12, 11]).trans (in_context torus29 [5, 1, 3] []))))))))))))))))
  have hr : V [5, 1, 8, 0, 4, 1, 2, 8, 2, 3, 4, 5, 6, 7, 8] = V [1, 2, 0, 6, 1, 3, 5, 4, 12] :=
    ((in_context torus1428 [5, 1, 8, 0, 4, 1] [3, 4, 5, 6, 7, 8]).trans ((in_context torus1 [5, 1, 8, 0, 4] [2, 3, 3, 4, 5, 6, 7, 8]).trans ((in_context torus2904 [] [3, 4, 5, 6, 7, 8]).trans ((in_context torus54 [1, 2, 0, 4] [4, 5, 6, 7, 8]).trans ((in_context torus60 [1, 2, 0, 4, 6] [5, 6, 7, 8]).trans ((in_context torus66 [1, 2, 0, 4, 6, 7] [6, 7, 8]).trans ((in_context torus72 [1, 2, 0, 4, 6, 7, 8] [7, 8]).trans ((in_context torus78 [1, 2, 0, 4, 6, 7, 8, 2] [8]).trans ((in_context torus1429 [1, 2, 0, 4, 6, 7] [12, 8]).trans ((in_context torus1839 [1, 2, 0, 4] [12, 8]).trans ((in_context torus4 [1, 2, 0] [6, 1, 3, 5, 12, 8]).trans (in_context torus84 [1, 2, 0, 6, 1, 3, 5] []))))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2910 : V [1, 2, 0, 6, 1, 3, 5, 4] = V [5, 1, 3, 11] := by
  have h0 : V [5, 1, 3, 11] = V [1, 2, 0, 6, 1, 3, 5, 4] :=
    overlap torus2907 torus29 [1, 2, 0, 6, 1, 3, 5, 4] [11] (by decide)
  have hl : V [5, 1, 3, 11] = V [5, 1, 3, 11] :=
    rfl
  have hr : V [1, 2, 0, 6, 1, 3, 5, 4] = V [1, 2, 0, 6, 1, 3, 5, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2915 : V [6, 1, 3, 5, 4, 6, 4] = V [4, 6, 5, 7, 1] := by
  have h0 : V [4, 6, 5, 7, 1] = V [6, 1, 3, 5, 2, 1, 0, 2, 4, 6, 4] :=
    overlap torus1624 torus2030 [6, 1, 3, 5, 2, 1] [5, 7, 1] (by decide)
  have hl : V [4, 6, 5, 7, 1] = V [4, 6, 5, 7, 1] :=
    rfl
  have hr : V [6, 1, 3, 5, 2, 1, 0, 2, 4, 6, 4] = V [6, 1, 3, 5, 4, 6, 4] :=
    ((in_context torus1968 [] [1, 0, 2, 4, 6, 4]).trans ((in_context torus0 [4, 6, 7, 2] [0, 2, 4, 6, 4]).trans ((in_context torus1839 [4] [4, 6, 4]).trans (in_context torus4 [] [6, 1, 3, 5, 4, 6, 4]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2916 : V [1, 2, 0, 4, 6, 5, 7, 1] = V [5, 1, 8, 11] := by
  have h0 : V [5, 1, 3, 11, 6, 4] = V [1, 2, 0, 4, 6, 5, 7, 1] :=
    overlap torus2910 torus2915 [1, 2, 0] [6, 4] (by decide)
  have hl : V [5, 1, 3, 11, 6, 4] = V [5, 1, 8, 11] :=
    ((in_context torus71 [5, 1, 3] [4]).trans ((in_context torus3 [5, 1] [11, 4]).trans (in_context torus59 [5, 1] [])))
  have hr : V [1, 2, 0, 4, 6, 5, 7, 1] = V [1, 2, 0, 4, 6, 5, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2917 : V [4, 1, 2, 0, 5, 1, 8, 11] = V [6, 5, 7, 1] := by
  have h0 : V [4, 1, 2, 2, 0, 4, 6, 5, 7, 1] = V [7, 5, 0, 8, 1, 6, 3, 5, 5, 1, 8, 11] :=
    overlap torus2207 torus2916 [7, 5, 0, 8, 1, 6, 3, 5] [2, 0, 4, 6, 5, 7, 1] (by decide)
  have hl : V [4, 1, 2, 2, 0, 4, 6, 5, 7, 1] = V [6, 5, 7, 1] :=
    ((in_context torus2 [4, 1] [0, 4, 6, 5, 7, 1]).trans ((in_context torus1 [4] [4, 6, 5, 7, 1]).trans (in_context torus4 [] [6, 5, 7, 1])))
  have hr : V [7, 5, 0, 8, 1, 6, 3, 5, 5, 1, 8, 11] = V [4, 1, 2, 0, 5, 1, 8, 11] :=
    (in_context torus2379 [] [5, 1, 8, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2926 : V [8, 3, 2, 4, 2, 0, 5] = V [0, 4, 2, 4, 3] := by
  have h0 : V [0, 4, 2, 4, 5, 5, 3] = V [8, 3, 2, 4, 2, 0, 5] :=
    overlap torus1789 torus2037 [8, 3] [5, 3] (by decide)
  have hl : V [0, 4, 2, 4, 5, 5, 3] = V [0, 4, 2, 4, 3] :=
    (in_context torus5 [0, 4, 2, 4] [3])
  have hr : V [8, 3, 2, 4, 2, 0, 5] = V [8, 3, 2, 4, 2, 0, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2934 : V [4, 1, 7, 0, 3, 8, 2] = V [1, 8, 0, 3, 12] := by
  have h0 : V [1, 8, 3, 8, 7, 7, 8, 2, 3, 4, 12] = V [4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 2] :=
    overlap torus2055 torus1413 [4, 2] [7, 8, 2, 3, 4, 12] (by decide)
  have hl : V [1, 8, 3, 8, 7, 7, 8, 2, 3, 4, 12] = V [1, 8, 0, 3, 12] :=
    ((in_context torus7 [1, 8, 3, 8] [8, 2, 3, 4, 12]).trans ((in_context torus8 [1, 8, 3] [2, 3, 4, 12]).trans ((in_context torus1439 [1, 8] [4, 12]).trans (in_context torus4 [1, 8, 0, 3] [12]))))
  have hr : V [4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 2] = V [4, 1, 7, 0, 3, 8, 2] :=
    ((in_context torus1436 [4] [8, 7, 6, 5, 4, 3, 2]).trans ((in_context torus8 [4, 1, 2] [7, 6, 5, 4, 3, 2]).trans ((in_context torus1471 [4, 1, 2] [4, 3, 2]).trans ((in_context torus1982 [4, 1, 2] [2]).trans (in_context torus2 [4, 1] [7, 0, 3, 8, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2935 : V [4, 1, 7, 0, 3, 8, 11] = V [1, 8, 0, 3, 5] := by
  have h0 : V [1, 8, 3, 8, 7, 7, 8, 2, 3, 4, 5] = V [4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 11] :=
    overlap torus2055 torus1423 [4, 2] [7, 8, 2, 3, 4, 5] (by decide)
  have hl : V [1, 8, 3, 8, 7, 7, 8, 2, 3, 4, 5] = V [1, 8, 0, 3, 5] :=
    ((in_context torus7 [1, 8, 3, 8] [8, 2, 3, 4, 5]).trans ((in_context torus8 [1, 8, 3] [2, 3, 4, 5]).trans ((in_context torus1439 [1, 8] [4, 5]).trans (in_context torus4 [1, 8, 0, 3] [5]))))
  have hr : V [4, 2, 3, 2, 8, 7, 6, 5, 4, 3, 11] = V [4, 1, 7, 0, 3, 8, 11] :=
    ((in_context torus1436 [4] [8, 7, 6, 5, 4, 3, 11]).trans ((in_context torus8 [4, 1, 2] [7, 6, 5, 4, 3, 11]).trans ((in_context torus1471 [4, 1, 2] [4, 3, 11]).trans ((in_context torus1982 [4, 1, 2] [11]).trans (in_context torus2 [4, 1] [7, 0, 3, 8, 11])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2936 : V [3, 0, 7, 1, 4, 0, 6, 8, 12] = V [0, 6, 4] := by
  have h0 : V [3, 0, 12, 1, 7, 0, 3, 8, 11] = V [0, 6, 1, 4, 2, 3, 8, 0, 1, 8, 0, 3, 5] :=
    overlap torus2485 torus2935 [0, 6, 1, 4, 2, 3, 8, 0] [1, 7, 0, 3, 8, 11] (by decide)
  have hl : V [3, 0, 12, 1, 7, 0, 3, 8, 11] = V [0, 6, 4] :=
    ((in_context torus94 [3, 0] [7, 0, 3, 8, 11]).trans ((in_context torus0 [3] [12, 7, 0, 3, 8, 11]).trans ((in_context torus78 [3] [0, 3, 8, 11]).trans ((in_context torus3 [] [12, 0, 3, 8, 11]).trans ((in_context torus93 [] [3, 8, 11]).trans ((in_context torus54 [0] [8, 11]).trans ((in_context torus84 [0, 6] [11]).trans (in_context torus29 [0, 6, 4] []))))))))
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 1, 8, 0, 3, 5] = V [3, 0, 7, 1, 4, 0, 6, 8, 12] :=
    ((in_context torus2501 [] [1, 8, 0, 3, 5]).trans ((in_context torus94 [3, 0, 7] [8, 0, 3, 5]).trans ((in_context torus84 [3, 0, 7, 1] [0, 3, 5]).trans ((in_context torus93 [3, 0, 7, 1, 4] [3, 5]).trans ((in_context torus54 [3, 0, 7, 1, 4, 0] [5]).trans (in_context torus66 [3, 0, 7, 1, 4, 0, 6] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2938 : V [3, 0, 7, 1, 4, 0, 6, 12] = V [0, 6, 4, 5] := by
  have h0 : V [0, 6, 4, 5] = V [3, 0, 7, 1, 4, 0, 6, 8, 8, 12] :=
    overlap torus2936 torus66 [3, 0, 7, 1, 4, 0, 6, 8] [5] (by decide)
  have hl : V [0, 6, 4, 5] = V [0, 6, 4, 5] :=
    rfl
  have hr : V [3, 0, 7, 1, 4, 0, 6, 8, 8, 12] = V [3, 0, 7, 1, 4, 0, 6, 12] :=
    (in_context torus8 [3, 0, 7, 1, 4, 0, 6] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2952 : V [4, 1, 8, 0, 3, 6, 4] = V [2, 5, 0, 7, 1] := by
  have h0 : V [2, 4, 5, 6, 7, 7, 5, 7, 1] = V [4, 1, 8, 3, 2, 3, 4, 6, 4] :=
    overlap torus2074 torus1964 [4, 1, 8, 3] [7, 5, 7, 1] (by decide)
  have hl : V [2, 4, 5, 6, 7, 7, 5, 7, 1] = V [2, 5, 0, 7, 1] :=
    ((in_context torus7 [2, 4, 5, 6] [5, 7, 1]).trans (in_context torus1459 [2] [7, 1]))
  have hr : V [4, 1, 8, 3, 2, 3, 4, 6, 4] = V [4, 1, 8, 0, 3, 6, 4] :=
    ((in_context torus1439 [4, 1, 8] [4, 6, 4]).trans (in_context torus4 [4, 1, 8, 0, 3] [6, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2955 : V [7, 1, 3, 0, 6, 4, 11] = V [1, 4, 0, 6, 8] := by
  have h0 : V [1, 4, 6, 4, 3, 3, 4, 5, 6, 7, 8] = V [7, 5, 6, 5, 4, 3, 2, 8, 7, 6, 11] :=
    overlap torus2077 torus1417 [7, 5] [3, 4, 5, 6, 7, 8] (by decide)
  have hl : V [1, 4, 6, 4, 3, 3, 4, 5, 6, 7, 8] = V [1, 4, 0, 6, 8] :=
    ((in_context torus3 [1, 4, 6, 4] [4, 5, 6, 7, 8]).trans ((in_context torus4 [1, 4, 6] [5, 6, 7, 8]).trans ((in_context torus1466 [1, 4] [7, 8]).trans (in_context torus7 [1, 4, 0, 6] [8]))))
  have hr : V [7, 5, 6, 5, 4, 3, 2, 8, 7, 6, 11] = V [7, 1, 3, 0, 6, 4, 11] :=
    ((in_context torus1460 [7] [4, 3, 2, 8, 7, 6, 11]).trans ((in_context torus1464 [7] [4, 3, 2, 8, 7, 6, 11]).trans ((in_context torus4 [7, 1, 5] [3, 2, 8, 7, 6, 11]).trans ((in_context torus206 [7, 1] [11]).trans ((in_context torus1466 [7, 1, 3] [7, 4, 11]).trans (in_context torus7 [7, 1, 3, 0, 6] [4, 11]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2962 : V [3, 1, 6, 0, 2, 7, 8] = V [1, 7, 0, 2, 12] := by
  have h0 : V [1, 7, 2, 7, 6, 6, 7, 8, 2, 3, 12] = V [3, 8, 2, 8, 7, 6, 5, 4, 3, 2, 8] :=
    overlap torus2085 torus1402 [3, 8] [6, 7, 8, 2, 3, 12] (by decide)
  have hl : V [1, 7, 2, 7, 6, 6, 7, 8, 2, 3, 12] = V [1, 7, 0, 2, 12] :=
    ((in_context torus6 [1, 7, 2, 7] [7, 8, 2, 3, 12]).trans ((in_context torus7 [1, 7, 2] [8, 2, 3, 12]).trans ((in_context torus1428 [1, 7] [3, 12]).trans (in_context torus3 [1, 7, 0, 2] [12]))))
  have hr : V [3, 8, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [3, 1, 6, 0, 2, 7, 8] :=
    ((in_context torus1487 [3] [7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus1490 [3] [7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus7 [3, 1, 8] [6, 5, 4, 3, 2, 8]).trans ((in_context torus266 [3, 1] [8]).trans ((in_context torus1428 [3, 1, 6] [3, 7, 8]).trans (in_context torus3 [3, 1, 6, 0, 2] [7, 8]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2964 : V [3, 8, 2, 7, 2, 1, 6] = V [1, 7, 2, 7, 8] := by
  have h0 : V [1, 7, 2, 7, 6, 6, 8] = V [3, 8, 2, 7, 2, 1, 6] :=
    overlap torus2085 torus1764 [3, 8] [6, 8] (by decide)
  have hl : V [1, 7, 2, 7, 6, 6, 8] = V [1, 7, 2, 7, 8] :=
    (in_context torus6 [1, 7, 2, 7] [8])
  have hr : V [3, 8, 2, 7, 2, 1, 6] = V [3, 8, 2, 7, 2, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2965 : V [3, 1, 8, 6, 7, 5, 0, 8] = V [1, 7, 0, 12] := by
  have h0 : V [1, 7, 2, 7, 8, 0, 8, 3, 2, 12] = V [3, 8, 2, 7, 1, 5, 0, 8] :=
    overlap torus2964 torus2725 [3, 8, 2, 7] [0, 8, 3, 2, 12] (by decide)
  have hl : V [1, 7, 2, 7, 8, 0, 8, 3, 2, 12] = V [1, 7, 0, 12] :=
    ((in_context torus1490 [1, 7, 2] [8, 3, 2, 12]).trans ((in_context torus1590 [1, 7] [8, 3, 2, 12]).trans ((in_context torus8 [1, 7, 0, 2, 3] [3, 2, 12]).trans ((in_context torus3 [1, 7, 0, 2] [2, 12]).trans (in_context torus2 [1, 7, 0] [12])))))
  have hr : V [3, 8, 2, 7, 1, 5, 0, 8] = V [3, 1, 8, 6, 7, 5, 0, 8] :=
    (in_context torus1598 [3] [5, 0, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2966 : V [7, 2, 8, 3, 1, 7, 0, 12] = V [1, 5, 0, 8] := by
  have h0 : V [7, 2, 8, 1, 8, 6, 7, 5, 0, 8] = V [0, 3, 8, 3, 2, 4, 1, 8, 1, 7, 0, 12] :=
    overlap torus2184 torus2965 [0, 3, 8, 3, 2, 4, 1, 8] [1, 8, 6, 7, 5, 0, 8] (by decide)
  have hl : V [7, 2, 8, 1, 8, 6, 7, 5, 0, 8] = V [1, 5, 0, 8] :=
    ((in_context torus1488 [7] [8, 6, 7, 5, 0, 8]).trans ((in_context torus1582 [] [8, 6, 7, 5, 0, 8]).trans ((in_context torus8 [1, 7, 6] [6, 7, 5, 0, 8]).trans ((in_context torus6 [1, 7] [7, 5, 0, 8]).trans (in_context torus7 [1] [5, 0, 8])))))
  have hr : V [0, 3, 8, 3, 2, 4, 1, 8, 1, 7, 0, 12] = V [7, 2, 8, 3, 1, 7, 0, 12] :=
    (in_context torus2304 [] [1, 7, 0, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2967 : V [7, 2, 8, 3, 1, 7, 0, 4, 12] = V [1, 5, 0] := by
  have h0 : V [1, 5, 0, 8, 8] = V [7, 2, 8, 3, 1, 7, 0, 4, 12] :=
    overlap torus2966 torus84 [7, 2, 8, 3, 1, 7, 0] [8] (by decide)
  have hl : V [1, 5, 0, 8, 8] = V [1, 5, 0] :=
    (in_context torus8 [1, 5, 0] [])
  have hr : V [7, 2, 8, 3, 1, 7, 0, 4, 12] = V [7, 2, 8, 3, 1, 7, 0, 4, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2968 : V [7, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [1, 5] := by
  have h0 : V [1, 5, 0, 1] = V [7, 2, 8, 3, 1, 7, 0, 4, 1, 12] :=
    overlap torus2967 torus94 [7, 2, 8, 3, 1, 7, 0, 4] [1] (by decide)
  have hl : V [1, 5, 0, 1] = V [1, 5] :=
    (in_context torus0 [1, 5] [])
  have hr : V [7, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [7, 2, 8, 3, 1, 7, 0, 4, 1, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2971 : V [7, 2, 8, 3, 1, 7, 0, 4, 1] = V [1, 5, 11] := by
  have h0 : V [1, 5, 11] = V [7, 2, 8, 3, 1, 7, 0, 4, 1] :=
    overlap torus2968 torus29 [7, 2, 8, 3, 1, 7, 0, 4, 1] [11] (by decide)
  have hl : V [1, 5, 11] = V [1, 5, 11] :=
    rfl
  have hr : V [7, 2, 8, 3, 1, 7, 0, 4, 1] = V [7, 2, 8, 3, 1, 7, 0, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2972 : V [7, 2, 8, 3, 1, 7, 0, 4] = V [1, 5, 0, 11] := by
  have h0 : V [1, 5, 0, 11] = V [7, 2, 8, 3, 1, 7, 0, 4] :=
    overlap torus2967 torus29 [7, 2, 8, 3, 1, 7, 0, 4] [11] (by decide)
  have hl : V [1, 5, 0, 11] = V [1, 5, 0, 11] :=
    rfl
  have hr : V [7, 2, 8, 3, 1, 7, 0, 4] = V [7, 2, 8, 3, 1, 7, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2980 : V [4, 1, 8, 3, 2, 4, 2] = V [2, 4, 3, 5, 1] := by
  have h0 : V [2, 4, 6, 0, 1, 6, 3, 5, 1] = V [4, 1, 8, 3, 8, 8, 2, 4, 2] :=
    overlap torus1997 torus2097 [4, 1, 8, 3, 8] [1, 6, 3, 5, 1] (by decide)
  have hl : V [2, 4, 6, 0, 1, 6, 3, 5, 1] = V [2, 4, 3, 5, 1] :=
    ((in_context torus0 [2, 4, 6] [6, 3, 5, 1]).trans (in_context torus6 [2, 4] [3, 5, 1]))
  have hr : V [4, 1, 8, 3, 8, 8, 2, 4, 2] = V [4, 1, 8, 3, 2, 4, 2] :=
    ((in_context torus2074 [] [8, 2, 4, 2]).trans ((in_context torus1805 [2] [2, 4, 2]).trans (in_context torus2 [] [4, 1, 8, 3, 2, 4, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus2987 : V [6, 1, 4, 0, 7, 5, 8] = V [2, 7, 0, 3, 1] := by
  have h0 : V [2, 7, 0, 3, 8, 8, 1] = V [6, 1, 4, 0, 7, 5, 8] :=
    overlap torus1982 torus2107 [6, 1] [8, 1] (by decide)
  have hl : V [2, 7, 0, 3, 8, 8, 1] = V [2, 7, 0, 3, 1] :=
    (in_context torus8 [2, 7, 0, 3] [1])
  have hr : V [6, 1, 4, 0, 7, 5, 8] = V [6, 1, 4, 0, 7, 5, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3008 : V [4, 0, 7, 5, 6, 4, 6] = V [6, 4, 5, 3, 0] := by
  have h0 : V [6, 4, 2, 1, 0, 2, 5, 3, 0] = V [4, 0, 7, 5, 7, 7, 6, 4, 6] :=
    overlap torus2152 torus2099 [4, 0, 7, 5, 7] [0, 2, 5, 3, 0] (by decide)
  have hl : V [6, 4, 2, 1, 0, 2, 5, 3, 0] = V [6, 4, 5, 3, 0] :=
    ((in_context torus1 [6, 4, 2] [2, 5, 3, 0]).trans (in_context torus2 [6, 4] [5, 3, 0]))
  have hr : V [4, 0, 7, 5, 7, 7, 6, 4, 6] = V [4, 0, 7, 5, 6, 4, 6] :=
    (in_context torus7 [4, 0, 7, 5] [6, 4, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3009 : V [5, 0, 8, 1, 6, 4, 5, 3, 0] = V [0, 2, 12] := by
  have h0 : V [0, 7, 12, 4, 6] = V [5, 0, 8, 1, 6, 4, 5, 3, 0] :=
    overlap torus2188 torus3008 [5, 0, 8, 1] [4, 6] (by decide)
  have hl : V [0, 7, 12, 4, 6] = V [0, 2, 12] :=
    ((in_context torus60 [0, 7] [6]).trans ((in_context torus7 [0] [12, 6]).trans (in_context torus72 [0] [])))
  have hr : V [5, 0, 8, 1, 6, 4, 5, 3, 0] = V [5, 0, 8, 1, 6, 4, 5, 3, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3010 : V [5, 0, 8, 1, 6, 4, 5, 3] = V [0, 2, 1, 12] := by
  have h0 : V [0, 2, 12, 1] = V [5, 0, 8, 1, 6, 4, 5, 3] :=
    overlap torus3009 torus0 [5, 0, 8, 1, 6, 4, 5, 3] [1] (by decide)
  have hl : V [0, 2, 12, 1] = V [0, 2, 1, 12] :=
    (in_context torus94 [0, 2] [])
  have hr : V [5, 0, 8, 1, 6, 4, 5, 3] = V [5, 0, 8, 1, 6, 4, 5, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3011 : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 12] = V [1, 3] := by
  have h0 : V [5, 7, 6, 8, 1, 0, 8, 1, 6, 4, 5, 3] = V [7, 1, 4, 6, 5, 7, 0, 2, 1, 12] :=
    overlap torus2710 torus3010 [7, 1, 4, 6, 5, 7] [0, 8, 1, 6, 4, 5, 3] (by decide)
  have hl : V [5, 7, 6, 8, 1, 0, 8, 1, 6, 4, 5, 3] = V [1, 3] :=
    ((in_context torus1 [5, 7, 6, 8] [8, 1, 6, 4, 5, 3]).trans ((in_context torus8 [5, 7, 6] [1, 6, 4, 5, 3]).trans ((in_context torus1470 [5] [6, 4, 5, 3]).trans ((in_context torus1566 [] [6, 4, 5, 3]).trans ((in_context torus6 [1, 5, 4] [4, 5, 3]).trans ((in_context torus4 [1, 5] [5, 3]).trans (in_context torus5 [1] [3])))))))
  have hr : V [7, 1, 4, 6, 5, 7, 0, 2, 1, 12] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 12] :=
    (in_context torus1580 [7, 1, 4] [2, 1, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3012 : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 12] = V [1] := by
  have h0 : V [1, 3, 3] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 12] :=
    overlap torus3011 torus54 [7, 1, 4, 0, 6, 8, 7, 2, 1] [3] (by decide)
  have hl : V [1, 3, 3] = V [1] :=
    (in_context torus3 [1] [])
  have hr : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 12] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3013 : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0, 12] = V [] := by
  have h0 : V [1, 0] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0, 12] :=
    overlap torus3012 torus93 [7, 1, 4, 0, 6, 8, 7, 2, 1, 6] [0] (by decide)
  have hl : V [1, 0] = V [] :=
    (in_context torus1 [] [])
  have hr : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0, 12] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3014 : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0] = V [11] := by
  have h0 : V [11] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0] :=
    overlap torus3013 torus29 [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0] [11] (by decide)
  have hl : V [11] = V [11] :=
    rfl
  have hr : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3016 : V [7, 1, 4, 0, 6, 8, 7, 2, 1] = V [1, 3, 11] := by
  have h0 : V [1, 3, 11] = V [7, 1, 4, 0, 6, 8, 7, 2, 1] :=
    overlap torus3011 torus29 [7, 1, 4, 0, 6, 8, 7, 2, 1] [11] (by decide)
  have hl : V [1, 3, 11] = V [1, 3, 11] :=
    rfl
  have hr : V [7, 1, 4, 0, 6, 8, 7, 2, 1] = V [7, 1, 4, 0, 6, 8, 7, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3018 : V [7, 1, 4, 0, 6, 8, 7, 2] = V [1, 3, 0, 11] := by
  have h0 : V [11, 7, 8, 1, 6, 5, 7, 6, 8, 7] = V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 6, 0] :=
    overlap torus3014 torus2169 [7, 1, 4, 0, 6, 8, 7, 2, 1, 6] [7, 8, 1, 6, 5, 7, 6, 8, 7] (by decide)
  have hl : V [11, 7, 8, 1, 6, 5, 7, 6, 8, 7] = V [1, 3, 0, 11] :=
    ((in_context torus77 [] [8, 1, 6, 5, 7, 6, 8, 7]).trans ((in_context torus83 [4] [1, 6, 5, 7, 6, 8, 7]).trans ((in_context torus92 [4, 5] [6, 5, 7, 6, 8, 7]).trans ((in_context torus71 [4, 5, 1] [5, 7, 6, 8, 7]).trans ((in_context torus65 [4, 5, 1, 3] [7, 6, 8, 7]).trans ((in_context torus77 [4, 5, 1, 3, 2] [6, 8, 7]).trans ((in_context torus71 [4, 5, 1, 3, 2, 4] [8, 7]).trans ((in_context torus83 [4, 5, 1, 3, 2, 4, 3] [7]).trans ((in_context torus77 [4, 5, 1, 3, 2, 4, 3, 5] []).trans ((in_context torus2555 [4] [11]).trans (in_context torus4 [] [1, 3, 0, 11])))))))))))
  have hr : V [7, 1, 4, 0, 6, 8, 7, 2, 1, 6, 6, 0] = V [7, 1, 4, 0, 6, 8, 7, 2] :=
    ((in_context torus6 [7, 1, 4, 0, 6, 8, 7, 2, 1] [0]).trans (in_context torus1 [7, 1, 4, 0, 6, 8, 7, 2] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3019 : V [6, 4, 0, 7, 1, 3, 0, 11] = V [5, 7, 0, 2] := by
  have h0 : V [6, 4, 4, 0, 6, 8, 7, 2] = V [3, 1, 3, 8, 7, 5, 1, 3, 0, 11] :=
    overlap torus1630 torus3018 [3, 1, 3, 8, 7, 5] [4, 0, 6, 8, 7, 2] (by decide)
  have hl : V [6, 4, 4, 0, 6, 8, 7, 2] = V [5, 7, 0, 2] :=
    ((in_context torus4 [6] [0, 6, 8, 7, 2]).trans ((in_context torus1467 [] [8, 7, 2]).trans (in_context torus1477 [5] [2])))
  have hr : V [3, 1, 3, 8, 7, 5, 1, 3, 0, 11] = V [6, 4, 0, 7, 1, 3, 0, 11] :=
    (in_context torus2101 [] [1, 3, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3020 : V [6, 4, 0, 7, 1, 3, 0, 6, 11] = V [5, 7, 0] := by
  have h0 : V [5, 7, 0, 2, 2] = V [6, 4, 0, 7, 1, 3, 0, 6, 11] :=
    overlap torus3019 torus47 [6, 4, 0, 7, 1, 3, 0] [2] (by decide)
  have hl : V [5, 7, 0, 2, 2] = V [5, 7, 0] :=
    (in_context torus2 [5, 7, 0] [])
  have hr : V [6, 4, 0, 7, 1, 3, 0, 6, 11] = V [6, 4, 0, 7, 1, 3, 0, 6, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3059 : V [0, 7, 8, 1, 6, 5, 7] = V [1, 6, 5, 7, 6] := by
  have h0 : V [1, 6, 5, 7, 6] = V [0, 7, 8, 1, 6, 5, 0, 7, 7, 1, 7] :=
    overlap torus2168 torus1480 [0, 7, 8, 1, 6, 5, 0, 7] [7, 6] (by decide)
  have hl : V [1, 6, 5, 7, 6] = V [1, 6, 5, 7, 6] :=
    rfl
  have hr : V [0, 7, 8, 1, 6, 5, 0, 7, 7, 1, 7] = V [0, 7, 8, 1, 6, 5, 7] :=
    ((in_context torus7 [0, 7, 8, 1, 6, 5, 0] [1, 7]).trans (in_context torus0 [0, 7, 8, 1, 6, 5] [7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3063 : V [0, 8, 2, 1, 7, 6, 0] = V [1, 7, 6, 2, 8] := by
  have h0 : V [1, 7, 6, 3, 5, 3, 0, 6, 4, 6, 7] = V [0, 8, 2, 1, 7, 6, 0, 8, 8] :=
    overlap torus2171 torus1852 [0, 8, 2, 1, 7, 6, 0, 8] [3, 5, 3, 0, 6, 4, 6, 7] (by decide)
  have hl : V [1, 7, 6, 3, 5, 3, 0, 6, 4, 6, 7] = V [1, 7, 6, 2, 8] :=
    ((in_context torus2095 [1, 7, 6] [4, 6, 7]).trans ((in_context torus4 [1, 7, 6, 2, 7, 1, 7] [6, 7]).trans ((in_context torus1481 [1, 7, 6, 2] [7]).trans (in_context torus7 [1, 7, 6, 2, 8] []))))
  have hr : V [0, 8, 2, 1, 7, 6, 0, 8, 8] = V [0, 8, 2, 1, 7, 6, 0] :=
    (in_context torus8 [0, 8, 2, 1, 7, 6, 0] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3072 : V [0, 4, 1, 8, 3, 2, 12] = V [7, 0, 3, 1, 8] := by
  have h0 : V [2, 12, 4, 3, 2, 8, 7, 6, 5, 4, 11] = V [7, 0, 3, 1, 6, 0, 2, 1, 7, 6, 7, 8, 2, 3, 4, 5, 6] :=
    overlap torus2180 torus1420 [7, 0, 3, 1, 6, 0, 2, 1, 7] [4, 3, 2, 8, 7, 6, 5, 4, 11] (by decide)
  have hl : V [2, 12, 4, 3, 2, 8, 7, 6, 5, 4, 11] = V [7, 0, 3, 1, 8] :=
    ((in_context torus60 [2] [3, 2, 8, 7, 6, 5, 4, 11]).trans ((in_context torus54 [2, 7] [2, 8, 7, 6, 5, 4, 11]).trans ((in_context torus48 [2, 7, 6] [8, 7, 6, 5, 4, 11]).trans ((in_context torus1471 [2] [12, 8, 7, 6, 5, 4, 11]).trans ((in_context torus84 [2, 6, 1, 6] [7, 6, 5, 4, 11]).trans ((in_context torus78 [2, 6, 1, 6, 4] [6, 5, 4, 11]).trans ((in_context torus1982 [2] [12, 6, 5, 4, 11]).trans ((in_context torus2 [] [7, 0, 3, 8, 12, 6, 5, 4, 11]).trans ((in_context torus72 [7, 0, 3, 8] [5, 4, 11]).trans ((in_context torus66 [7, 0, 3, 8, 2] [4, 11]).trans ((in_context torus1487 [7, 0, 3] [12, 4, 11]).trans ((in_context torus1490 [7, 0, 3] [12, 4, 11]).trans ((in_context torus60 [7, 0, 3, 1, 8, 7] [11]).trans ((in_context torus7 [7, 0, 3, 1, 8] [12, 11]).trans (in_context torus29 [7, 0, 3, 1, 8] [])))))))))))))))
  have hr : V [7, 0, 3, 1, 6, 0, 2, 1, 7, 6, 7, 8, 2, 3, 4, 5, 6] = V [0, 4, 1, 8, 3, 2, 12] :=
    ((in_context torus1475 [7, 0, 3, 1, 6, 0, 2, 1] [8, 2, 3, 4, 5, 6]).trans ((in_context torus1 [7, 0, 3, 1, 6, 0, 2] [7, 8, 8, 2, 3, 4, 5, 6]).trans ((in_context torus2178 [] [8, 2, 3, 4, 5, 6]).trans ((in_context torus84 [0, 2] [2, 3, 4, 5, 6]).trans ((in_context torus48 [0, 2, 4] [3, 4, 5, 6]).trans ((in_context torus54 [0, 2, 4, 5] [4, 5, 6]).trans ((in_context torus60 [0, 2, 4, 5, 6] [5, 6]).trans ((in_context torus66 [0, 2, 4, 5, 6, 7] [6]).trans ((in_context torus1805 [0, 2] [12, 6]).trans ((in_context torus2 [0] [4, 1, 8, 3, 12, 6]).trans (in_context torus72 [0, 4, 1, 8, 3] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3074 : V [5, 0, 8, 1, 6, 4, 5] = V [0, 2, 1, 6, 12] := by
  have h0 : V [0, 7, 12, 4, 7, 6, 5, 6, 3] = V [5, 0, 8, 1, 4, 0, 7, 5, 7, 8, 2, 3, 5] :=
    overlap torus2188 torus195 [5, 0, 8, 1, 4, 0, 7, 5] [4, 7, 6, 5, 6, 3] (by decide)
  have hl : V [0, 7, 12, 4, 7, 6, 5, 6, 3] = V [0, 2, 1, 6, 12] :=
    ((in_context torus60 [0, 7] [7, 6, 5, 6, 3]).trans ((in_context torus7 [0] [12, 7, 6, 5, 6, 3]).trans ((in_context torus78 [0] [6, 5, 6, 3]).trans ((in_context torus72 [0, 3] [5, 6, 3]).trans ((in_context torus66 [0, 3, 2] [6, 3]).trans ((in_context torus1434 [0] [12, 6, 3]).trans ((in_context torus72 [0, 2, 1, 2] [3]).trans ((in_context torus2 [0, 2, 1] [12, 3]).trans (in_context torus54 [0, 2, 1] [])))))))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 5, 7, 8, 2, 3, 5] = V [5, 0, 8, 1, 6, 4, 5] :=
    ((in_context torus2151 [5, 0, 8, 1] [2, 3, 5]).trans ((in_context torus1445 [5, 0, 8, 1, 6] [3, 5]).trans (in_context torus3 [5, 0, 8, 1, 6, 4] [5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3076 : V [0, 2, 1, 6, 8, 7, 12] = V [5, 0, 8, 1, 6] := by
  have h0 : V [7, 12, 2, 8, 7, 6, 5, 4, 3, 2, 11] = V [5, 0, 8, 1, 4, 0, 7, 1, 5, 4, 5, 6, 7, 8, 2, 3, 4] :=
    overlap torus2190 torus1424 [5, 0, 8, 1, 4, 0, 7, 1, 5] [2, 8, 7, 6, 5, 4, 3, 2, 11] (by decide)
  have hl : V [7, 12, 2, 8, 7, 6, 5, 4, 3, 2, 11] = V [5, 0, 8, 1, 6] :=
    ((in_context torus48 [7] [8, 7, 6, 5, 4, 3, 2, 11]).trans ((in_context torus84 [7, 5] [7, 6, 5, 4, 3, 2, 11]).trans ((in_context torus78 [7, 5, 4] [6, 5, 4, 3, 2, 11]).trans ((in_context torus1453 [7] [12, 6, 5, 4, 3, 2, 11]).trans ((in_context torus72 [7, 4, 1, 4] [5, 4, 3, 2, 11]).trans ((in_context torus2065 [] [12, 5, 4, 3, 2, 11]).trans ((in_context torus66 [5, 0, 8, 6, 8] [4, 3, 2, 11]).trans ((in_context torus8 [5, 0, 8, 6] [12, 4, 3, 2, 11]).trans ((in_context torus60 [5, 0, 8, 6] [3, 2, 11]).trans ((in_context torus54 [5, 0, 8, 6, 7] [2, 11]).trans ((in_context torus1469 [5, 0, 8] [12, 2, 11]).trans ((in_context torus1473 [5, 0, 8] [12, 2, 11]).trans ((in_context torus48 [5, 0, 8, 1, 6, 5] [11]).trans ((in_context torus5 [5, 0, 8, 1, 6] [12, 11]).trans (in_context torus29 [5, 0, 8, 1, 6] [])))))))))))))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 1, 5, 4, 5, 6, 7, 8, 2, 3, 4] = V [0, 2, 1, 6, 8, 7, 12] :=
    ((in_context torus1457 [5, 0, 8, 1, 4, 0, 7, 1] [6, 7, 8, 2, 3, 4]).trans ((in_context torus1 [5, 0, 8, 1, 4, 0, 7] [5, 6, 6, 7, 8, 2, 3, 4]).trans ((in_context torus2188 [] [6, 7, 8, 2, 3, 4]).trans ((in_context torus72 [0, 7] [7, 8, 2, 3, 4]).trans ((in_context torus78 [0, 7, 2] [8, 2, 3, 4]).trans ((in_context torus84 [0, 7, 2, 3] [2, 3, 4]).trans ((in_context torus48 [0, 7, 2, 3, 4] [3, 4]).trans ((in_context torus1767 [0] [12, 3, 4]).trans ((in_context torus54 [0, 2, 1, 6, 8, 6] [4]).trans ((in_context torus6 [0, 2, 1, 6, 8] [12, 4]).trans (in_context torus60 [0, 2, 1, 6, 8] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3077 : V [0, 2, 1, 6, 8, 7, 2, 12] = V [5, 0, 8, 1] := by
  have h0 : V [5, 0, 8, 1, 6, 6] = V [0, 2, 1, 6, 8, 7, 2, 12] :=
    overlap torus3076 torus72 [0, 2, 1, 6, 8, 7] [6] (by decide)
  have hl : V [5, 0, 8, 1, 6, 6] = V [5, 0, 8, 1] :=
    (in_context torus6 [5, 0, 8, 1] [])
  have hr : V [0, 2, 1, 6, 8, 7, 2, 12] = V [0, 2, 1, 6, 8, 7, 2, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3092 : V [2, 3, 1, 8, 7, 2, 8] = V [1, 1, 8, 7, 2] := by
  have h0 : V [1, 2, 7, 8, 8, 7, 0, 2, 3, 8, 2] = V [2, 3, 8, 0, 2, 3, 8] :=
    overlap torus1591 torus2265 [2, 3, 8] [8, 7, 0, 2, 3, 8, 2] (by decide)
  have hl : V [1, 2, 7, 8, 8, 7, 0, 2, 3, 8, 2] = V [1, 1, 8, 7, 2] :=
    ((in_context torus8 [1, 2, 7] [7, 0, 2, 3, 8, 2]).trans ((in_context torus7 [1, 2] [0, 2, 3, 8, 2]).trans ((in_context torus1438 [1] [8, 2]).trans ((in_context torus1487 [1] [2]).trans (in_context torus1490 [1] [2])))))
  have hr : V [2, 3, 8, 0, 2, 3, 8] = V [2, 3, 1, 8, 7, 2, 8] :=
    (in_context torus1586 [2, 3] [8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3160 : V [6, 1, 5, 2, 1, 2, 6] = V [0, 6, 5, 0, 8] := by
  have h0 : V [0, 6, 5, 0, 8] = V [6, 1, 5, 2, 1, 2, 6] :=
    overlap torus2336 torus8 [6, 1, 5, 2, 1, 2, 6] [8] (by decide)
  have hl : V [0, 6, 5, 0, 8] = V [0, 6, 5, 0, 8] :=
    rfl
  have hr : V [6, 1, 5, 2, 1, 2, 6] = V [6, 1, 5, 2, 1, 2, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3163 : V [0, 5, 1, 3, 8, 2, 7] = V [2, 0, 6, 1, 12] := by
  have h0 : V [2, 0, 4, 12, 8, 3, 1] = V [0, 5, 1, 3, 8, 2, 7] :=
    overlap torus2356 torus2323 [0, 5, 1] [8, 3, 1] (by decide)
  have hl : V [2, 0, 4, 12, 8, 3, 1] = V [2, 0, 6, 1, 12] :=
    ((in_context torus84 [2, 0, 4] [3, 1]).trans ((in_context torus4 [2, 0] [12, 3, 1]).trans ((in_context torus54 [2, 0] [1]).trans (in_context torus94 [2, 0, 6] []))))
  have hr : V [0, 5, 1, 3, 8, 2, 7] = V [0, 5, 1, 3, 8, 2, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3164 : V [2, 4, 3, 5, 1, 2, 0, 6, 1, 12] = V [1, 7] := by
  have h0 : V [2, 4, 3, 5, 5, 1, 3, 8, 2, 7] = V [4, 1, 8, 3, 2, 4, 2, 2, 0, 6, 1, 12] :=
    overlap torus2454 torus3163 [4, 1, 8, 3, 2, 4, 2] [5, 1, 3, 8, 2, 7] (by decide)
  have hl : V [2, 4, 3, 5, 5, 1, 3, 8, 2, 7] = V [1, 7] :=
    ((in_context torus5 [2, 4, 3] [1, 3, 8, 2, 7]).trans ((in_context torus1443 [2] [3, 8, 2, 7]).trans ((in_context torus1544 [] [3, 8, 2, 7]).trans ((in_context torus3 [1, 2, 8] [8, 2, 7]).trans ((in_context torus8 [1, 2] [2, 7]).trans (in_context torus2 [1] [7]))))))
  have hr : V [4, 1, 8, 3, 2, 4, 2, 2, 0, 6, 1, 12] = V [2, 4, 3, 5, 1, 2, 0, 6, 1, 12] :=
    (in_context torus2980 [] [2, 0, 6, 1, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3165 : V [2, 4, 3, 5, 1, 2, 0, 6, 1] = V [1, 7, 11] := by
  have h0 : V [1, 7, 11] = V [2, 4, 3, 5, 1, 2, 0, 6, 1] :=
    overlap torus3164 torus29 [2, 4, 3, 5, 1, 2, 0, 6, 1] [11] (by decide)
  have hl : V [1, 7, 11] = V [1, 7, 11] :=
    rfl
  have hr : V [2, 4, 3, 5, 1, 2, 0, 6, 1] = V [2, 4, 3, 5, 1, 2, 0, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3166 : V [2, 4, 3, 5, 1, 2, 0, 6, 12] = V [1, 7, 0] := by
  have h0 : V [1, 7, 0] = V [2, 4, 3, 5, 1, 2, 0, 6, 1, 0, 12] :=
    overlap torus3164 torus93 [2, 4, 3, 5, 1, 2, 0, 6, 1] [0] (by decide)
  have hl : V [1, 7, 0] = V [1, 7, 0] :=
    rfl
  have hr : V [2, 4, 3, 5, 1, 2, 0, 6, 1, 0, 12] = V [2, 4, 3, 5, 1, 2, 0, 6, 12] :=
    (in_context torus1 [2, 4, 3, 5, 1, 2, 0, 6] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3169 : V [4, 2, 3, 8, 0, 4, 1, 7, 0] = V [0, 6, 12] := by
  have h0 : V [2, 0, 5, 3, 4, 4, 3, 5, 1, 2, 0, 6, 12] = V [4, 2, 3, 8, 0, 4, 1, 7, 0] :=
    overlap torus2893 torus3166 [4, 2, 3, 8, 0, 4] [4, 3, 5, 1, 2, 0, 6, 12] (by decide)
  have hl : V [2, 0, 5, 3, 4, 4, 3, 5, 1, 2, 0, 6, 12] = V [0, 6, 12] :=
    ((in_context torus4 [2, 0, 5, 3] [3, 5, 1, 2, 0, 6, 12]).trans ((in_context torus3 [2, 0, 5] [5, 1, 2, 0, 6, 12]).trans ((in_context torus5 [2, 0] [1, 2, 0, 6, 12]).trans ((in_context torus0 [2] [2, 0, 6, 12]).trans (in_context torus2 [] [0, 6, 12])))))
  have hr : V [4, 2, 3, 8, 0, 4, 1, 7, 0] = V [4, 2, 3, 8, 0, 4, 1, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3170 : V [4, 2, 3, 8, 0, 4, 1, 7] = V [0, 6, 1, 12] := by
  have h0 : V [2, 0, 5, 3, 4, 4, 3, 5, 1, 2, 0, 6, 1, 12] = V [4, 2, 3, 8, 0, 4, 1, 7] :=
    overlap torus2893 torus3164 [4, 2, 3, 8, 0, 4] [4, 3, 5, 1, 2, 0, 6, 1, 12] (by decide)
  have hl : V [2, 0, 5, 3, 4, 4, 3, 5, 1, 2, 0, 6, 1, 12] = V [0, 6, 1, 12] :=
    ((in_context torus4 [2, 0, 5, 3] [3, 5, 1, 2, 0, 6, 1, 12]).trans ((in_context torus3 [2, 0, 5] [5, 1, 2, 0, 6, 1, 12]).trans ((in_context torus5 [2, 0] [1, 2, 0, 6, 1, 12]).trans ((in_context torus0 [2] [2, 0, 6, 1, 12]).trans (in_context torus2 [] [0, 6, 1, 12])))))
  have hr : V [4, 2, 3, 8, 0, 4, 1, 7] = V [4, 2, 3, 8, 0, 4, 1, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3171 : V [2, 4, 3, 5, 1, 2, 0, 6] = V [1, 7, 0, 11] := by
  have h0 : V [1, 7, 11, 0] = V [2, 4, 3, 5, 1, 2, 0, 6] :=
    overlap torus3165 torus1 [2, 4, 3, 5, 1, 2, 0, 6] [0] (by decide)
  have hl : V [1, 7, 11, 0] = V [1, 7, 0, 11] :=
    (in_context torus91 [1, 7] [])
  have hr : V [2, 4, 3, 5, 1, 2, 0, 6] = V [2, 4, 3, 5, 1, 2, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3174 : V [3, 5, 1, 2, 0, 6, 1, 12] = V [4, 2, 1, 7] := by
  have h0 : V [5, 6, 7, 8, 2, 2, 3, 8, 0, 4, 1, 7] = V [3, 6, 5, 4, 5, 2, 0, 6, 1, 12] :=
    overlap torus177 torus3170 [3, 6, 5, 4, 5, 2] [2, 3, 8, 0, 4, 1, 7] (by decide)
  have hl : V [5, 6, 7, 8, 2, 2, 3, 8, 0, 4, 1, 7] = V [4, 2, 1, 7] :=
    ((in_context torus1823 [] [2, 3, 8, 0, 4, 1, 7]).trans ((in_context torus2018 [3] [3, 8, 0, 4, 1, 7]).trans ((in_context torus3 [] [5, 6, 7, 8, 3, 8, 0, 4, 1, 7]).trans ((in_context torus295 [] [0, 4, 1, 7]).trans ((in_context torus1453 [4, 2] [4, 0, 4, 1, 7]).trans ((in_context torus4 [4, 2, 4, 1] [0, 4, 1, 7]).trans ((in_context torus1 [4, 2, 4] [4, 1, 7]).trans (in_context torus4 [4, 2] [1, 7]))))))))
  have hr : V [3, 6, 5, 4, 5, 2, 0, 6, 1, 12] = V [3, 5, 1, 2, 0, 6, 1, 12] :=
    ((in_context torus1462 [3] [5, 2, 0, 6, 1, 12]).trans (in_context torus5 [3, 5, 1] [2, 0, 6, 1, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3180 : V [5, 0, 8, 6, 7, 5, 11] = V [0, 2, 1, 6, 0] := by
  have h0 : V [7, 5, 6, 4, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [5, 0, 8, 6, 7, 5, 11] :=
    overlap torus2338 torus2365 [5, 0, 8, 6, 7, 5] [4, 0, 8, 1, 5, 0, 7, 2, 8] (by decide)
  have hl : V [7, 5, 6, 4, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [0, 2, 1, 6, 0] :=
    ((in_context torus4 [7, 5, 6] [0, 8, 1, 5, 0, 7, 2, 8]).trans ((in_context torus1473 [7] [8, 1, 5, 0, 7, 2, 8]).trans ((in_context torus1577 [] [8, 1, 5, 0, 7, 2, 8]).trans ((in_context torus2119 [0, 7] [0, 7, 2, 8]).trans ((in_context torus1767 [0] [7, 0, 7, 2, 8]).trans ((in_context torus1482 [0, 2, 1, 6, 8] [7, 2, 8]).trans ((in_context torus1585 [0, 2, 1, 6] [7, 2, 8]).trans ((in_context torus7 [0, 2, 1, 6, 0, 8, 2] [2, 8]).trans ((in_context torus2 [0, 2, 1, 6, 0, 8] [8]).trans (in_context torus8 [0, 2, 1, 6, 0] []))))))))))
  have hr : V [5, 0, 8, 6, 7, 5, 11] = V [5, 0, 8, 6, 7, 5, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3190 : V [3, 0, 6, 1, 4, 2, 11] = V [0, 7, 1, 4, 6] := by
  have h0 : V [5, 2, 1, 7, 7, 0, 4, 1, 8, 0, 3] = V [3, 0, 6, 1, 4, 8, 8, 2, 11] :=
    overlap torus2401 torus2391 [3, 0, 6, 1, 4, 8] [7, 0, 4, 1, 8, 0, 3] (by decide)
  have hl : V [5, 2, 1, 7, 7, 0, 4, 1, 8, 0, 3] = V [0, 7, 1, 4, 6] :=
    ((in_context torus7 [5, 2, 1] [0, 4, 1, 8, 0, 3]).trans ((in_context torus1 [5, 2] [4, 1, 8, 0, 3]).trans ((in_context torus1810 [] [0, 3]).trans ((in_context torus1440 [0, 5, 7, 8] []).trans ((in_context torus1429 [0, 5, 7] [4]).trans ((in_context torus1863 [0, 5] []).trans (in_context torus5 [0] [7, 1, 4, 6])))))))
  have hr : V [3, 0, 6, 1, 4, 8, 8, 2, 11] = V [3, 0, 6, 1, 4, 2, 11] :=
    (in_context torus8 [3, 0, 6, 1, 4] [2, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3191 : V [3, 0, 6, 1, 4, 2, 3, 11] = V [0, 7, 1, 4] := by
  have h0 : V [0, 7, 1, 4, 6, 6] = V [3, 0, 6, 1, 4, 2, 3, 11] :=
    overlap torus3190 torus71 [3, 0, 6, 1, 4, 2] [6] (by decide)
  have hl : V [0, 7, 1, 4, 6, 6] = V [0, 7, 1, 4] :=
    (in_context torus6 [0, 7, 1, 4] [])
  have hr : V [3, 0, 6, 1, 4, 2, 3, 11] = V [3, 0, 6, 1, 4, 2, 3, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3195 : V [6, 1, 3, 5, 4, 6, 12] = V [1, 2, 0, 5, 1] := by
  have h0 : V [4, 6, 5, 7, 7, 1, 3, 0, 6, 1, 4, 2, 3] = V [6, 1, 3, 5, 4, 6, 12] :=
    overlap torus2395 torus2409 [6, 1, 3, 5, 4, 6] [7, 1, 3, 0, 6, 1, 4, 2, 3] (by decide)
  have hl : V [4, 6, 5, 7, 7, 1, 3, 0, 6, 1, 4, 2, 3] = V [1, 2, 0, 5, 1] :=
    ((in_context torus7 [4, 6, 5] [1, 3, 0, 6, 1, 4, 2, 3]).trans ((in_context torus1461 [4] [3, 0, 6, 1, 4, 2, 3]).trans ((in_context torus1561 [] [3, 0, 6, 1, 4, 2, 3]).trans ((in_context torus2095 [1, 4] [1, 4, 2, 3]).trans ((in_context torus1998 [1] [4, 1, 4, 2, 3]).trans ((in_context torus1452 [1, 2, 0, 5, 3] [4, 2, 3]).trans ((in_context torus1550 [1, 2, 0, 5] [4, 2, 3]).trans ((in_context torus4 [1, 2, 0, 5, 1, 3, 2] [2, 3]).trans ((in_context torus2 [1, 2, 0, 5, 1, 3] [3]).trans (in_context torus3 [1, 2, 0, 5, 1] []))))))))))
  have hr : V [6, 1, 3, 5, 4, 6, 12] = V [6, 1, 3, 5, 4, 6, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3200 : V [4, 0, 7, 1, 5, 3, 11] = V [0, 8, 1, 5, 7] := by
  have h0 : V [6, 3, 1, 8, 8, 0, 5, 1, 2, 0, 4] = V [4, 0, 7, 1, 5, 2, 2, 3, 11] :=
    overlap torus2412 torus2262 [4, 0, 7, 1, 5, 2] [8, 0, 5, 1, 2, 0, 4] (by decide)
  have hl : V [6, 3, 1, 8, 8, 0, 5, 1, 2, 0, 4] = V [0, 8, 1, 5, 7] :=
    ((in_context torus8 [6, 3, 1] [0, 5, 1, 2, 0, 4]).trans ((in_context torus1 [6, 3] [5, 1, 2, 0, 4]).trans ((in_context torus1826 [] [0, 4]).trans ((in_context torus1449 [0, 6, 8, 2] []).trans ((in_context torus238 [0] []).trans ((in_context torus1484 [0, 2] [5, 7]).trans (in_context torus1491 [0] [5, 7])))))))
  have hr : V [4, 0, 7, 1, 5, 2, 2, 3, 11] = V [4, 0, 7, 1, 5, 3, 11] :=
    (in_context torus2 [4, 0, 7, 1, 5] [3, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3248 : V [8, 1, 5, 7, 6, 8, 12] = V [1, 4, 0, 7, 1] := by
  have h0 : V [8, 1, 0, 8, 1, 4, 0, 7, 1] = V [6, 2, 0, 2, 4, 5, 7, 7, 6, 8, 12] :=
    overlap torus2143 torus2449 [6, 2, 0, 2, 4, 5, 7] [0, 8, 1, 4, 0, 7, 1] (by decide)
  have hl : V [8, 1, 0, 8, 1, 4, 0, 7, 1] = V [1, 4, 0, 7, 1] :=
    ((in_context torus1 [8] [8, 1, 4, 0, 7, 1]).trans (in_context torus8 [] [1, 4, 0, 7, 1]))
  have hr : V [6, 2, 0, 2, 4, 5, 7, 7, 6, 8, 12] = V [8, 1, 5, 7, 6, 8, 12] :=
    (in_context torus2144 [] [7, 6, 8, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3249 : V [5, 0, 8, 1, 4, 0, 11] = V [0, 7, 2, 8, 3] := by
  have h0 : V [7, 6, 8, 12, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [5, 0, 8, 1, 4, 0, 11] :=
    overlap torus2449 torus2365 [5, 0, 8, 1, 4, 0] [4, 0, 8, 1, 5, 0, 7, 2, 8] (by decide)
  have hl : V [7, 6, 8, 12, 4, 0, 8, 1, 5, 0, 7, 2, 8] = V [0, 7, 2, 8, 3] :=
    ((in_context torus60 [7, 6, 8] [0, 8, 1, 5, 0, 7, 2, 8]).trans ((in_context torus93 [7, 6, 8, 7] [8, 1, 5, 0, 7, 2, 8]).trans ((in_context torus84 [7, 6, 8, 7, 0] [1, 5, 0, 7, 2, 8]).trans ((in_context torus94 [7, 6, 8, 7, 0, 4] [5, 0, 7, 2, 8]).trans ((in_context torus66 [7, 6, 8, 7, 0, 4, 1] [0, 7, 2, 8]).trans ((in_context torus93 [7, 6, 8, 7, 0, 4, 1, 8] [7, 2, 8]).trans ((in_context torus78 [7, 6, 8, 7, 0, 4, 1, 8, 0] [2, 8]).trans ((in_context torus48 [7, 6, 8, 7, 0, 4, 1, 8, 0, 3] [8]).trans ((in_context torus2442 [7, 6, 8] [8]).trans ((in_context torus1588 [] [3, 8, 8]).trans (in_context torus8 [0, 7, 2, 8, 3] [])))))))))))
  have hr : V [5, 0, 8, 1, 4, 0, 11] = V [5, 0, 8, 1, 4, 0, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3252 : V [4, 6, 1, 3, 0, 5, 8] = V [7, 0, 2, 1, 6] := by
  have h0 : V [7, 0, 2, 1, 6] = V [4, 6, 1, 3, 0, 5, 8] :=
    overlap torus2451 torus6 [4, 6, 1, 3, 0, 5, 8] [6] (by decide)
  have hl : V [7, 0, 2, 1, 6] = V [7, 0, 2, 1, 6] :=
    rfl
  have hr : V [4, 6, 1, 3, 0, 5, 8] = V [4, 6, 1, 3, 0, 5, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3259 : V [7, 0, 0, 8, 2, 1, 7] = V [6, 0, 8, 2, 6] := by
  have h0 : V [6, 7, 2, 8, 8, 2, 1, 7, 6, 8, 6] = V [7, 0, 8, 7, 8, 1, 7] :=
    overlap torus1589 torus2461 [7, 0, 8] [8, 2, 1, 7, 6, 8, 6] (by decide)
  have hl : V [6, 7, 2, 8, 8, 2, 1, 7, 6, 8, 6] = V [6, 0, 8, 2, 6] :=
    ((in_context torus8 [6, 7, 2] [2, 1, 7, 6, 8, 6]).trans ((in_context torus2 [6, 7] [1, 7, 6, 8, 6]).trans ((in_context torus1481 [6] [8, 6]).trans (in_context torus1484 [6] [6]))))
  have hr : V [7, 0, 8, 7, 8, 1, 7] = V [7, 0, 0, 8, 2, 1, 7] :=
    (in_context torus1484 [7, 0] [1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3261 : V [3, 0, 5, 1, 2, 0, 6] = V [8, 2, 7, 0, 11] := by
  have h0 : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 11] = V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 6] :=
    overlap torus2199 torus2466 [7, 2, 1, 6, 0, 8, 4, 2] [5, 1, 3, 8, 2, 7, 0, 11] (by decide)
  have hl : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 11] = V [8, 2, 7, 0, 11] :=
    ((in_context torus5 [3, 0] [1, 3, 8, 2, 7, 0, 11]).trans ((in_context torus0 [3] [3, 8, 2, 7, 0, 11]).trans (in_context torus3 [] [8, 2, 7, 0, 11])))
  have hr : V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 6] = V [3, 0, 5, 1, 2, 0, 6] :=
    (in_context torus2312 [] [2, 0, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3262 : V [3, 0, 5, 1, 2, 0, 12] = V [8, 2, 7, 0, 3] := by
  have h0 : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 3] = V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 12] :=
    overlap torus2199 torus2472 [7, 2, 1, 6, 0, 8, 4, 2] [5, 1, 3, 8, 2, 7, 0, 3] (by decide)
  have hl : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 3] = V [8, 2, 7, 0, 3] :=
    ((in_context torus5 [3, 0] [1, 3, 8, 2, 7, 0, 3]).trans ((in_context torus0 [3] [3, 8, 2, 7, 0, 3]).trans (in_context torus3 [] [8, 2, 7, 0, 3])))
  have hr : V [7, 2, 1, 6, 0, 8, 4, 2, 2, 0, 12] = V [3, 0, 5, 1, 2, 0, 12] :=
    (in_context torus2312 [] [2, 0, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3265 : V [5, 1, 2, 4, 3, 5, 12] = V [1, 8, 0, 4, 1] := by
  have h0 : V [3, 5, 4, 6, 6, 1, 4, 2, 3, 8, 0, 4, 1] = V [5, 1, 2, 4, 3, 5, 3, 3, 12] :=
    overlap torus2330 torus2484 [5, 1, 2, 4, 3, 5, 3] [6, 1, 4, 2, 3, 8, 0, 4, 1] (by decide)
  have hl : V [3, 5, 4, 6, 6, 1, 4, 2, 3, 8, 0, 4, 1] = V [1, 8, 0, 4, 1] :=
    ((in_context torus6 [3, 5, 4] [1, 4, 2, 3, 8, 0, 4, 1]).trans ((in_context torus1452 [3] [4, 2, 3, 8, 0, 4, 1]).trans ((in_context torus1550 [] [4, 2, 3, 8, 0, 4, 1]).trans ((in_context torus4 [1, 3, 2] [2, 3, 8, 0, 4, 1]).trans ((in_context torus2 [1, 3] [3, 8, 0, 4, 1]).trans (in_context torus3 [1] [8, 0, 4, 1]))))))
  have hr : V [5, 1, 2, 4, 3, 5, 3, 3, 12] = V [5, 1, 2, 4, 3, 5, 12] :=
    (in_context torus3 [5, 1, 2, 4, 3, 5] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3266 : V [0, 6, 1, 4, 2, 3, 8] = V [3, 0, 7, 1, 12] := by
  have h0 : V [3, 0, 12, 5, 4, 3, 4] = V [0, 6, 1, 4, 2, 3, 8, 0, 3, 4, 3, 2, 3] :=
    overlap torus2485 torus103 [0, 6, 1, 4, 2, 3, 8, 0] [5, 4, 3, 4] (by decide)
  have hl : V [3, 0, 12, 5, 4, 3, 4] = V [3, 0, 7, 1, 12] :=
    ((in_context torus66 [3, 0] [4, 3, 4]).trans ((in_context torus60 [3, 0, 8] [3, 4]).trans ((in_context torus54 [3, 0, 8, 7] [4]).trans ((in_context torus1480 [3, 0] [12, 4]).trans ((in_context torus60 [3, 0, 7, 1, 7] []).trans (in_context torus7 [3, 0, 7, 1] [12]))))))
  have hr : V [0, 6, 1, 4, 2, 3, 8, 0, 3, 4, 3, 2, 3] = V [0, 6, 1, 4, 2, 3, 8] :=
    ((in_context torus146 [0, 6, 1, 4, 2, 3, 8, 0] []).trans ((in_context torus1586 [0, 6, 1, 4, 2, 3] [2, 8, 2]).trans ((in_context torus2 [0, 6, 1, 4, 2, 3, 1, 8, 7] [8, 2]).trans ((in_context torus1484 [0, 6, 1, 4, 2, 3, 1] [2]).trans ((in_context torus1 [0, 6, 1, 4, 2, 3] [8, 2, 2]).trans (in_context torus2 [0, 6, 1, 4, 2, 3, 8] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3267 : V [4, 0, 6, 1, 3, 0, 12] = V [2, 3, 8, 0, 4] := by
  have h0 : V [4, 0, 6, 6, 1, 4, 2, 3, 8, 0, 4] = V [8, 3, 1, 7, 0, 2, 5, 3, 3, 0, 12] :=
    overlap torus2220 torus2485 [8, 3, 1, 7, 0, 2, 5, 3] [6, 1, 4, 2, 3, 8, 0, 4] (by decide)
  have hl : V [4, 0, 6, 6, 1, 4, 2, 3, 8, 0, 4] = V [2, 3, 8, 0, 4] :=
    ((in_context torus6 [4, 0] [1, 4, 2, 3, 8, 0, 4]).trans ((in_context torus0 [4] [4, 2, 3, 8, 0, 4]).trans (in_context torus4 [] [2, 3, 8, 0, 4])))
  have hr : V [8, 3, 1, 7, 0, 2, 5, 3, 3, 0, 12] = V [4, 0, 6, 1, 3, 0, 12] :=
    (in_context torus2322 [] [3, 0, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3273 : V [6, 5, 7, 1, 4, 0, 8] = V [4, 1, 2, 0, 11] := by
  have h0 : V [4, 7, 6, 5, 6, 3, 3, 0, 6, 1, 2, 0, 11] = V [6, 7, 8, 2, 3, 4, 6, 0, 8] :=
    overlap torus196 torus2504 [6, 7, 8, 2, 3] [3, 0, 6, 1, 2, 0, 11] (by decide)
  have hl : V [4, 7, 6, 5, 6, 3, 3, 0, 6, 1, 2, 0, 11] = V [4, 1, 2, 0, 11] :=
    ((in_context torus1471 [4] [6, 3, 3, 0, 6, 1, 2, 0, 11]).trans ((in_context torus6 [4, 6, 1] [3, 3, 0, 6, 1, 2, 0, 11]).trans ((in_context torus3 [4, 6, 1] [0, 6, 1, 2, 0, 11]).trans ((in_context torus1 [4, 6] [6, 1, 2, 0, 11]).trans (in_context torus6 [4] [1, 2, 0, 11])))))
  have hr : V [6, 7, 8, 2, 3, 4, 6, 0, 8] = V [6, 5, 7, 1, 4, 0, 8] :=
    ((in_context torus216 [6] [0, 8]).trans ((in_context torus1480 [6, 5] [7, 4, 0, 8]).trans (in_context torus7 [6, 5, 7, 1] [4, 0, 8])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3278 : V [7, 0, 2, 4, 3, 5, 12] = V [0, 3, 1, 6, 0] := by
  have h0 : V [7, 2, 8, 8, 2, 7, 0, 3, 1, 6, 0] = V [0, 3, 8, 3, 2, 4, 1, 8, 0, 5, 12] :=
    overlap torus2184 torus2511 [0, 3, 8, 3, 2, 4, 1, 8] [8, 2, 7, 0, 3, 1, 6, 0] (by decide)
  have hl : V [7, 2, 8, 8, 2, 7, 0, 3, 1, 6, 0] = V [0, 3, 1, 6, 0] :=
    ((in_context torus8 [7, 2] [2, 7, 0, 3, 1, 6, 0]).trans ((in_context torus2 [7] [7, 0, 3, 1, 6, 0]).trans (in_context torus7 [] [0, 3, 1, 6, 0])))
  have hr : V [0, 3, 8, 3, 2, 4, 1, 8, 0, 5, 12] = V [7, 0, 2, 4, 3, 5, 12] :=
    ((in_context torus2304 [] [0, 5, 12]).trans (in_context torus1545 [7] [5, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3299 : V [3, 0, 5, 6, 4, 5, 1] = V [4, 0, 5, 3, 4] := by
  have h0 : V [4, 0, 5, 1, 0, 3, 4] = V [3, 0, 5, 6, 4, 5, 3, 3, 1] :=
    overlap torus2571 torus1495 [3, 0, 5, 6, 4, 5, 3] [0, 3, 4] (by decide)
  have hl : V [4, 0, 5, 1, 0, 3, 4] = V [4, 0, 5, 3, 4] :=
    (in_context torus1 [4, 0, 5] [3, 4])
  have hr : V [3, 0, 5, 6, 4, 5, 3, 3, 1] = V [3, 0, 5, 6, 4, 5, 1] :=
    (in_context torus3 [3, 0, 5, 6, 4, 5] [1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3313 : V [2, 0, 4, 1, 8, 0, 12] = V [7, 8, 6, 0, 2] := by
  have h0 : V [2, 0, 4, 4, 1, 2, 7, 8, 6, 0, 2] = V [6, 8, 1, 5, 0, 7, 3, 8, 8, 0, 12] :=
    overlap torus2201 torus2729 [6, 8, 1, 5, 0, 7, 3, 8] [4, 1, 2, 7, 8, 6, 0, 2] (by decide)
  have hl : V [2, 0, 4, 4, 1, 2, 7, 8, 6, 0, 2] = V [7, 8, 6, 0, 2] :=
    ((in_context torus4 [2, 0] [1, 2, 7, 8, 6, 0, 2]).trans ((in_context torus0 [2] [2, 7, 8, 6, 0, 2]).trans (in_context torus2 [] [7, 8, 6, 0, 2])))
  have hr : V [6, 8, 1, 5, 0, 7, 3, 8, 8, 0, 12] = V [2, 0, 4, 1, 8, 0, 12] :=
    (in_context torus2325 [] [8, 0, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3318 : V [8, 3, 2, 4, 1, 8, 0] = V [1, 6, 0, 2, 11] := by
  have h0 : V [1, 6, 0, 11, 5] = V [8, 3, 2, 4, 1, 8, 0] :=
    overlap torus2831 torus5 [8, 3, 2, 4, 1, 8, 0] [5] (by decide)
  have hl : V [1, 6, 0, 11, 5] = V [1, 6, 0, 2, 11] :=
    (in_context torus65 [1, 6, 0] [])
  have hr : V [8, 3, 2, 4, 1, 8, 0] = V [8, 3, 2, 4, 1, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3319 : V [0, 6, 0, 7, 2, 3, 4] = V [6, 7, 1, 4, 6] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 6, 7, 1, 4, 6] = V [6, 5, 6, 7, 0, 7, 2, 3, 4] :=
    overlap torus117 torus2853 [6, 5, 6, 7] [1, 6, 7, 1, 4, 6] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 6, 7, 1, 4, 6] = V [6, 7, 1, 4, 6] :=
    ((in_context torus143 [] [1, 6, 7, 1, 4, 6]).trans ((in_context torus1428 [] [3, 2, 1, 6, 7, 1, 4, 6]).trans ((in_context torus3 [0, 2] [2, 1, 6, 7, 1, 4, 6]).trans ((in_context torus2 [0] [1, 6, 7, 1, 4, 6]).trans (in_context torus0 [] [6, 7, 1, 4, 6])))))
  have hr : V [6, 5, 6, 7, 0, 7, 2, 3, 4] = V [0, 6, 0, 7, 2, 3, 4] :=
    ((in_context torus1466 [] [7, 0, 7, 2, 3, 4]).trans (in_context torus7 [0, 6] [0, 7, 2, 3, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3325 : V [5, 1, 8, 0, 4, 1, 2] = V [1, 2, 4, 3, 12] := by
  have h0 : V [1, 2, 0, 4, 12, 2, 8] = V [5, 1, 8, 0, 4, 2, 2, 1, 2] :=
    overlap torus2904 torus1434 [5, 1, 8, 0, 4, 2] [2, 8] (by decide)
  have hl : V [1, 2, 0, 4, 12, 2, 8] = V [1, 2, 4, 3, 12] :=
    ((in_context torus48 [1, 2, 0, 4] [8]).trans ((in_context torus84 [1, 2, 0, 4, 5] []).trans ((in_context torus1451 [1, 2, 0] [12]).trans ((in_context torus1544 [1] [0, 12]).trans ((in_context torus1545 [1, 1] [12]).trans (in_context torus1 [1] [2, 4, 3, 12]))))))
  have hr : V [5, 1, 8, 0, 4, 2, 2, 1, 2] = V [5, 1, 8, 0, 4, 1, 2] :=
    (in_context torus2 [5, 1, 8, 0, 4] [1, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3326 : V [0, 5, 1, 2, 0, 4, 12] = V [8, 0, 4, 2, 3] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 8, 0, 4, 2, 3] = V [5, 4, 5, 6, 1, 2, 0, 4, 12] :=
    overlap torus108 torus2904 [5, 4, 5, 6] [1, 8, 0, 4, 2, 3] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 8, 0, 4, 2, 3] = V [8, 0, 4, 2, 3] :=
    ((in_context torus143 [] [1, 8, 0, 4, 2, 3]).trans ((in_context torus1428 [] [3, 2, 1, 8, 0, 4, 2, 3]).trans ((in_context torus3 [0, 2] [2, 1, 8, 0, 4, 2, 3]).trans ((in_context torus2 [0] [1, 8, 0, 4, 2, 3]).trans (in_context torus0 [] [8, 0, 4, 2, 3])))))
  have hr : V [5, 4, 5, 6, 1, 2, 0, 4, 12] = V [0, 5, 1, 2, 0, 4, 12] :=
    ((in_context torus1457 [] [6, 1, 2, 0, 4, 12]).trans (in_context torus6 [0, 5] [1, 2, 0, 4, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3333 : V [3, 0, 7, 1, 4, 0, 12] = V [0, 6, 4, 5, 3] := by
  have h0 : V [0, 6, 4, 5, 3] = V [3, 0, 7, 1, 4, 0, 6, 6, 12] :=
    overlap torus2938 torus54 [3, 0, 7, 1, 4, 0, 6] [3] (by decide)
  have hl : V [0, 6, 4, 5, 3] = V [0, 6, 4, 5, 3] :=
    rfl
  have hr : V [3, 0, 7, 1, 4, 0, 6, 6, 12] = V [3, 0, 7, 1, 4, 0, 12] :=
    (in_context torus6 [3, 0, 7, 1, 4, 0] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3334 : V [0, 7, 1, 4, 0, 6, 8] = V [3, 0, 6, 4, 11] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 6, 4, 11] = V [7, 6, 7, 8, 1, 4, 0, 6, 8] :=
    overlap torus126 torus2955 [7, 6, 7, 8] [1, 3, 0, 6, 4, 11] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 6, 4, 11] = V [3, 0, 6, 4, 11] :=
    ((in_context torus143 [] [1, 3, 0, 6, 4, 11]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 6, 4, 11]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 6, 4, 11]).trans ((in_context torus2 [0] [1, 3, 0, 6, 4, 11]).trans (in_context torus0 [] [3, 0, 6, 4, 11])))))
  have hr : V [7, 6, 7, 8, 1, 4, 0, 6, 8] = V [0, 7, 1, 4, 0, 6, 8] :=
    ((in_context torus1475 [] [8, 1, 4, 0, 6, 8]).trans (in_context torus8 [0, 7] [1, 4, 0, 6, 8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3335 : V [0, 3, 1, 7, 0, 2, 12] = V [6, 0, 2, 7, 8] := by
  have h0 : V [2, 8, 2, 3, 2, 1, 6, 0, 2, 7, 8] = V [3, 2, 3, 4, 1, 7, 0, 2, 12] :=
    overlap torus143 torus2962 [3, 2, 3, 4] [1, 6, 0, 2, 7, 8] (by decide)
  have hl : V [2, 8, 2, 3, 2, 1, 6, 0, 2, 7, 8] = V [6, 0, 2, 7, 8] :=
    ((in_context torus1428 [] [3, 2, 1, 6, 0, 2, 7, 8]).trans ((in_context torus3 [0, 2] [2, 1, 6, 0, 2, 7, 8]).trans ((in_context torus2 [0] [1, 6, 0, 2, 7, 8]).trans (in_context torus0 [] [6, 0, 2, 7, 8]))))
  have hr : V [3, 2, 3, 4, 1, 7, 0, 2, 12] = V [0, 3, 1, 7, 0, 2, 12] :=
    ((in_context torus1439 [] [4, 1, 7, 0, 2, 12]).trans (in_context torus4 [0, 3] [1, 7, 0, 2, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3339 : V [8, 6, 0, 2, 1, 5, 11] = V [7, 2, 0, 4, 1] := by
  have h0 : V [5, 1, 5, 3, 2, 2, 8, 3, 1, 7, 0, 4, 1] = V [8, 6, 0, 2, 1, 5, 11] :=
    overlap torus1981 torus2971 [8, 6, 0, 2] [2, 8, 3, 1, 7, 0, 4, 1] (by decide)
  have hl : V [5, 1, 5, 3, 2, 2, 8, 3, 1, 7, 0, 4, 1] = V [7, 2, 0, 4, 1] :=
    ((in_context torus2 [5, 1, 5, 3] [8, 3, 1, 7, 0, 4, 1]).trans ((in_context torus1778 [] [1, 7, 0, 4, 1]).trans ((in_context torus0 [7, 2, 7] [7, 0, 4, 1]).trans (in_context torus7 [7, 2] [0, 4, 1]))))
  have hr : V [8, 6, 0, 2, 1, 5, 11] = V [8, 6, 0, 2, 1, 5, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3342 : V [6, 1, 4, 0, 7, 1, 3] = V [8, 7, 2, 1, 12] := by
  have h0 : V [2, 7, 0, 3, 1, 6, 0, 2, 1, 7, 4, 6, 1] = V [6, 1, 4, 0, 7, 5, 5, 1, 3] :=
    overlap torus2987 torus2203 [6, 1, 4, 0, 7, 5] [6, 0, 2, 1, 7, 4, 6, 1] (by decide)
  have hl : V [2, 7, 0, 3, 1, 6, 0, 2, 1, 7, 4, 6, 1] = V [8, 7, 2, 1, 12] :=
    ((in_context torus2259 [2] [4, 6, 1]).trans ((in_context torus2 [] [8, 12, 4, 6, 1]).trans ((in_context torus60 [8] [6, 1]).trans ((in_context torus72 [8, 7] [1]).trans (in_context torus94 [8, 7, 2] [])))))
  have hr : V [6, 1, 4, 0, 7, 5, 5, 1, 3] = V [6, 1, 4, 0, 7, 1, 3] :=
    (in_context torus5 [6, 1, 4, 0, 7] [1, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3344 : V [5, 6, 4, 0, 7, 1, 3] = V [7, 0, 2, 1, 12] := by
  have h0 : V [5, 6, 4, 0, 1, 4, 0, 6, 8, 7, 2, 1, 12] = V [4, 1, 4, 2, 8, 7, 5, 1, 3] :=
    overlap torus2333 torus3011 [4, 1, 4, 2, 8, 7, 5] [1, 4, 0, 6, 8, 7, 2, 1, 12] (by decide)
  have hl : V [5, 6, 4, 0, 1, 4, 0, 6, 8, 7, 2, 1, 12] = V [7, 0, 2, 1, 12] :=
    ((in_context torus0 [5, 6, 4] [4, 0, 6, 8, 7, 2, 1, 12]).trans ((in_context torus4 [5, 6] [0, 6, 8, 7, 2, 1, 12]).trans ((in_context torus1473 [] [6, 8, 7, 2, 1, 12]).trans ((in_context torus1466 [1] [8, 7, 2, 1, 12]).trans ((in_context torus1 [] [6, 7, 8, 7, 2, 1, 12]).trans (in_context torus1477 [] [2, 1, 12]))))))
  have hr : V [4, 1, 4, 2, 8, 7, 5, 1, 3] = V [5, 6, 4, 0, 7, 1, 3] :=
    (in_context torus2704 [] [1, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3347 : V [6, 4, 0, 7, 1, 3, 11] = V [5, 7, 0, 2, 1] := by
  have h0 : V [6, 4, 4, 0, 6, 8, 7, 2, 1] = V [3, 1, 3, 8, 7, 5, 1, 3, 11] :=
    overlap torus1630 torus3016 [3, 1, 3, 8, 7, 5] [4, 0, 6, 8, 7, 2, 1] (by decide)
  have hl : V [6, 4, 4, 0, 6, 8, 7, 2, 1] = V [5, 7, 0, 2, 1] :=
    ((in_context torus4 [6] [0, 6, 8, 7, 2, 1]).trans ((in_context torus1467 [] [8, 7, 2, 1]).trans (in_context torus1477 [5] [2, 1])))
  have hr : V [3, 1, 3, 8, 7, 5, 1, 3, 11] = V [6, 4, 0, 7, 1, 3, 11] :=
    (in_context torus2101 [] [1, 3, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3348 : V [7, 6, 8, 1, 5, 0, 2, 1] = V [5, 1, 3, 11] := by
  have h0 : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 11] = V [7, 8, 2, 3, 4, 5, 7, 0, 2, 1] :=
    overlap torus216 torus3347 [7, 8, 2, 3, 4] [4, 0, 7, 1, 3, 11] (by decide)
  have hl : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 11] = V [5, 1, 3, 11] :=
    ((in_context torus1480 [5] [7, 4, 4, 0, 7, 1, 3, 11]).trans ((in_context torus7 [5, 7, 1] [4, 4, 0, 7, 1, 3, 11]).trans ((in_context torus4 [5, 7, 1] [0, 7, 1, 3, 11]).trans ((in_context torus1 [5, 7] [7, 1, 3, 11]).trans (in_context torus7 [5] [1, 3, 11])))))
  have hr : V [7, 8, 2, 3, 4, 5, 7, 0, 2, 1] = V [7, 6, 8, 1, 5, 0, 2, 1] :=
    ((in_context torus236 [7] [0, 2, 1]).trans ((in_context torus1484 [7, 6, 2] [5, 0, 2, 1]).trans (in_context torus1491 [7, 6] [5, 0, 2, 1])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3349 : V [7, 6, 8, 1, 5, 0, 2] = V [5, 1, 3, 0, 11] := by
  have h0 : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 0, 11] = V [7, 8, 2, 3, 4, 5, 7, 0, 2] :=
    overlap torus216 torus3019 [7, 8, 2, 3, 4] [4, 0, 7, 1, 3, 0, 11] (by decide)
  have hl : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 0, 11] = V [5, 1, 3, 0, 11] :=
    ((in_context torus1480 [5] [7, 4, 4, 0, 7, 1, 3, 0, 11]).trans ((in_context torus7 [5, 7, 1] [4, 4, 0, 7, 1, 3, 0, 11]).trans ((in_context torus4 [5, 7, 1] [0, 7, 1, 3, 0, 11]).trans ((in_context torus1 [5, 7] [7, 1, 3, 0, 11]).trans (in_context torus7 [5] [1, 3, 0, 11])))))
  have hr : V [7, 8, 2, 3, 4, 5, 7, 0, 2] = V [7, 6, 8, 1, 5, 0, 2] :=
    ((in_context torus236 [7] [0, 2]).trans ((in_context torus1484 [7, 6, 2] [5, 0, 2]).trans (in_context torus1491 [7, 6] [5, 0, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3352 : V [1, 5, 0, 2, 1, 6, 12] = V [8, 1, 6, 4, 5] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 8, 1, 6, 4, 5] = V [5, 6, 5, 4, 0, 2, 1, 6, 12] :=
    overlap torus111 torus3074 [5, 6, 5, 4] [0, 8, 1, 6, 4, 5] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 8, 1, 6, 4, 5] = V [8, 1, 6, 4, 5] :=
    ((in_context torus146 [] [0, 8, 1, 6, 4, 5]).trans ((in_context torus1436 [] [8, 2, 0, 8, 1, 6, 4, 5]).trans ((in_context torus8 [1, 2] [2, 0, 8, 1, 6, 4, 5]).trans ((in_context torus2 [1] [0, 8, 1, 6, 4, 5]).trans (in_context torus1 [] [8, 1, 6, 4, 5])))))
  have hr : V [5, 6, 5, 4, 0, 2, 1, 6, 12] = V [1, 5, 0, 2, 1, 6, 12] :=
    ((in_context torus1460 [] [4, 0, 2, 1, 6, 12]).trans ((in_context torus1464 [] [4, 0, 2, 1, 6, 12]).trans (in_context torus4 [1, 5] [0, 2, 1, 6, 12])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3355 : V [0, 2, 1, 6, 8, 7, 2] = V [5, 0, 8, 1, 11] := by
  have h0 : V [5, 0, 8, 1, 11] = V [0, 2, 1, 6, 8, 7, 2] :=
    overlap torus3077 torus29 [0, 2, 1, 6, 8, 7, 2] [11] (by decide)
  have hl : V [5, 0, 8, 1, 11] = V [5, 0, 8, 1, 11] :=
    rfl
  have hr : V [0, 2, 1, 6, 8, 7, 2] = V [0, 2, 1, 6, 8, 7, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3356 : V [2, 7, 1, 5, 0, 8, 1, 11] = V [8, 3, 1, 7] := by
  have h0 : V [2, 7, 2, 1, 6, 8, 7, 2] = V [4, 2, 0, 5, 3, 5, 7, 5, 0, 8, 1, 11] :=
    overlap torus1955 torus3355 [4, 2, 0, 5, 3, 5, 7] [2, 1, 6, 8, 7, 2] (by decide)
  have hl : V [2, 7, 2, 1, 6, 8, 7, 2] = V [8, 3, 1, 7] :=
    ((in_context torus2050 [2] [7, 2]).trans ((in_context torus2 [] [3, 4, 5, 6, 7, 2]).trans ((in_context torus1783 [3] []).trans (in_context torus3 [] [8, 3, 1, 7]))))
  have hr : V [4, 2, 0, 5, 3, 5, 7, 5, 0, 8, 1, 11] = V [2, 7, 1, 5, 0, 8, 1, 11] :=
    (in_context torus1960 [] [5, 0, 8, 1, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3357 : V [2, 7, 1, 5, 0, 8, 1, 4, 11] = V [8, 3, 1] := by
  have h0 : V [8, 3, 1, 7, 7] = V [2, 7, 1, 5, 0, 8, 1, 4, 11] :=
    overlap torus3356 torus77 [2, 7, 1, 5, 0, 8, 1] [7] (by decide)
  have hl : V [8, 3, 1, 7, 7] = V [8, 3, 1] :=
    (in_context torus7 [8, 3, 1] [])
  have hr : V [2, 7, 1, 5, 0, 8, 1, 4, 11] = V [2, 7, 1, 5, 0, 8, 1, 4, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3359 : V [2, 7, 1, 5, 0, 8, 1, 4] = V [8, 3, 1, 12] := by
  have h0 : V [8, 3, 1, 12] = V [2, 7, 1, 5, 0, 8, 1, 4] :=
    overlap torus3357 torus24 [2, 7, 1, 5, 0, 8, 1, 4] [12] (by decide)
  have hl : V [8, 3, 1, 12] = V [8, 3, 1, 12] :=
    rfl
  have hr : V [2, 7, 1, 5, 0, 8, 1, 4] = V [2, 7, 1, 5, 0, 8, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3363 : V [1, 7, 5, 6, 4, 0, 11] = V [2, 1, 6, 0, 3] := by
  have h0 : V [7, 8, 11, 4, 3, 5, 1, 2, 0, 6, 12] = V [2, 1, 6, 0, 3, 1, 7, 0, 1, 7, 0] :=
    overlap torus2384 torus3166 [2, 1, 6, 0, 3, 1, 7, 0] [4, 3, 5, 1, 2, 0, 6, 12] (by decide)
  have hl : V [7, 8, 11, 4, 3, 5, 1, 2, 0, 6, 12] = V [2, 1, 6, 0, 3] :=
    ((in_context torus59 [7, 8] [3, 5, 1, 2, 0, 6, 12]).trans ((in_context torus8 [7] [11, 3, 5, 1, 2, 0, 6, 12]).trans ((in_context torus53 [7] [5, 1, 2, 0, 6, 12]).trans ((in_context torus7 [] [11, 5, 1, 2, 0, 6, 12]).trans ((in_context torus65 [] [1, 2, 0, 6, 12]).trans ((in_context torus92 [2] [2, 0, 6, 12]).trans ((in_context torus47 [2, 1] [0, 6, 12]).trans ((in_context torus91 [2, 1, 6] [6, 12]).trans ((in_context torus71 [2, 1, 6, 0] [12]).trans (in_context torus24 [2, 1, 6, 0, 3] []))))))))))
  have hr : V [2, 1, 6, 0, 3, 1, 7, 0, 1, 7, 0] = V [1, 7, 5, 6, 4, 0, 11] :=
    ((in_context torus2476 [] [1, 7, 0]).trans ((in_context torus92 [7, 8, 6] [7, 0]).trans ((in_context torus1597 [] [11, 7, 0]).trans ((in_context torus77 [1, 7, 5, 6] [0]).trans (in_context torus91 [1, 7, 5, 6, 4] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3372 : V [1, 5, 0, 2, 1, 6, 0] = V [8, 6, 7, 5, 11] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 8, 6, 7, 5, 11] = V [5, 6, 5, 4, 0, 2, 1, 6, 0] :=
    overlap torus111 torus3180 [5, 6, 5, 4] [0, 8, 6, 7, 5, 11] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 8, 6, 7, 5, 11] = V [8, 6, 7, 5, 11] :=
    ((in_context torus146 [] [0, 8, 6, 7, 5, 11]).trans ((in_context torus1436 [] [8, 2, 0, 8, 6, 7, 5, 11]).trans ((in_context torus8 [1, 2] [2, 0, 8, 6, 7, 5, 11]).trans ((in_context torus2 [1] [0, 8, 6, 7, 5, 11]).trans (in_context torus1 [] [8, 6, 7, 5, 11])))))
  have hr : V [5, 6, 5, 4, 0, 2, 1, 6, 0] = V [1, 5, 0, 2, 1, 6, 0] :=
    ((in_context torus1460 [] [4, 0, 2, 1, 6, 0]).trans ((in_context torus1464 [] [4, 0, 2, 1, 6, 0]).trans (in_context torus4 [1, 5] [0, 2, 1, 6, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3373 : V [1, 5, 0, 2, 1, 6, 8, 7] = V [8, 1, 6, 11] := by
  have h0 : V [8, 6, 7, 5, 11, 7, 8, 0] = V [1, 5, 0, 2, 1, 6, 8, 7] :=
    overlap torus3372 torus1483 [1, 5, 0, 2, 1, 6] [7, 8, 0] (by decide)
  have hl : V [8, 6, 7, 5, 11, 7, 8, 0] = V [8, 1, 6, 11] :=
    ((in_context torus77 [8, 6, 7, 5] [8, 0]).trans ((in_context torus1615 [8] [11, 8, 0]).trans ((in_context torus83 [8, 1, 6, 1, 5] [0]).trans ((in_context torus5 [8, 1, 6, 1] [11, 0]).trans ((in_context torus91 [8, 1, 6, 1] []).trans (in_context torus1 [8, 1, 6] [11]))))))
  have hr : V [1, 5, 0, 2, 1, 6, 8, 7] = V [1, 5, 0, 2, 1, 6, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3378 : V [3, 0, 6, 1, 4, 2, 3] = V [0, 7, 1, 4, 12] := by
  have h0 : V [0, 7, 1, 4, 12] = V [3, 0, 6, 1, 4, 2, 3] :=
    overlap torus3191 torus24 [3, 0, 6, 1, 4, 2, 3] [12] (by decide)
  have hl : V [0, 7, 1, 4, 12] = V [0, 7, 1, 4, 12] :=
    rfl
  have hr : V [3, 0, 6, 1, 4, 2, 3] = V [3, 0, 6, 1, 4, 2, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3395 : V [1, 3, 8, 2, 7, 0, 3] = V [5, 1, 2, 0, 12] := by
  have h0 : V [2, 3, 2, 8, 2, 0, 5, 1, 2, 0, 12] = V [3, 4, 3, 2, 8, 2, 7, 0, 3] :=
    overlap torus146 torus3262 [3, 4, 3, 2] [0, 5, 1, 2, 0, 12] (by decide)
  have hl : V [2, 3, 2, 8, 2, 0, 5, 1, 2, 0, 12] = V [5, 1, 2, 0, 12] :=
    ((in_context torus1436 [] [8, 2, 0, 5, 1, 2, 0, 12]).trans ((in_context torus8 [1, 2] [2, 0, 5, 1, 2, 0, 12]).trans ((in_context torus2 [1] [0, 5, 1, 2, 0, 12]).trans (in_context torus1 [] [5, 1, 2, 0, 12]))))
  have hr : V [3, 4, 3, 2, 8, 2, 7, 0, 3] = V [1, 3, 8, 2, 7, 0, 3] :=
    ((in_context torus1442 [] [2, 8, 2, 7, 0, 3]).trans ((in_context torus1446 [] [2, 8, 2, 7, 0, 3]).trans (in_context torus2 [1, 3] [8, 2, 7, 0, 3])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3397 : V [1, 4, 2, 3, 8, 0, 4] = V [6, 1, 3, 0, 12] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 6, 1, 3, 0, 12] = V [4, 5, 4, 3, 2, 3, 8, 0, 4] :=
    overlap torus103 torus3267 [4, 5, 4, 3] [0, 6, 1, 3, 0, 12] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 6, 1, 3, 0, 12] = V [6, 1, 3, 0, 12] :=
    ((in_context torus146 [] [0, 6, 1, 3, 0, 12]).trans ((in_context torus1436 [] [8, 2, 0, 6, 1, 3, 0, 12]).trans ((in_context torus8 [1, 2] [2, 0, 6, 1, 3, 0, 12]).trans ((in_context torus2 [1] [0, 6, 1, 3, 0, 12]).trans (in_context torus1 [] [6, 1, 3, 0, 12])))))
  have hr : V [4, 5, 4, 3, 2, 3, 8, 0, 4] = V [1, 4, 2, 3, 8, 0, 4] :=
    ((in_context torus1451 [] [3, 2, 3, 8, 0, 4]).trans ((in_context torus1455 [] [3, 2, 3, 8, 0, 4]).trans (in_context torus3 [1, 4] [2, 3, 8, 0, 4])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3398 : V [8, 6, 7, 5, 0, 8, 11] = V [0, 3, 1, 7, 0] := by
  have h0 : V [11, 0, 6, 1, 3, 0, 12] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 2, 3, 8, 0, 4] :=
    overlap torus2389 torus3267 [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] [0, 6, 1, 3, 0, 12] (by decide)
  have hl : V [11, 0, 6, 1, 3, 0, 12] = V [0, 3, 1, 7, 0] :=
    ((in_context torus91 [] [6, 1, 3, 0, 12]).trans ((in_context torus71 [0] [1, 3, 0, 12]).trans ((in_context torus92 [0, 3] [3, 0, 12]).trans ((in_context torus53 [0, 3, 1] [0, 12]).trans ((in_context torus91 [0, 3, 1, 7] [12]).trans (in_context torus24 [0, 3, 1, 7, 0] []))))))
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 2, 3, 8, 0, 4] = V [8, 6, 7, 5, 0, 8, 11] :=
    ((in_context torus2390 [] [2, 3, 8, 0, 4]).trans ((in_context torus47 [8] [3, 8, 0, 4]).trans ((in_context torus53 [8, 6] [8, 0, 4]).trans ((in_context torus83 [8, 6, 7] [0, 4]).trans ((in_context torus91 [8, 6, 7, 5] [4]).trans (in_context torus59 [8, 6, 7, 5, 0] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3401 : V [6, 5, 7, 1, 4, 0, 12] = V [4, 1, 2, 0, 5] := by
  have h0 : V [4, 1, 2, 0, 11, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [6, 5, 7, 1, 4, 0, 12] :=
    overlap torus3273 torus2196 [6, 5, 7, 1, 4, 0] [0, 4, 1, 7, 0, 3, 1, 8, 6, 7] (by decide)
  have hl : V [4, 1, 2, 0, 11, 0, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [4, 1, 2, 0, 5] :=
    ((in_context torus91 [4, 1, 2, 0] [4, 1, 7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus59 [4, 1, 2, 0, 0] [1, 7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus92 [4, 1, 2, 0, 0, 8] [7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus77 [4, 1, 2, 0, 0, 8, 1] [0, 3, 1, 8, 6, 7]).trans ((in_context torus91 [4, 1, 2, 0, 0, 8, 1, 4] [3, 1, 8, 6, 7]).trans ((in_context torus53 [4, 1, 2, 0, 0, 8, 1, 4, 0] [1, 8, 6, 7]).trans ((in_context torus92 [4, 1, 2, 0, 0, 8, 1, 4, 0, 7] [8, 6, 7]).trans ((in_context torus83 [4, 1, 2, 0, 0, 8, 1, 4, 0, 7, 1] [6, 7]).trans ((in_context torus71 [4, 1, 2, 0, 0, 8, 1, 4, 0, 7, 1, 5] [7]).trans ((in_context torus3200 [4, 1, 2, 0, 0, 8, 1] [7]).trans ((in_context torus1 [4, 1, 2, 0, 0, 8] [8, 1, 5, 7, 7]).trans ((in_context torus8 [4, 1, 2, 0, 0] [1, 5, 7, 7]).trans ((in_context torus0 [4, 1, 2, 0] [5, 7, 7]).trans (in_context torus7 [4, 1, 2, 0, 5] []))))))))))))))
  have hr : V [6, 5, 7, 1, 4, 0, 12] = V [6, 5, 7, 1, 4, 0, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3417 : V [1, 3, 0, 6, 4, 5, 3] = V [7, 1, 4, 0, 12] := by
  have h0 : V [2, 3, 2, 8, 2, 0, 7, 1, 4, 0, 12] = V [3, 4, 3, 2, 0, 6, 4, 5, 3] :=
    overlap torus146 torus3333 [3, 4, 3, 2] [0, 7, 1, 4, 0, 12] (by decide)
  have hl : V [2, 3, 2, 8, 2, 0, 7, 1, 4, 0, 12] = V [7, 1, 4, 0, 12] :=
    ((in_context torus1436 [] [8, 2, 0, 7, 1, 4, 0, 12]).trans ((in_context torus8 [1, 2] [2, 0, 7, 1, 4, 0, 12]).trans ((in_context torus2 [1] [0, 7, 1, 4, 0, 12]).trans (in_context torus1 [] [7, 1, 4, 0, 12]))))
  have hr : V [3, 4, 3, 2, 0, 6, 4, 5, 3] = V [1, 3, 0, 6, 4, 5, 3] :=
    ((in_context torus1442 [] [2, 0, 6, 4, 5, 3]).trans ((in_context torus1446 [] [2, 0, 6, 4, 5, 3]).trans (in_context torus2 [1, 3] [0, 6, 4, 5, 3])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3419 : V [0, 7, 1, 4, 6, 5, 7] = V [3, 0, 6, 1, 11] := by
  have h0 : V [3, 0, 6, 4, 11, 7, 1] = V [0, 7, 1, 4, 0, 6, 0, 7, 8] :=
    overlap torus3334 torus1479 [0, 7, 1, 4, 0, 6] [7, 1] (by decide)
  have hl : V [3, 0, 6, 4, 11, 7, 1] = V [3, 0, 6, 1, 11] :=
    ((in_context torus77 [3, 0, 6, 4] [1]).trans ((in_context torus4 [3, 0, 6] [11, 1]).trans (in_context torus92 [3, 0, 6] [])))
  have hr : V [0, 7, 1, 4, 0, 6, 0, 7, 8] = V [0, 7, 1, 4, 6, 5, 7] :=
    ((in_context torus1574 [0, 7, 1, 4, 0] []).trans (in_context torus0 [0, 7, 1, 4] [6, 5, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3422 : V [8, 3, 1, 7, 0, 4, 1] = V [2, 7, 1, 5, 11] := by
  have h0 : V [2, 7, 2, 1, 6, 6, 0, 2, 1, 5, 11] = V [3, 4, 5, 6, 7, 2, 0, 4, 1] :=
    overlap torus1764 torus3339 [3, 4, 5, 6] [6, 0, 2, 1, 5, 11] (by decide)
  have hl : V [2, 7, 2, 1, 6, 6, 0, 2, 1, 5, 11] = V [2, 7, 1, 5, 11] :=
    ((in_context torus6 [2, 7, 2, 1] [0, 2, 1, 5, 11]).trans ((in_context torus1 [2, 7, 2] [2, 1, 5, 11]).trans (in_context torus2 [2, 7] [1, 5, 11])))
  have hr : V [3, 4, 5, 6, 7, 2, 0, 4, 1] = V [8, 3, 1, 7, 0, 4, 1] :=
    ((in_context torus1783 [3] [0, 4, 1]).trans (in_context torus3 [] [8, 3, 1, 7, 0, 4, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3429 : V [3, 5, 0, 7, 1, 4, 12] = V [4, 2, 0, 5, 1] := by
  have h0 : V [2, 7, 1, 7, 4, 1, 4, 2, 3] = V [3, 5, 0, 7, 1, 4, 12] :=
    overlap torus2095 torus3378 [3, 5] [1, 4, 2, 3] (by decide)
  have hl : V [2, 7, 1, 7, 4, 1, 4, 2, 3] = V [4, 2, 0, 5, 1] :=
    ((in_context torus2065 [2, 7, 1] [3]).trans ((in_context torus1890 [2, 7, 1] []).trans (in_context torus1745 [] [1])))
  have hr : V [3, 5, 0, 7, 1, 4, 12] = V [3, 5, 0, 7, 1, 4, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3441 : V [1, 3, 0, 6, 1, 4, 2] = V [7, 1, 4, 6, 12] := by
  have h0 : V [7, 1, 4, 0, 12, 1, 3] = V [1, 3, 0, 6, 4, 4, 1, 4, 2] :=
    overlap torus3417 torus1563 [1, 3, 0, 6, 4] [1, 3] (by decide)
  have hl : V [7, 1, 4, 0, 12, 1, 3] = V [7, 1, 4, 6, 12] :=
    ((in_context torus94 [7, 1, 4, 0] [3]).trans ((in_context torus0 [7, 1, 4] [12, 3]).trans (in_context torus54 [7, 1, 4] [])))
  have hr : V [1, 3, 0, 6, 4, 4, 1, 4, 2] = V [1, 3, 0, 6, 1, 4, 2] :=
    (in_context torus4 [1, 3, 0, 6] [1, 4, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3450 : V [8, 0, 3, 4, 2, 3] = V [2, 0, 0, 3, 4, 2] := by
  have h0 : V [2, 0, 2, 2, 3, 2, 3, 2] = V [8, 2, 2, 3, 2, 3, 2, 3] :=
    overlap torus1429 torus160 [8, 2] [2, 3, 2, 3, 2] (by decide)
  have hl : V [2, 0, 2, 2, 3, 2, 3, 2] = V [2, 0, 0, 3, 4, 2] :=
    ((in_context torus2 [2, 0] [3, 2, 3, 2]).trans (in_context torus1439 [2, 0] [2]))
  have hr : V [8, 2, 2, 3, 2, 3, 2, 3] = V [8, 0, 3, 4, 2, 3] :=
    ((in_context torus2 [8] [3, 2, 3, 2, 3]).trans (in_context torus1439 [8] [2, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3464 : V [1, 3, 2, 0, 4, 5] = V [0, 4, 5, 1, 3, 2] := by
  have h0 : V [3, 4, 3, 4, 3, 4] = V [4, 2, 3, 0, 4, 3] :=
    inclusion torus161 torus1442 [4] [4, 3] (by decide)
  have hl : V [3, 4, 3, 4, 3, 4] = V [1, 3, 2, 0, 4, 5] :=
    ((in_context torus1442 [] [4, 3, 4]).trans ((in_context torus1446 [] [4, 3, 4]).trans (in_context torus1448 [1, 3, 2] [])))
  have hr : V [4, 2, 3, 0, 4, 3] = V [0, 4, 5, 1, 3, 2] :=
    ((in_context torus1446 [4] [4, 3]).trans ((in_context torus1554 [] [4, 3]).trans ((in_context torus1442 [0, 4, 5] []).trans (in_context torus1446 [0, 4, 5] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3470 : V [1, 3, 2, 4, 3, 0] = V [0, 4, 5, 3, 5, 4] := by
  have h0 : V [3, 4, 3, 4, 3, 4, 4, 0] = V [4, 3, 4, 3, 4, 1, 4, 3] :=
    overlap torus161 torus1455 [4, 3, 4, 3, 4] [4, 0] (by decide)
  have hl : V [3, 4, 3, 4, 3, 4, 4, 0] = V [1, 3, 2, 4, 3, 0] :=
    ((in_context torus1442 [] [4, 3, 4, 4, 0]).trans ((in_context torus1446 [] [4, 3, 4, 4, 0]).trans ((in_context torus1448 [1, 3, 2] [4, 0]).trans ((in_context torus1451 [1, 3, 2, 0] [0]).trans (in_context torus1447 [1, 3, 2] [0])))))
  have hr : V [4, 3, 4, 3, 4, 1, 4, 3] = V [0, 4, 5, 3, 5, 4] :=
    ((in_context torus1448 [] [3, 4, 1, 4, 3]).trans (in_context torus1454 [0, 4, 5, 3] []))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3480 : V [6, 0, 0, 7, 8, 6] = V [5, 0, 7, 8, 6, 7] := by
  have h0 : V [6, 0, 7, 6, 7, 6] = V [5, 6, 6, 7, 6, 7, 6, 7] :=
    overlap torus1468 torus164 [5, 6] [7, 6, 7, 6] (by decide)
  have hl : V [6, 0, 7, 6, 7, 6] = V [6, 0, 0, 7, 8, 6] :=
    (in_context torus1475 [6, 0] [6])
  have hr : V [5, 6, 6, 7, 6, 7, 6, 7] = V [5, 0, 7, 8, 6, 7] :=
    ((in_context torus6 [5] [7, 6, 7, 6, 7]).trans (in_context torus1475 [5] [6, 7]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3485 : V [1, 5, 4, 6, 5, 0] = V [0, 6, 7, 5, 7, 6] := by
  have h0 : V [5, 6, 5, 6, 5, 6, 6, 0] = V [6, 5, 6, 5, 6, 1, 6, 5] :=
    overlap torus163 torus1473 [6, 5, 6, 5, 6] [6, 0] (by decide)
  have hl : V [5, 6, 5, 6, 5, 6, 6, 0] = V [1, 5, 4, 6, 5, 0] :=
    ((in_context torus1460 [] [6, 5, 6, 6, 0]).trans ((in_context torus1464 [] [6, 5, 6, 6, 0]).trans ((in_context torus1466 [1, 5, 4] [6, 0]).trans ((in_context torus1469 [1, 5, 4, 0] [0]).trans (in_context torus1465 [1, 5, 4] [0])))))
  have hr : V [6, 5, 6, 5, 6, 1, 6, 5] = V [0, 6, 7, 5, 7, 6] :=
    ((in_context torus1466 [] [5, 6, 1, 6, 5]).trans (in_context torus1472 [0, 6, 7, 5] []))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3588 : V [7, 1, 7, 4, 1, 4] = V [3, 8, 0, 4, 2, 3] := by
  have h0 : V [7, 1, 7, 4, 1, 4] = V [8, 7, 5, 1, 5, 3] :=
    overlap torus1480 torus1568 [8, 7] [4, 1, 4] (by decide)
  have hl : V [7, 1, 7, 4, 1, 4] = V [7, 1, 7, 4, 1, 4] :=
    rfl
  have hr : V [8, 7, 5, 1, 5, 3] = V [3, 8, 0, 4, 2, 3] :=
    ((in_context torus1576 [8] [3]).trans ((in_context torus1584 [] [4, 3]).trans (in_context torus1989 [] [3])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3689 : V [2, 6, 1, 6, 3, 5] = V [0, 2, 3, 4, 2, 0] := by
  have h0 : V [2, 8, 7, 1, 7, 5, 3, 5] = V [0, 2, 3, 4, 2, 0] :=
    overlap torus1433 torus1656 [0, 2, 3] [7, 1, 7, 5, 3, 5] (by decide)
  have hl : V [2, 8, 7, 1, 7, 5, 3, 5] = V [2, 6, 1, 6, 3, 5] :=
    ((in_context torus1479 [2] [7, 5, 3, 5]).trans ((in_context torus1478 [2, 0] [5, 3, 5]).trans ((in_context torus1474 [2] [5, 3, 5]).trans (in_context torus1471 [2] [3, 5]))))
  have hr : V [0, 2, 3, 4, 2, 0] = V [0, 2, 3, 4, 2, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus3706 : V [2, 1, 5, 0, 8, 6] = V [1, 6, 0, 8, 3, 12] := by
  have h0 : V [1, 6, 8, 6, 6, 7, 8, 2, 3, 12] = V [2, 7, 2, 2, 8, 7, 6, 5, 4, 3, 2, 8] :=
    overlap torus1665 torus1402 [2, 7, 2] [6, 7, 8, 2, 3, 12] (by decide)
  have hl : V [1, 6, 8, 6, 6, 7, 8, 2, 3, 12] = V [1, 6, 0, 8, 3, 12] :=
    ((in_context torus6 [1, 6, 8] [7, 8, 2, 3, 12]).trans ((in_context torus1484 [1, 6] [2, 3, 12]).trans (in_context torus2 [1, 6, 0, 8] [3, 12])))
  have hr : V [2, 7, 2, 2, 8, 7, 6, 5, 4, 3, 2, 8] = V [2, 1, 5, 0, 8, 6] :=
    ((in_context torus2 [2, 7] [8, 7, 6, 5, 4, 3, 2, 8]).trans ((in_context torus1478 [2] [6, 5, 4, 3, 2, 8]).trans ((in_context torus1482 [2] [6, 5, 4, 3, 2, 8]).trans ((in_context torus6 [2, 1, 7] [5, 4, 3, 2, 8]).trans ((in_context torus246 [2, 1] []).trans ((in_context torus1484 [2, 1, 5] [2, 6]).trans (in_context torus2 [2, 1, 5, 0, 8] [6])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3714 : V [7, 1, 7, 4, 1, 3] = V [3, 8, 0, 4, 3, 0] := by
  have h0 : V [3, 8, 0, 4, 3, 0] = V [7, 1, 7, 5, 4, 1, 3, 2] :=
    overlap torus1678 torus1446 [7, 1, 7, 5, 4] [3, 0] (by decide)
  have hl : V [3, 8, 0, 4, 3, 0] = V [3, 8, 0, 4, 3, 0] :=
    rfl
  have hr : V [7, 1, 7, 5, 4, 1, 3, 2] = V [7, 1, 7, 4, 1, 3] :=
    ((in_context torus1452 [7, 1, 7] [3, 2]).trans ((in_context torus1614 [7, 1, 7, 0] []).trans (in_context torus0 [7, 1, 7] [4, 1, 3])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3719 : V [4, 2, 3, 8, 0, 4] = V [2, 0, 5, 3, 4, 2] := by
  have h0 : V [2, 0, 5, 3, 4, 2] = V [4, 2, 3, 8, 0, 4] :=
    overlap torus1683 torus1678 [4, 2] [4, 2] (by decide)
  have hl : V [2, 0, 5, 3, 4, 2] = V [2, 0, 5, 3, 4, 2] :=
    rfl
  have hr : V [4, 2, 3, 8, 0, 4] = V [4, 2, 3, 8, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3720 : V [1, 2, 0, 5, 3, 4, 2] = V [6, 1, 3, 0, 12] := by
  have h0 : V [6, 1, 3, 0, 12] = V [1, 2, 0, 5, 3, 4, 2] :=
    inclusion torus3397 torus3719 [1] [] (by decide)
  have hl : V [6, 1, 3, 0, 12] = V [6, 1, 3, 0, 12] :=
    rfl
  have hr : V [1, 2, 0, 5, 3, 4, 2] = V [1, 2, 0, 5, 3, 4, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3761 : V [8, 1, 5, 7, 6, 8] = V [6, 8, 7, 2, 1, 6] := by
  have h0 : V [2, 8, 7, 8, 5, 7, 6, 8] = V [6, 8, 2, 2, 7, 2, 1, 6] :=
    overlap torus238 torus1764 [6, 8, 2] [6, 8] (by decide)
  have hl : V [2, 8, 7, 8, 5, 7, 6, 8] = V [8, 1, 5, 7, 6, 8] :=
    ((in_context torus1484 [2] [5, 7, 6, 8]).trans (in_context torus1491 [] [5, 7, 6, 8]))
  have hr : V [6, 8, 2, 2, 7, 2, 1, 6] = V [6, 8, 7, 2, 1, 6] :=
    (in_context torus2 [6, 8] [7, 2, 1, 6])
  exact hl.symm.trans (h0.trans hr)

private theorem torus3762 : V [6, 8, 7, 2, 1, 6, 12] = V [1, 4, 0, 7, 1] := by
  have h0 : V [1, 4, 0, 7, 1] = V [6, 8, 7, 2, 1, 6, 12] :=
    inclusion torus3248 torus3761 [] [12] (by decide)
  have hl : V [1, 4, 0, 7, 1] = V [1, 4, 0, 7, 1] :=
    rfl
  have hr : V [6, 8, 7, 2, 1, 6, 12] = V [6, 8, 7, 2, 1, 6, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3764 : V [6, 8, 7, 2, 1, 6, 0, 12] = V [1, 4, 0, 7] := by
  have h0 : V [1, 4, 0, 7, 1, 0] = V [6, 8, 7, 2, 1, 6, 0, 12] :=
    overlap torus3762 torus93 [6, 8, 7, 2, 1, 6] [0] (by decide)
  have hl : V [1, 4, 0, 7, 1, 0] = V [1, 4, 0, 7] :=
    (in_context torus1 [1, 4, 0, 7] [])
  have hr : V [6, 8, 7, 2, 1, 6, 0, 12] = V [6, 8, 7, 2, 1, 6, 0, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3788 : V [7, 2, 8, 3, 1, 7] = V [2, 1, 6, 8, 7, 2] := by
  have h0 : V [2, 1, 6, 8, 6, 6, 7, 2] = V [7, 2, 3, 3, 8, 3, 1, 7] :=
    overlap torus1767 torus1783 [7, 2, 3] [6, 7, 2] (by decide)
  have hl : V [2, 1, 6, 8, 6, 6, 7, 2] = V [2, 1, 6, 8, 7, 2] :=
    (in_context torus6 [2, 1, 6, 8] [7, 2])
  have hr : V [7, 2, 3, 3, 8, 3, 1, 7] = V [7, 2, 8, 3, 1, 7] :=
    (in_context torus3 [7, 2] [8, 3, 1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3816 : V [4, 5, 6, 8, 0, 2] = V [2, 4, 1, 8, 2, 1] := by
  have h0 : V [2, 4, 1, 8, 3, 0, 2, 3] = V [4, 5, 6, 7, 1, 8, 7, 2] :=
    overlap torus1805 torus1586 [4, 5, 6, 7] [0, 2, 3] (by decide)
  have hl : V [2, 4, 1, 8, 3, 0, 2, 3] = V [2, 4, 1, 8, 2, 1] :=
    (in_context torus1492 [2, 4, 1, 8] [])
  have hr : V [4, 5, 6, 7, 1, 8, 7, 2] = V [4, 5, 6, 8, 0, 2] :=
    (in_context torus1511 [4, 5, 6] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3824 : V [6, 7, 2, 0, 3, 0] = V [5, 3, 5, 1, 2, 3] := by
  have h0 : V [5, 3, 5, 1, 2, 3] = V [6, 7, 2, 0, 3, 0] :=
    overlap torus1820 torus1549 [6, 7] [3] (by decide)
  have hl : V [5, 3, 5, 1, 2, 3] = V [5, 3, 5, 1, 2, 3] :=
    rfl
  have hr : V [6, 7, 2, 0, 3, 0] = V [6, 7, 2, 0, 3, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3828 : V [5, 4, 6, 1, 3, 5] = V [3, 5, 1, 2, 4, 3] := by
  have h0 : V [3, 5, 1, 2, 4, 3] = V [5, 6, 7, 2, 0, 2] :=
    overlap torus1823 torus1429 [5, 6, 7] [3] (by decide)
  have hl : V [3, 5, 1, 2, 4, 3] = V [3, 5, 1, 2, 4, 3] :=
    rfl
  have hr : V [5, 6, 7, 2, 0, 2] = V [5, 4, 6, 1, 3, 5] :=
    (in_context torus1839 [5] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3831 : V [4, 3, 5, 1, 2, 4] = V [2, 4, 1, 8, 3, 2] := by
  have h0 : V [2, 4, 1, 8, 3, 2] = V [4, 3, 5, 1, 2, 4] :=
    overlap torus1805 torus1823 [4] [2] (by decide)
  have hl : V [2, 4, 1, 8, 3, 2] = V [2, 4, 1, 8, 3, 2] :=
    rfl
  have hr : V [4, 3, 5, 1, 2, 4] = V [4, 3, 5, 1, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3840 : V [5, 0, 6, 2, 0, 2] = V [1, 5, 6, 1, 3, 5] := by
  have h0 : V [4, 5, 6, 5, 6, 2, 0, 2] = V [5, 6, 5, 4, 6, 1, 3, 5] :=
    overlap torus116 torus1839 [5, 6, 5] [2, 0, 2] (by decide)
  have hl : V [4, 5, 6, 5, 6, 2, 0, 2] = V [5, 0, 6, 2, 0, 2] :=
    (in_context torus1459 [] [6, 2, 0, 2])
  have hr : V [5, 6, 5, 4, 6, 1, 3, 5] = V [1, 5, 6, 1, 3, 5] :=
    ((in_context torus1460 [] [4, 6, 1, 3, 5]).trans ((in_context torus1464 [] [4, 6, 1, 3, 5]).trans (in_context torus4 [1, 5] [6, 1, 3, 5])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3843 : V [2, 4, 3, 5, 3, 0] = V [0, 5, 3, 5, 4, 6] := by
  have h0 : V [0, 5, 3, 5, 4, 6] = V [2, 4, 2, 2, 3, 5, 3, 0] :=
    overlap torus1741 torus1842 [2, 4, 2] [4, 6] (by decide)
  have hl : V [0, 5, 3, 5, 4, 6] = V [0, 5, 3, 5, 4, 6] :=
    rfl
  have hr : V [2, 4, 2, 2, 3, 5, 3, 0] = V [2, 4, 3, 5, 3, 0] :=
    (in_context torus2 [2, 4] [3, 5, 3, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3846 : V [5, 1, 2, 4, 3, 5] = V [3, 5, 4, 6, 1, 3] := by
  have h0 : V [3, 5, 4, 6, 1, 3] = V [5, 1, 2, 4, 2, 7, 1, 0, 7, 2, 3, 5] :=
    overlap torus1623 torus1846 [5, 1, 2, 4, 2, 7, 1] [4, 6, 1, 3] (by decide)
  have hl : V [3, 5, 4, 6, 1, 3] = V [3, 5, 4, 6, 1, 3] :=
    rfl
  have hr : V [5, 1, 2, 4, 2, 7, 1, 0, 7, 2, 3, 5] = V [5, 1, 2, 4, 3, 5] :=
    ((in_context torus1647 [] [0, 7, 2, 3, 5]).trans ((in_context torus1476 [3, 5] [2, 3, 5]).trans ((in_context torus1823 [3] [3, 5]).trans (in_context torus3 [] [5, 1, 2, 4, 3, 5]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3857 : V [6, 1, 6, 7, 1, 4] = V [0, 7, 2, 3, 4, 6] := by
  have h0 : V [0, 7, 8, 2, 0, 2, 4, 6] = V [7, 6, 5, 7, 1, 4] :=
    overlap torus1475 torus1861 [7, 6] [2, 0, 2, 4, 6] (by decide)
  have hl : V [0, 7, 8, 2, 0, 2, 4, 6] = V [0, 7, 2, 3, 4, 6] :=
    ((in_context torus1430 [0, 7] [2, 4, 6]).trans ((in_context torus1436 [0, 7] [2, 4, 6]).trans ((in_context torus1428 [0, 7, 1] [4, 6]).trans (in_context torus1 [0, 7] [2, 3, 4, 6]))))
  have hr : V [7, 6, 5, 7, 1, 4] = V [6, 1, 6, 7, 1, 4] :=
    (in_context torus1471 [] [7, 1, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3885 : V [7, 2, 3, 4, 6, 4] = V [1, 6, 1, 6, 7, 1] := by
  have h0 : V [6, 7, 0, 5, 7, 1] = V [7, 2, 3, 4, 6, 4] :=
    overlap torus1478 torus1964 [7] [5, 7, 1] (by decide)
  have hl : V [6, 7, 0, 5, 7, 1] = V [1, 6, 1, 6, 7, 1] :=
    ((in_context torus1482 [] [5, 7, 1]).trans (in_context torus1471 [1] [7, 1]))
  have hr : V [7, 2, 3, 4, 6, 4] = V [7, 2, 3, 4, 6, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3909 : V [7, 1, 5, 0, 8, 6] = V [3, 8, 0, 4, 1, 2] := by
  have h0 : V [3, 8, 0, 4, 2, 3, 2, 8] = V [7, 1, 5, 8, 7, 8, 2, 6] :=
    overlap torus1989 torus246 [7, 1] [3, 2, 8] (by decide)
  have hl : V [3, 8, 0, 4, 2, 3, 2, 8] = V [3, 8, 0, 4, 1, 2] :=
    ((in_context torus1436 [3, 8, 0, 4] [8]).trans (in_context torus8 [3, 8, 0, 4, 1, 2] []))
  have hr : V [7, 1, 5, 8, 7, 8, 2, 6] = V [7, 1, 5, 0, 8, 6] :=
    ((in_context torus1484 [7, 1, 5] [2, 6]).trans (in_context torus2 [7, 1, 5, 0, 8] [6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3910 : V [2, 1, 8, 5, 1, 5] = V [0, 2, 8, 0, 4, 2] := by
  have h0 : V [2, 1, 8, 6, 5, 4] = V [0, 2, 3, 3, 8, 0, 4, 2] :=
    overlap torus1722 torus1989 [0, 2, 3] [5, 4] (by decide)
  have hl : V [2, 1, 8, 6, 5, 4] = V [2, 1, 8, 5, 1, 5] :=
    (in_context torus1462 [2, 1, 8] [])
  have hr : V [0, 2, 3, 3, 8, 0, 4, 2] = V [0, 2, 8, 0, 4, 2] :=
    (in_context torus3 [0, 2] [8, 0, 4, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus3918 : V [5, 3, 0, 6, 1, 4] = V [2, 1, 7, 0, 3, 8] := by
  have h0 : V [2, 1, 2, 2, 7, 0, 3, 8] = V [5, 3, 0, 6, 4, 6, 5, 1, 5, 3] :=
    overlap torus2006 torus1984 [5, 3, 0, 6, 4, 6] [2, 7, 0, 3, 8] (by decide)
  have hl : V [2, 1, 2, 2, 7, 0, 3, 8] = V [2, 1, 7, 0, 3, 8] :=
    (in_context torus2 [2, 1] [7, 0, 3, 8])
  have hr : V [5, 3, 0, 6, 4, 6, 5, 1, 5, 3] = V [5, 3, 0, 6, 1, 4] :=
    ((in_context torus1461 [5, 3, 0, 6, 4] [5, 3]).trans ((in_context torus1561 [5, 3, 0, 6] [5, 3]).trans ((in_context torus5 [5, 3, 0, 6, 1, 4, 3] [3]).trans (in_context torus3 [5, 3, 0, 6, 1, 4] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3928 : V [5, 3, 4, 2, 4, 1] = V [1, 2, 4, 2, 3, 8] := by
  have h0 : V [1, 2, 4, 2, 3, 8] = V [5, 3, 5, 5, 4, 2, 4, 1] :=
    overlap torus2020 torus1801 [5, 3, 5] [3, 8] (by decide)
  have hl : V [1, 2, 4, 2, 3, 8] = V [1, 2, 4, 2, 3, 8] :=
    rfl
  have hr : V [5, 3, 5, 5, 4, 2, 4, 1] = V [5, 3, 4, 2, 4, 1] :=
    (in_context torus5 [5, 3] [4, 2, 4, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3950 : V [4, 1, 8, 3, 2, 4] = V [2, 4, 3, 5, 1, 2] := by
  have h0 : V [2, 4, 5, 7, 7, 5, 3, 5, 1, 2] = V [4, 1, 8, 3, 2, 4] :=
    overlap torus2048 torus1821 [4, 1, 8, 3] [7, 5, 3, 5, 1, 2] (by decide)
  have hl : V [2, 4, 5, 7, 7, 5, 3, 5, 1, 2] = V [2, 4, 3, 5, 1, 2] :=
    ((in_context torus7 [2, 4, 5] [5, 3, 5, 1, 2]).trans (in_context torus5 [2, 4] [3, 5, 1, 2]))
  have hr : V [4, 1, 8, 3, 2, 4] = V [4, 1, 8, 3, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus3953 : V [7, 0, 2, 1, 6, 8] = V [4, 6, 1, 3, 0, 5] := by
  have h0 : V [7, 0, 2, 1, 6, 8] = V [6, 7, 8, 2, 3, 4, 5, 6] :=
    overlap torus1477 torus2050 [6, 7, 8] [2, 1, 6, 8] (by decide)
  have hl : V [7, 0, 2, 1, 6, 8] = V [7, 0, 2, 1, 6, 8] :=
    rfl
  have hr : V [6, 7, 8, 2, 3, 4, 5, 6] = V [4, 6, 1, 3, 0, 5] :=
    ((in_context torus1429 [6, 7] [4, 5, 6]).trans ((in_context torus1839 [] [4, 5, 6]).trans ((in_context torus1457 [4, 6, 1, 3] [6]).trans (in_context torus6 [4, 6, 1, 3, 0, 5] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus3997 : V [3, 4, 5, 3, 0, 6] = V [1, 3, 7, 1, 7, 4] := by
  have h0 : V [1, 3, 8, 2, 2, 7, 6, 4] = V [3, 4, 5, 3, 0, 6] :=
    overlap torus1592 torus2093 [3, 4] [2, 7, 6, 4] (by decide)
  have hl : V [1, 3, 8, 2, 2, 7, 6, 4] = V [1, 3, 7, 1, 7, 4] :=
    ((in_context torus2 [1, 3, 8] [7, 6, 4]).trans (in_context torus1480 [1, 3] [4]))
  have hr : V [3, 4, 5, 3, 0, 6] = V [3, 4, 5, 3, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4035 : V [5, 1, 2, 0, 4, 7] = V [3, 6, 0, 8, 1, 5] := by
  have h0 : V [3, 6, 0, 8, 1, 5] = V [5, 1, 2, 4, 2, 2, 3, 4, 5, 7] :=
    overlap torus1648 torus2119 [5, 1, 2, 4, 2] [8, 1, 5] (by decide)
  have hl : V [3, 6, 0, 8, 1, 5] = V [3, 6, 0, 8, 1, 5] :=
    rfl
  have hr : V [5, 1, 2, 4, 2, 2, 3, 4, 5, 7] = V [5, 1, 2, 0, 4, 7] :=
    ((in_context torus2018 [] [2, 3, 4, 5, 7]).trans ((in_context torus1823 [3] [3, 4, 5, 7]).trans ((in_context torus3 [] [5, 1, 2, 4, 3, 4, 5, 7]).trans ((in_context torus1448 [5, 1, 2] [5, 7]).trans (in_context torus5 [5, 1, 2, 0, 4] [7])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4044 : V [4, 6, 5, 7, 5, 0] = V [0, 7, 5, 7, 6, 8] := by
  have h0 : V [0, 7, 5, 7, 8, 8, 6, 8] = V [4, 6, 5, 7, 5, 0] :=
    overlap torus2129 torus2114 [4, 6] [8, 6, 8] (by decide)
  have hl : V [0, 7, 5, 7, 8, 8, 6, 8] = V [0, 7, 5, 7, 6, 8] :=
    (in_context torus8 [0, 7, 5, 7] [6, 8])
  have hr : V [4, 6, 5, 7, 5, 0] = V [4, 6, 5, 7, 5, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4135 : V [1, 6, 5, 7, 1, 6] = V [0, 7, 8, 6, 7, 5] := by
  have h0 : V [8, 7, 7, 8, 1, 6, 5, 7, 1, 6] = V [0, 7, 8, 6, 7, 5] :=
    overlap torus1483 torus2249 [0, 7, 8] [7, 8, 1, 6, 5, 7, 1, 6] (by decide)
  have hl : V [8, 7, 7, 8, 1, 6, 5, 7, 1, 6] = V [1, 6, 5, 7, 1, 6] :=
    ((in_context torus7 [8] [8, 1, 6, 5, 7, 1, 6]).trans (in_context torus8 [] [1, 6, 5, 7, 1, 6]))
  have hr : V [0, 7, 8, 6, 7, 5] = V [0, 7, 8, 6, 7, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4140 : V [1, 7, 6, 8, 7, 2] = V [0, 8, 2, 7, 0, 8] := by
  have h0 : V [7, 0, 8, 1, 6, 8, 5, 1, 5, 3] = V [0, 8, 2, 1, 7, 6, 8, 7, 7, 2] :=
    overlap torus2251 torus1631 [0, 8, 2, 1, 7, 6, 8, 7] [1, 6, 8, 5, 1, 5, 3] (by decide)
  have hl : V [7, 0, 8, 1, 6, 8, 5, 1, 5, 3] = V [1, 7, 6, 8, 7, 2] :=
    ((in_context torus1670 [7, 0, 8, 1] []).trans ((in_context torus1 [7, 0, 8] [2, 7, 2]).trans (in_context torus1582 [] [7, 2])))
  have hr : V [0, 8, 2, 1, 7, 6, 8, 7, 7, 2] = V [0, 8, 2, 7, 0, 8] :=
    ((in_context torus7 [0, 8, 2, 1, 7, 6, 8] [2]).trans (in_context torus1527 [0, 8, 2] []))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4160 : V [4, 5, 1, 3, 2, 4] = V [1, 1, 3, 2, 4, 3] := by
  have h0 : V [1, 5, 4, 4, 5, 1, 3, 2, 4, 3] = V [4, 5, 1, 3, 2, 4] :=
    overlap torus1464 torus2268 [4, 5] [4, 5, 1, 3, 2, 4, 3] (by decide)
  have hl : V [1, 5, 4, 4, 5, 1, 3, 2, 4, 3] = V [1, 1, 3, 2, 4, 3] :=
    ((in_context torus4 [1, 5] [5, 1, 3, 2, 4, 3]).trans (in_context torus5 [1] [1, 3, 2, 4, 3]))
  have hr : V [4, 5, 1, 3, 2, 4] = V [4, 5, 1, 3, 2, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4190 : V [8, 7, 2, 8, 3, 2] = V [0, 0, 2, 3, 8, 0] := by
  have h0 : V [0, 0, 2, 3, 8, 0] = V [8, 7, 0, 2, 3, 1, 8, 1, 8, 7] :=
    overlap torus2282 torus1490 [8, 7, 0, 2, 3, 1, 8] [8, 0] (by decide)
  have hl : V [0, 0, 2, 3, 8, 0] = V [0, 0, 2, 3, 8, 0] :=
    rfl
  have hr : V [8, 7, 0, 2, 3, 1, 8, 1, 8, 7] = V [8, 7, 2, 8, 3, 2] :=
    ((in_context torus1489 [8, 7, 0, 2, 3, 1] [7]).trans ((in_context torus1541 [8, 7, 0, 2] [7, 7]).trans ((in_context torus1517 [8, 7] [2, 7, 7]).trans (in_context torus7 [8, 7, 2, 8, 3, 2] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4199 : V [7, 1, 6, 3, 1, 3] = V [0, 7, 6, 0, 2, 7] := by
  have h0 : V [0, 7, 6, 0, 3, 5, 3, 0, 6, 4, 7, 0] = V [7, 1, 6, 3, 1, 3, 7, 7] :=
    overlap torus2310 torus1850 [7, 1, 6, 3, 1, 3, 7] [3, 5, 3, 0, 6, 4, 7, 0] (by decide)
  have hl : V [0, 7, 6, 0, 3, 5, 3, 0, 6, 4, 7, 0] = V [0, 7, 6, 0, 2, 7] :=
    ((in_context torus2095 [0, 7, 6, 0] [4, 7, 0]).trans ((in_context torus4 [0, 7, 6, 0, 2, 7, 1, 7] [7, 0]).trans ((in_context torus7 [0, 7, 6, 0, 2, 7, 1] [0]).trans (in_context torus1 [0, 7, 6, 0, 2, 7] []))))
  have hr : V [7, 1, 6, 3, 1, 3, 7, 7] = V [7, 1, 6, 3, 1, 3] :=
    (in_context torus7 [7, 1, 6, 3, 1, 3] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4202 : V [8, 1, 6, 0, 2, 7] = V [4, 2, 0, 5, 1, 3] := by
  have h0 : V [8, 1, 6, 0, 3, 5, 3, 0, 6, 4, 7, 0] = V [4, 2, 0, 5, 1, 3, 7, 7] :=
    overlap torus2340 torus1850 [4, 2, 0, 5, 1, 3, 7] [3, 5, 3, 0, 6, 4, 7, 0] (by decide)
  have hl : V [8, 1, 6, 0, 3, 5, 3, 0, 6, 4, 7, 0] = V [8, 1, 6, 0, 2, 7] :=
    ((in_context torus2095 [8, 1, 6, 0] [4, 7, 0]).trans ((in_context torus4 [8, 1, 6, 0, 2, 7, 1, 7] [7, 0]).trans ((in_context torus7 [8, 1, 6, 0, 2, 7, 1] [0]).trans (in_context torus1 [8, 1, 6, 0, 2, 7] []))))
  have hr : V [4, 2, 0, 5, 1, 3, 7, 7] = V [4, 2, 0, 5, 1, 3] :=
    (in_context torus7 [4, 2, 0, 5, 1, 3] [])
  exact hl.symm.trans (h0.trans hr)

private theorem torus4203 : V [5, 1, 2, 0, 4, 6] = V [1, 8, 0, 4, 2, 11] := by
  have h0 : V [1, 3, 8, 11, 2, 1, 2, 7] = V [5, 1, 2, 0, 6, 1, 3, 3, 0, 6, 4, 6] :=
    overlap torus2350 torus2010 [5, 1, 2, 0, 6, 1, 3] [2, 1, 2, 7] (by decide)
  have hl : V [1, 3, 8, 11, 2, 1, 2, 7] = V [1, 8, 0, 4, 2, 11] :=
    ((in_context torus47 [1, 3, 8] [1, 2, 7]).trans ((in_context torus92 [1, 3, 8, 6] [2, 7]).trans ((in_context torus47 [1, 3, 8, 6, 1] [7]).trans ((in_context torus1584 [1, 3] [11, 7]).trans ((in_context torus77 [1, 3, 7, 1, 7, 5] []).trans ((in_context torus1989 [1, 3] [11]).trans (in_context torus3 [1] [8, 0, 4, 2, 11])))))))
  have hr : V [5, 1, 2, 0, 6, 1, 3, 3, 0, 6, 4, 6] = V [5, 1, 2, 0, 4, 6] :=
    ((in_context torus3 [5, 1, 2, 0, 6, 1] [0, 6, 4, 6]).trans ((in_context torus1 [5, 1, 2, 0, 6] [6, 4, 6]).trans (in_context torus6 [5, 1, 2, 0] [4, 6])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4208 : V [3, 0, 7, 1, 4, 6] = V [0, 6, 1, 4, 2, 11] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 7, 1, 4, 6] = V [6, 5, 6, 7, 1, 4, 2, 11] :=
    overlap torus117 torus2360 [6, 5, 6, 7] [1, 3, 0, 7, 1, 4, 6] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 7, 1, 4, 6] = V [3, 0, 7, 1, 4, 6] :=
    ((in_context torus143 [] [1, 3, 0, 7, 1, 4, 6]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 7, 1, 4, 6]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 7, 1, 4, 6]).trans ((in_context torus2 [0] [1, 3, 0, 7, 1, 4, 6]).trans (in_context torus0 [] [3, 0, 7, 1, 4, 6])))))
  have hr : V [6, 5, 6, 7, 1, 4, 2, 11] = V [0, 6, 1, 4, 2, 11] :=
    ((in_context torus1466 [] [7, 1, 4, 2, 11]).trans (in_context torus7 [0, 6] [1, 4, 2, 11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4218 : V [7, 1, 4, 0, 6, 12] = V [1, 3, 0, 6, 4, 5] := by
  have h0 : V [5, 8, 0, 3, 3, 1, 6, 0, 2, 1, 7, 5] = V [7, 1, 4, 0, 6, 2, 2, 12] :=
    overlap torus2373 torus2180 [7, 1, 4, 0, 6, 2] [3, 1, 6, 0, 2, 1, 7, 5] (by decide)
  have hl : V [5, 8, 0, 3, 3, 1, 6, 0, 2, 1, 7, 5] = V [1, 3, 0, 6, 4, 5] :=
    ((in_context torus3 [5, 8, 0] [1, 6, 0, 2, 1, 7, 5]).trans ((in_context torus0 [5, 8] [6, 0, 2, 1, 7, 5]).trans ((in_context torus2036 [] [1, 7, 5]).trans (in_context torus1687 [1] [5]))))
  have hr : V [7, 1, 4, 0, 6, 2, 2, 12] = V [7, 1, 4, 0, 6, 12] :=
    (in_context torus2 [7, 1, 4, 0, 6] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4222 : V [7, 0, 4, 1, 8, 3] = V [0, 3, 1, 8, 6, 11] := by
  have h0 : V [2, 8, 2, 3, 2, 1, 7, 0, 4, 1, 8, 3] = V [3, 2, 3, 4, 1, 8, 6, 11] :=
    overlap torus143 torus2388 [3, 2, 3, 4] [1, 7, 0, 4, 1, 8, 3] (by decide)
  have hl : V [2, 8, 2, 3, 2, 1, 7, 0, 4, 1, 8, 3] = V [7, 0, 4, 1, 8, 3] :=
    ((in_context torus1428 [] [3, 2, 1, 7, 0, 4, 1, 8, 3]).trans ((in_context torus3 [0, 2] [2, 1, 7, 0, 4, 1, 8, 3]).trans ((in_context torus2 [0] [1, 7, 0, 4, 1, 8, 3]).trans (in_context torus0 [] [7, 0, 4, 1, 8, 3]))))
  have hr : V [3, 2, 3, 4, 1, 8, 6, 11] = V [0, 3, 1, 8, 6, 11] :=
    ((in_context torus1439 [] [4, 1, 8, 6, 11]).trans (in_context torus4 [0, 3] [1, 8, 6, 11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4225 : V [7, 1, 4, 6, 5, 12] = V [1, 3, 0, 6, 1, 4] := by
  have h0 : V [5, 7, 6, 8, 8, 1, 4, 0, 7, 1, 5, 3] = V [7, 1, 4, 6, 5, 7, 7, 12] :=
    overlap torus2396 torus2190 [7, 1, 4, 6, 5, 7] [8, 1, 4, 0, 7, 1, 5, 3] (by decide)
  have hl : V [5, 7, 6, 8, 8, 1, 4, 0, 7, 1, 5, 3] = V [1, 3, 0, 6, 1, 4] :=
    ((in_context torus8 [5, 7, 6] [1, 4, 0, 7, 1, 5, 3]).trans ((in_context torus1470 [5] [4, 0, 7, 1, 5, 3]).trans ((in_context torus1566 [] [4, 0, 7, 1, 5, 3]).trans ((in_context torus2105 [1, 5] [1, 5, 3]).trans ((in_context torus2010 [1] [5, 1, 5, 3]).trans ((in_context torus1461 [1, 3, 0, 6, 4] [5, 3]).trans ((in_context torus1561 [1, 3, 0, 6] [5, 3]).trans ((in_context torus5 [1, 3, 0, 6, 1, 4, 3] [3]).trans (in_context torus3 [1, 3, 0, 6, 1, 4] [])))))))))
  have hr : V [7, 1, 4, 6, 5, 7, 7, 12] = V [7, 1, 4, 6, 5, 12] :=
    (in_context torus7 [7, 1, 4, 6, 5] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4228 : V [2, 0, 5, 1, 3, 8] = V [0, 6, 1, 3, 5, 12] := by
  have h0 : V [0, 4, 6, 12, 4, 5, 6, 7] = V [2, 0, 5, 1, 8, 8, 3, 8] :=
    overlap torus2406 torus1681 [2, 0, 5, 1, 8] [4, 5, 6, 7] (by decide)
  have hl : V [0, 4, 6, 12, 4, 5, 6, 7] = V [0, 6, 1, 3, 5, 12] :=
    ((in_context torus60 [0, 4, 6] [5, 6, 7]).trans ((in_context torus66 [0, 4, 6, 7] [6, 7]).trans ((in_context torus72 [0, 4, 6, 7, 8] [7]).trans ((in_context torus78 [0, 4, 6, 7, 8, 2] []).trans ((in_context torus1429 [0, 4, 6, 7] [12]).trans ((in_context torus1839 [0, 4] [12]).trans (in_context torus4 [0] [6, 1, 3, 5, 12])))))))
  have hr : V [2, 0, 5, 1, 8, 8, 3, 8] = V [2, 0, 5, 1, 3, 8] :=
    (in_context torus8 [2, 0, 5, 1] [3, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4229 : V [2, 0, 5, 1, 3, 11] = V [0, 6, 1, 3, 5, 4] := by
  have h0 : V [4, 8, 1, 6, 6, 0, 3, 1, 7, 0, 2, 4] = V [2, 0, 5, 1, 3, 7, 7, 11] :=
    overlap torus2407 torus2383 [2, 0, 5, 1, 3, 7] [6, 0, 3, 1, 7, 0, 2, 4] (by decide)
  have hl : V [4, 8, 1, 6, 6, 0, 3, 1, 7, 0, 2, 4] = V [0, 6, 1, 3, 5, 4] :=
    ((in_context torus6 [4, 8, 1] [0, 3, 1, 7, 0, 2, 4]).trans ((in_context torus1 [4, 8] [3, 1, 7, 0, 2, 4]).trans ((in_context torus2053 [] [0, 2, 4]).trans ((in_context torus1839 [0, 4] [4]).trans (in_context torus4 [0] [6, 1, 3, 5, 4])))))
  have hr : V [2, 0, 5, 1, 3, 7, 7, 11] = V [2, 0, 5, 1, 3, 11] :=
    (in_context torus7 [2, 0, 5, 1, 3] [11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4231 : V [4, 1, 8, 0, 3, 12] = V [1, 7, 0, 3, 8, 2] := by
  have h0 : V [2, 5, 0, 7, 7, 1, 3, 0, 6, 1, 4, 2] = V [4, 1, 8, 0, 3, 6, 6, 12] :=
    overlap torus2377 torus2410 [4, 1, 8, 0, 3, 6] [7, 1, 3, 0, 6, 1, 4, 2] (by decide)
  have hl : V [2, 5, 0, 7, 7, 1, 3, 0, 6, 1, 4, 2] = V [1, 7, 0, 3, 8, 2] :=
    ((in_context torus7 [2, 5, 0] [1, 3, 0, 6, 1, 4, 2]).trans ((in_context torus0 [2, 5] [3, 0, 6, 1, 4, 2]).trans ((in_context torus2094 [] [1, 4, 2]).trans ((in_context torus1568 [1, 2, 7] [2]).trans ((in_context torus1576 [1, 2] [3, 2]).trans ((in_context torus1982 [1, 2] [2]).trans (in_context torus2 [1] [7, 0, 3, 8, 2])))))))
  have hr : V [4, 1, 8, 0, 3, 6, 6, 12] = V [4, 1, 8, 0, 3, 12] :=
    (in_context torus6 [4, 1, 8, 0, 3] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4244 : V [7, 8, 1, 6, 5, 0] = V [1, 1, 6, 5, 8, 7] := by
  have h0 : V [1, 8, 7, 7, 8, 1, 6, 5, 8, 7] = V [7, 8, 1, 6, 5, 0] :=
    overlap torus1490 torus2432 [7, 8] [7, 8, 1, 6, 5, 8, 7] (by decide)
  have hl : V [1, 8, 7, 7, 8, 1, 6, 5, 8, 7] = V [1, 1, 6, 5, 8, 7] :=
    ((in_context torus7 [1, 8] [8, 1, 6, 5, 8, 7]).trans (in_context torus8 [1] [1, 6, 5, 8, 7]))
  have hr : V [7, 8, 1, 6, 5, 0] = V [7, 8, 1, 6, 5, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4255 : V [3, 1, 8, 6, 7, 5] = V [1, 7, 0, 4, 1, 12] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 3, 1, 8, 6, 7, 5] = V [7, 8, 7, 6, 0, 4, 1, 12] :=
    overlap torus129 torus2446 [7, 8, 7, 6] [0, 3, 1, 8, 6, 7, 5] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 3, 1, 8, 6, 7, 5] = V [3, 1, 8, 6, 7, 5] :=
    ((in_context torus146 [] [0, 3, 1, 8, 6, 7, 5]).trans ((in_context torus1436 [] [8, 2, 0, 3, 1, 8, 6, 7, 5]).trans ((in_context torus8 [1, 2] [2, 0, 3, 1, 8, 6, 7, 5]).trans ((in_context torus2 [1] [0, 3, 1, 8, 6, 7, 5]).trans (in_context torus1 [] [3, 1, 8, 6, 7, 5])))))
  have hr : V [7, 8, 7, 6, 0, 4, 1, 12] = V [1, 7, 0, 4, 1, 12] :=
    ((in_context torus1478 [] [6, 0, 4, 1, 12]).trans ((in_context torus1482 [] [6, 0, 4, 1, 12]).trans (in_context torus6 [1, 7] [0, 4, 1, 12])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4267 : V [8, 0, 5, 1, 2, 0] = V [0, 4, 2, 3, 8, 11] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 8, 0, 5, 1, 2, 0] = V [4, 3, 4, 5, 2, 3, 8, 11] :=
    overlap torus100 torus2457 [4, 3, 4, 5] [1, 8, 0, 5, 1, 2, 0] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 8, 0, 5, 1, 2, 0] = V [8, 0, 5, 1, 2, 0] :=
    ((in_context torus143 [] [1, 8, 0, 5, 1, 2, 0]).trans ((in_context torus1428 [] [3, 2, 1, 8, 0, 5, 1, 2, 0]).trans ((in_context torus3 [0, 2] [2, 1, 8, 0, 5, 1, 2, 0]).trans ((in_context torus2 [0] [1, 8, 0, 5, 1, 2, 0]).trans (in_context torus0 [] [8, 0, 5, 1, 2, 0])))))
  have hr : V [4, 3, 4, 5, 2, 3, 8, 11] = V [0, 4, 2, 3, 8, 11] :=
    ((in_context torus1448 [] [5, 2, 3, 8, 11]).trans (in_context torus5 [0, 4] [2, 3, 8, 11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4269 : V [1, 7, 6, 8, 1, 7] = V [0, 8, 2, 7, 8, 6] := by
  have h0 : V [1, 8, 7, 8, 2, 1, 7, 6, 8, 6] = V [7, 8, 7, 8, 1, 7] :=
    overlap torus1490 torus2461 [7, 8] [8, 2, 1, 7, 6, 8, 6] (by decide)
  have hl : V [1, 8, 7, 8, 2, 1, 7, 6, 8, 6] = V [0, 8, 2, 7, 8, 6] :=
    ((in_context torus1484 [1] [2, 1, 7, 6, 8, 6]).trans ((in_context torus1 [] [8, 2, 2, 1, 7, 6, 8, 6]).trans ((in_context torus2 [8] [1, 7, 6, 8, 6]).trans (in_context torus1585 [] [8, 6]))))
  have hr : V [7, 8, 7, 8, 1, 7] = V [1, 7, 6, 8, 1, 7] :=
    ((in_context torus1478 [] [8, 1, 7]).trans (in_context torus1482 [] [8, 1, 7]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4274 : V [2, 4, 3, 5, 1, 2] = V [1, 7, 0, 3, 1, 11] := by
  have h0 : V [1, 7, 0, 11, 7, 6, 5, 6] = V [4, 1, 8, 0, 3, 5, 4, 3, 4, 3, 2, 3] :=
    overlap torus2465 torus120 [4, 1, 8, 0, 3, 5, 4] [7, 6, 5, 6] (by decide)
  have hl : V [1, 7, 0, 11, 7, 6, 5, 6] = V [1, 7, 0, 3, 1, 11] :=
    ((in_context torus77 [1, 7, 0] [6, 5, 6]).trans ((in_context torus71 [1, 7, 0, 4] [5, 6]).trans ((in_context torus65 [1, 7, 0, 4, 3] [6]).trans ((in_context torus1444 [1, 7, 0] [11, 6]).trans ((in_context torus71 [1, 7, 0, 3, 1, 3] []).trans (in_context torus3 [1, 7, 0, 3, 1] [11]))))))
  have hr : V [4, 1, 8, 0, 3, 5, 4, 3, 4, 3, 2, 3] = V [2, 4, 3, 5, 1, 2] :=
    ((in_context torus104 [4, 1, 8, 0, 3] [2, 3]).trans ((in_context torus1442 [4, 1, 8, 0] [4, 3, 2, 2, 3]).trans ((in_context torus1586 [4, 1] [0, 4, 3, 2, 2, 3]).trans ((in_context torus1558 [4, 1] [4, 3, 2, 2, 3]).trans ((in_context torus1444 [4, 1, 8, 3, 2] [2, 3]).trans ((in_context torus1439 [4, 1, 8] [1, 3, 2, 3]).trans ((in_context torus1554 [4, 1, 8, 0, 3] [3]).trans ((in_context torus1550 [4, 1, 8, 0] [3, 3]).trans ((in_context torus0 [4, 1, 8] [3, 2, 4, 3, 3]).trans ((in_context torus3 [4, 1, 8, 3, 2, 4] []).trans (in_context torus3950 [] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4277 : V [8, 2, 7, 0, 3, 1] = V [3, 0, 5, 1, 2, 12] := by
  have h0 : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 3, 1] = V [7, 2, 1, 6, 0, 8, 4, 2, 2, 12] :=
    overlap torus2199 torus2471 [7, 2, 1, 6, 0, 8, 4, 2] [5, 1, 3, 8, 2, 7, 0, 3, 1] (by decide)
  have hl : V [3, 0, 5, 5, 1, 3, 8, 2, 7, 0, 3, 1] = V [8, 2, 7, 0, 3, 1] :=
    ((in_context torus5 [3, 0] [1, 3, 8, 2, 7, 0, 3, 1]).trans ((in_context torus0 [3] [3, 8, 2, 7, 0, 3, 1]).trans (in_context torus3 [] [8, 2, 7, 0, 3, 1])))
  have hr : V [7, 2, 1, 6, 0, 8, 4, 2, 2, 12] = V [3, 0, 5, 1, 2, 12] :=
    (in_context torus2312 [] [2, 12])
  exact hl.symm.trans (h0.trans hr)

private theorem torus4282 : V [3, 5, 4, 6, 1, 3] = V [1, 8, 0, 4, 1, 11] := by
  have h0 : V [1, 8, 0, 11, 8, 7, 6, 7] = V [5, 1, 2, 0, 4, 6, 5, 3, 4, 3, 2, 3] :=
    overlap torus2478 torus129 [5, 1, 2, 0, 4, 6, 5] [8, 7, 6, 7] (by decide)
  have hl : V [1, 8, 0, 11, 8, 7, 6, 7] = V [1, 8, 0, 4, 1, 11] :=
    ((in_context torus83 [1, 8, 0] [7, 6, 7]).trans ((in_context torus77 [1, 8, 0, 5] [6, 7]).trans ((in_context torus71 [1, 8, 0, 5, 4] [7]).trans ((in_context torus1453 [1, 8, 0] [11, 7]).trans ((in_context torus77 [1, 8, 0, 4, 1, 4] []).trans (in_context torus4 [1, 8, 0, 4, 1] [11]))))))
  have hr : V [5, 1, 2, 0, 4, 6, 5, 3, 4, 3, 2, 3] = V [3, 5, 4, 6, 1, 3] :=
    ((in_context torus1606 [5, 1, 2, 0, 4] [3, 2, 3]).trans ((in_context torus1926 [5, 1, 2, 0, 4] [2, 3]).trans ((in_context torus1561 [5, 1, 2, 0] [3, 2, 2, 3]).trans ((in_context torus0 [5, 1, 2] [4, 3, 5, 3, 2, 2, 3]).trans ((in_context torus2 [5, 1, 2, 4, 3, 5, 3] [3]).trans ((in_context torus3 [5, 1, 2, 4, 3, 5] []).trans (in_context torus3846 [] [])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4286 : V [3, 0, 5, 7, 6, 8] = V [0, 6, 1, 2, 0, 11] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 7, 6, 8] = V [6, 5, 6, 7, 1, 2, 0, 11] :=
    overlap torus117 torus2486 [6, 5, 6, 7] [1, 3, 0, 5, 7, 6, 8] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 7, 6, 8] = V [3, 0, 5, 7, 6, 8] :=
    ((in_context torus143 [] [1, 3, 0, 5, 7, 6, 8]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 5, 7, 6, 8]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 5, 7, 6, 8]).trans ((in_context torus2 [0] [1, 3, 0, 5, 7, 6, 8]).trans (in_context torus0 [] [3, 0, 5, 7, 6, 8])))))
  have hr : V [6, 5, 6, 7, 1, 2, 0, 11] = V [0, 6, 1, 2, 0, 11] :=
    ((in_context torus1466 [] [7, 1, 2, 0, 11]).trans (in_context torus7 [0, 6] [1, 2, 0, 11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4298 : V [4, 1, 8, 0, 5, 1] = V [1, 2, 7, 8, 6, 11] := by
  have h0 : V [2, 4, 5, 6, 7, 8, 8, 2, 7, 0, 3, 1, 6, 11] = V [5, 4, 3, 4, 8, 0, 5, 1] :=
    overlap torus299 torus2509 [5, 4, 3, 4, 8] [8, 2, 7, 0, 3, 1, 6, 11] (by decide)
  have hl : V [2, 4, 5, 6, 7, 8, 8, 2, 7, 0, 3, 1, 6, 11] = V [1, 2, 7, 8, 6, 11] :=
    ((in_context torus1805 [2] [8, 2, 7, 0, 3, 1, 6, 11]).trans ((in_context torus2 [] [4, 1, 8, 3, 8, 2, 7, 0, 3, 1, 6, 11]).trans ((in_context torus2074 [] [2, 7, 0, 3, 1, 6, 11]).trans ((in_context torus275 [2] [0, 3, 1, 6, 11]).trans ((in_context torus1444 [2, 3, 8] [3, 0, 3, 1, 6, 11]).trans ((in_context torus3 [2, 3, 8, 3, 1] [0, 3, 1, 6, 11]).trans ((in_context torus1 [2, 3, 8, 3] [3, 1, 6, 11]).trans ((in_context torus3 [2, 3, 8] [1, 6, 11]).trans (in_context torus1591 [] [6, 11])))))))))
  have hr : V [5, 4, 3, 4, 8, 0, 5, 1] = V [4, 1, 8, 0, 5, 1] :=
    ((in_context torus1453 [] [4, 8, 0, 5, 1]).trans (in_context torus4 [4, 1] [8, 0, 5, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4307 : V [8, 6, 7, 5, 0, 11] = V [0, 3, 1, 7, 0, 4] := by
  have h0 : V [11, 0, 6, 1, 3, 0, 7, 12] = V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 2, 3, 8, 0] :=
    overlap torus2389 torus2517 [3, 1, 7, 0, 4, 1, 8, 0, 3, 5] [0, 6, 1, 3, 0, 7, 12] (by decide)
  have hl : V [11, 0, 6, 1, 3, 0, 7, 12] = V [0, 3, 1, 7, 0, 4] :=
    ((in_context torus91 [] [6, 1, 3, 0, 7, 12]).trans ((in_context torus71 [0] [1, 3, 0, 7, 12]).trans ((in_context torus92 [0, 3] [3, 0, 7, 12]).trans ((in_context torus53 [0, 3, 1] [0, 7, 12]).trans ((in_context torus91 [0, 3, 1, 7] [7, 12]).trans ((in_context torus77 [0, 3, 1, 7, 0] [12]).trans (in_context torus24 [0, 3, 1, 7, 0, 4] [])))))))
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 3, 5, 2, 3, 8, 0] = V [8, 6, 7, 5, 0, 11] :=
    ((in_context torus2390 [] [2, 3, 8, 0]).trans ((in_context torus47 [8] [3, 8, 0]).trans ((in_context torus53 [8, 6] [8, 0]).trans ((in_context torus83 [8, 6, 7] [0]).trans (in_context torus91 [8, 6, 7, 5] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4309 : V [4, 0, 8, 1, 5, 12] = V [0, 7, 1, 5, 3, 4] := by
  have h0 : V [4, 0, 6, 12, 3, 6, 5, 4, 5, 2] = V [0, 7, 1, 3, 0, 6, 4, 6, 7, 8, 2, 4] :=
    overlap torus2522 torus175 [0, 7, 1, 3, 0, 6, 4] [3, 6, 5, 4, 5, 2] (by decide)
  have hl : V [4, 0, 6, 12, 3, 6, 5, 4, 5, 2] = V [4, 0, 8, 1, 5, 12] :=
    ((in_context torus54 [4, 0, 6] [6, 5, 4, 5, 2]).trans ((in_context torus6 [4, 0] [12, 6, 5, 4, 5, 2]).trans ((in_context torus72 [4, 0] [5, 4, 5, 2]).trans ((in_context torus66 [4, 0, 2] [4, 5, 2]).trans ((in_context torus60 [4, 0, 2, 8] [5, 2]).trans ((in_context torus66 [4, 0, 2, 8, 7] [2]).trans ((in_context torus1484 [4, 0, 2] [12, 2]).trans ((in_context torus1491 [4, 0] [12, 2]).trans (in_context torus48 [4, 0, 8, 1] [])))))))))
  have hr : V [0, 7, 1, 3, 0, 6, 4, 6, 7, 8, 2, 4] = V [0, 7, 1, 5, 3, 4] :=
    ((in_context torus2132 [0, 7, 1] [8, 2, 4]).trans ((in_context torus1435 [0, 7, 1, 5] [2, 4]).trans (in_context torus2 [0, 7, 1, 5, 3] [4])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4343 : V [4, 1, 8, 0, 3, 6] = V [2, 5, 0, 7, 1, 4] := by
  have h0 : V [2, 4, 5, 6, 8, 8, 5, 7, 1, 4] = V [4, 1, 8, 2, 1, 2, 8, 3, 4, 6] :=
    overlap torus2653 torus1862 [4, 1, 8, 2, 1, 2] [8, 5, 7, 1, 4] (by decide)
  have hl : V [2, 4, 5, 6, 8, 8, 5, 7, 1, 4] = V [2, 5, 0, 7, 1, 4] :=
    ((in_context torus8 [2, 4, 5, 6] [5, 7, 1, 4]).trans (in_context torus1459 [2] [7, 1, 4]))
  have hr : V [4, 1, 8, 2, 1, 2, 8, 3, 4, 6] = V [4, 1, 8, 0, 3, 6] :=
    ((in_context torus1435 [4, 1, 8] [3, 4, 6]).trans ((in_context torus1439 [4, 1, 8] [4, 6]).trans (in_context torus4 [4, 1, 8, 0, 3] [6])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4352 : V [5, 1, 8, 0, 4, 11] = V [1, 2, 0, 4, 6, 5] := by
  have h0 : V [11, 1, 5, 0, 7, 2, 8, 12] = V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 1, 4, 0, 7] :=
    overlap torus2365 torus2712 [7, 1, 4, 0, 8, 1, 5, 0, 7, 2] [1, 5, 0, 7, 2, 8, 12] (by decide)
  have hl : V [11, 1, 5, 0, 7, 2, 8, 12] = V [1, 2, 0, 4, 6, 5] :=
    ((in_context torus92 [] [5, 0, 7, 2, 8, 12]).trans ((in_context torus65 [1] [0, 7, 2, 8, 12]).trans ((in_context torus91 [1, 2] [7, 2, 8, 12]).trans ((in_context torus77 [1, 2, 0] [2, 8, 12]).trans ((in_context torus47 [1, 2, 0, 4] [8, 12]).trans ((in_context torus83 [1, 2, 0, 4, 6] [12]).trans (in_context torus24 [1, 2, 0, 4, 6, 5] [])))))))
  have hr : V [7, 1, 4, 0, 8, 1, 5, 0, 7, 2, 1, 4, 0, 7] = V [5, 1, 8, 0, 4, 11] :=
    ((in_context torus2366 [] [1, 4, 0, 7]).trans ((in_context torus92 [5] [4, 0, 7]).trans ((in_context torus59 [5, 1] [0, 7]).trans ((in_context torus91 [5, 1, 8] [7]).trans (in_context torus77 [5, 1, 8, 0] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4376 : V [4, 1, 2, 7, 8, 11] = V [1, 8, 0, 5, 1, 2] := by
  have h0 : V [4, 2, 3, 8, 3, 3, 1, 11] = V [1, 8, 0, 5, 1, 2] :=
    overlap torus2814 torus2508 [1, 8] [3, 1, 11] (by decide)
  have hl : V [4, 2, 3, 8, 3, 3, 1, 11] = V [4, 1, 2, 7, 8, 11] :=
    ((in_context torus3 [4, 2, 3, 8] [1, 11]).trans (in_context torus1591 [4] [11]))
  have hr : V [1, 8, 0, 5, 1, 2] = V [1, 8, 0, 5, 1, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4378 : V [4, 1, 4, 5, 1, 2] = V [0, 5, 7, 8, 2, 4] := by
  have h0 : V [0, 5, 7, 8, 2, 4] = V [4, 1, 4, 5, 1, 2] :=
    overlap torus2834 torus4 [4, 1, 4, 5, 1, 2] [4] (by decide)
  have hl : V [0, 5, 7, 8, 2, 4] = V [0, 5, 7, 8, 2, 4] :=
    rfl
  have hr : V [4, 1, 4, 5, 1, 2] = V [4, 1, 4, 5, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4379 : V [7, 2, 1, 6, 0, 8] = V [3, 0, 5, 1, 2, 4] := by
  have h0 : V [3, 0, 5, 1, 2, 4] = V [7, 2, 1, 6, 0, 8] :=
    overlap torus7 torus2837 [7] [3, 0, 5, 1, 2, 4] (by decide)
  have hl : V [3, 0, 5, 1, 2, 4] = V [3, 0, 5, 1, 2, 4] :=
    rfl
  have hr : V [7, 2, 1, 6, 0, 8] = V [7, 2, 1, 6, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4380 : V [8, 3, 1, 7, 0, 2] = V [4, 0, 6, 1, 3, 5] := by
  have h0 : V [4, 0, 6, 1, 3, 5] = V [8, 3, 1, 7, 0, 2] :=
    overlap torus8 torus2844 [8] [4, 0, 6, 1, 3, 5] (by decide)
  have hl : V [4, 0, 6, 1, 3, 5] = V [4, 0, 6, 1, 3, 5] :=
    rfl
  have hr : V [8, 3, 1, 7, 0, 2] = V [8, 3, 1, 7, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4391 : V [5, 1, 8, 0, 4, 1] = V [1, 2, 4, 3, 5, 12] := by
  have h0 : V [1, 2, 0, 4, 12, 0, 2, 3] = V [5, 1, 8, 0, 4, 2, 2, 1] :=
    overlap torus2904 torus1492 [5, 1, 8, 0, 4, 2] [0, 2, 3] (by decide)
  have hl : V [1, 2, 0, 4, 12, 0, 2, 3] = V [1, 2, 4, 3, 5, 12] :=
    ((in_context torus93 [1, 2, 0, 4] [2, 3]).trans ((in_context torus48 [1, 2, 0, 4, 0] [3]).trans ((in_context torus54 [1, 2, 0, 4, 0, 5] []).trans ((in_context torus1561 [1, 2, 0] [12]).trans (in_context torus0 [1, 2] [4, 3, 5, 12])))))
  have hr : V [5, 1, 8, 0, 4, 2, 2, 1] = V [5, 1, 8, 0, 4, 1] :=
    (in_context torus2 [5, 1, 8, 0, 4] [1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4397 : V [7, 2, 8, 3, 1, 12] = V [1, 5, 0, 8, 1, 4] := by
  have h0 : V [12, 1, 2, 0, 5, 1, 8, 11] = V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 6, 5, 7, 1] :=
    overlap torus2189 torus2917 [5, 0, 8, 1, 4, 0, 7, 1, 5, 3] [1, 2, 0, 5, 1, 8, 11] (by decide)
  have hl : V [12, 1, 2, 0, 5, 1, 8, 11] = V [1, 5, 0, 8, 1, 4] :=
    ((in_context torus94 [] [2, 0, 5, 1, 8, 11]).trans ((in_context torus48 [1] [0, 5, 1, 8, 11]).trans ((in_context torus93 [1, 5] [5, 1, 8, 11]).trans ((in_context torus66 [1, 5, 0] [1, 8, 11]).trans ((in_context torus94 [1, 5, 0, 8] [8, 11]).trans ((in_context torus84 [1, 5, 0, 8, 1] [11]).trans (in_context torus29 [1, 5, 0, 8, 1, 4] [])))))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 1, 5, 3, 6, 5, 7, 1] = V [7, 2, 8, 3, 1, 12] :=
    ((in_context torus2190 [] [6, 5, 7, 1]).trans ((in_context torus72 [7] [5, 7, 1]).trans ((in_context torus66 [7, 2] [7, 1]).trans ((in_context torus78 [7, 2, 8] [1]).trans (in_context torus94 [7, 2, 8, 3] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4399 : V [8, 0, 3, 5, 4, 12] = V [0, 4, 1, 7, 0, 3] := by
  have h0 : V [0, 4, 2, 4, 3, 1, 3, 8, 2, 7, 0, 3] = V [8, 3, 2, 4, 2, 2, 0, 12] :=
    overlap torus2926 torus2472 [8, 3, 2, 4, 2] [1, 3, 8, 2, 7, 0, 3] (by decide)
  have hl : V [0, 4, 2, 4, 3, 1, 3, 8, 2, 7, 0, 3] = V [0, 4, 1, 7, 0, 3] :=
    ((in_context torus1443 [0, 4, 2] [3, 8, 2, 7, 0, 3]).trans ((in_context torus1544 [0, 4] [3, 8, 2, 7, 0, 3]).trans ((in_context torus3 [0, 4, 1, 2, 8] [8, 2, 7, 0, 3]).trans ((in_context torus8 [0, 4, 1, 2] [2, 7, 0, 3]).trans (in_context torus2 [0, 4, 1] [7, 0, 3])))))
  have hr : V [8, 3, 2, 4, 2, 2, 0, 12] = V [8, 0, 3, 5, 4, 12] :=
    ((in_context torus2 [8, 3, 2, 4] [0, 12]).trans (in_context torus1559 [8] [12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4405 : V [6, 5, 7, 1, 4, 0] = V [4, 1, 2, 0, 5, 11] := by
  have h0 : V [11, 2, 8, 3, 1, 7, 0, 12] = V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 1, 5, 0, 8] :=
    overlap torus2361 torus2966 [6, 1, 3, 0, 7, 1, 4, 0, 6, 8] [2, 8, 3, 1, 7, 0, 12] (by decide)
  have hl : V [11, 2, 8, 3, 1, 7, 0, 12] = V [6, 5, 7, 1, 4, 0] :=
    ((in_context torus47 [] [8, 3, 1, 7, 0, 12]).trans ((in_context torus83 [6] [3, 1, 7, 0, 12]).trans ((in_context torus53 [6, 5] [1, 7, 0, 12]).trans ((in_context torus92 [6, 5, 7] [7, 0, 12]).trans ((in_context torus77 [6, 5, 7, 1] [0, 12]).trans ((in_context torus91 [6, 5, 7, 1, 4] [12]).trans (in_context torus24 [6, 5, 7, 1, 4, 0] [])))))))
  have hr : V [6, 1, 3, 0, 7, 1, 4, 0, 6, 8, 1, 5, 0, 8] = V [4, 1, 2, 0, 5, 11] :=
    ((in_context torus2362 [] [1, 5, 0, 8]).trans ((in_context torus92 [4] [5, 0, 8]).trans ((in_context torus65 [4, 1] [0, 8]).trans ((in_context torus91 [4, 1, 2] [8]).trans (in_context torus83 [4, 1, 2, 0] [])))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4407 : V [7, 1, 4, 0, 8, 1] = V [1, 5, 3, 4, 2, 11] := by
  have h0 : V [5, 6, 11, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [7, 1, 4, 0, 8, 1, 5, 0, 1, 5] :=
    overlap torus2367 torus2968 [7, 1, 4, 0, 8, 1, 5, 0] [2, 8, 3, 1, 7, 0, 4, 1, 12] (by decide)
  have hl : V [5, 6, 11, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [7, 1, 4, 0, 8, 1] :=
    ((in_context torus47 [5, 6] [8, 3, 1, 7, 0, 4, 1, 12]).trans ((in_context torus6 [5] [11, 8, 3, 1, 7, 0, 4, 1, 12]).trans ((in_context torus83 [5] [3, 1, 7, 0, 4, 1, 12]).trans ((in_context torus5 [] [11, 3, 1, 7, 0, 4, 1, 12]).trans ((in_context torus53 [] [1, 7, 0, 4, 1, 12]).trans ((in_context torus92 [7] [7, 0, 4, 1, 12]).trans ((in_context torus77 [7, 1] [0, 4, 1, 12]).trans ((in_context torus91 [7, 1, 4] [4, 1, 12]).trans ((in_context torus59 [7, 1, 4, 0] [1, 12]).trans ((in_context torus92 [7, 1, 4, 0, 8] [12]).trans (in_context torus24 [7, 1, 4, 0, 8, 1] [])))))))))))
  have hr : V [7, 1, 4, 0, 8, 1, 5, 0, 1, 5] = V [1, 5, 3, 4, 2, 11] :=
    ((in_context torus2475 [] [1, 5]).trans ((in_context torus92 [5, 6, 4] [5]).trans ((in_context torus1595 [] [11, 5]).trans (in_context torus65 [1, 5, 3, 4] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4420 : V [5, 0, 8, 6, 7, 5] = V [0, 2, 1, 6, 0, 12] := by
  have h0 : V [0, 2, 1, 12, 2, 3, 4, 3] = V [5, 0, 8, 1, 6, 4, 5, 2, 8, 2, 3, 2] :=
    overlap torus3010 torus143 [5, 0, 8, 1, 6, 4, 5] [2, 3, 4, 3] (by decide)
  have hl : V [0, 2, 1, 12, 2, 3, 4, 3] = V [0, 2, 1, 6, 0, 12] :=
    ((in_context torus48 [0, 2, 1] [3, 4, 3]).trans ((in_context torus54 [0, 2, 1, 5] [4, 3]).trans ((in_context torus60 [0, 2, 1, 5, 6] [3]).trans ((in_context torus54 [0, 2, 1, 5, 6, 7] []).trans (in_context torus1468 [0, 2, 1] [12])))))
  have hr : V [5, 0, 8, 1, 6, 4, 5, 2, 8, 2, 3, 2] = V [5, 0, 8, 6, 7, 5] :=
    ((in_context torus1428 [5, 0, 8, 1, 6, 4, 5] [3, 2]).trans ((in_context torus1464 [5, 0, 8, 1, 6] [2, 3, 3, 2]).trans ((in_context torus1569 [5, 0, 8, 1] [2, 3, 3, 2]).trans ((in_context torus1 [5, 0, 8] [6, 7, 5, 2, 3, 3, 2]).trans ((in_context torus3 [5, 0, 8, 6, 7, 5, 2] [2]).trans (in_context torus2 [5, 0, 8, 6, 7, 5] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4421 : V [8, 1, 6, 4, 5, 3] = V [1, 5, 0, 2, 1, 12] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 8, 1, 6, 4, 5, 3] = V [5, 6, 5, 4, 0, 2, 1, 12] :=
    overlap torus111 torus3010 [5, 6, 5, 4] [0, 8, 1, 6, 4, 5, 3] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 8, 1, 6, 4, 5, 3] = V [8, 1, 6, 4, 5, 3] :=
    ((in_context torus146 [] [0, 8, 1, 6, 4, 5, 3]).trans ((in_context torus1436 [] [8, 2, 0, 8, 1, 6, 4, 5, 3]).trans ((in_context torus8 [1, 2] [2, 0, 8, 1, 6, 4, 5, 3]).trans ((in_context torus2 [1] [0, 8, 1, 6, 4, 5, 3]).trans (in_context torus1 [] [8, 1, 6, 4, 5, 3])))))
  have hr : V [5, 6, 5, 4, 0, 2, 1, 12] = V [1, 5, 0, 2, 1, 12] :=
    ((in_context torus1460 [] [4, 0, 2, 1, 12]).trans ((in_context torus1464 [] [4, 0, 2, 1, 12]).trans (in_context torus4 [1, 5] [0, 2, 1, 12])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4428 : V [4, 0, 6, 8, 7, 2] = V [0, 7, 1, 3, 0, 11] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 4, 0, 6, 8, 7, 2] = V [7, 6, 7, 8, 1, 3, 0, 11] :=
    overlap torus126 torus3018 [7, 6, 7, 8] [1, 4, 0, 6, 8, 7, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 4, 0, 6, 8, 7, 2] = V [4, 0, 6, 8, 7, 2] :=
    ((in_context torus143 [] [1, 4, 0, 6, 8, 7, 2]).trans ((in_context torus1428 [] [3, 2, 1, 4, 0, 6, 8, 7, 2]).trans ((in_context torus3 [0, 2] [2, 1, 4, 0, 6, 8, 7, 2]).trans ((in_context torus2 [0] [1, 4, 0, 6, 8, 7, 2]).trans (in_context torus0 [] [4, 0, 6, 8, 7, 2])))))
  have hr : V [7, 6, 7, 8, 1, 3, 0, 11] = V [0, 7, 1, 3, 0, 11] :=
    ((in_context torus1475 [] [8, 1, 3, 0, 11]).trans (in_context torus8 [0, 7] [1, 3, 0, 11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4431 : V [7, 6, 8, 1, 5, 0] = V [5, 1, 3, 0, 6, 11] := by
  have h0 : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 0, 6, 11] = V [7, 8, 2, 3, 4, 5, 7, 0] :=
    overlap torus216 torus3020 [7, 8, 2, 3, 4] [4, 0, 7, 1, 3, 0, 6, 11] (by decide)
  have hl : V [5, 8, 7, 6, 7, 4, 4, 0, 7, 1, 3, 0, 6, 11] = V [5, 1, 3, 0, 6, 11] :=
    ((in_context torus1480 [5] [7, 4, 4, 0, 7, 1, 3, 0, 6, 11]).trans ((in_context torus7 [5, 7, 1] [4, 4, 0, 7, 1, 3, 0, 6, 11]).trans ((in_context torus4 [5, 7, 1] [0, 7, 1, 3, 0, 6, 11]).trans ((in_context torus1 [5, 7] [7, 1, 3, 0, 6, 11]).trans (in_context torus7 [5] [1, 3, 0, 6, 11])))))
  have hr : V [7, 8, 2, 3, 4, 5, 7, 0] = V [7, 6, 8, 1, 5, 0] :=
    ((in_context torus236 [7] [0]).trans ((in_context torus1484 [7, 6, 2] [5, 0]).trans (in_context torus1491 [7, 6] [5, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4435 : V [5, 0, 2, 1, 6, 12] = V [0, 8, 1, 6, 4, 5] := by
  have h0 : V [0, 8, 1, 6, 4, 5] = V [5, 0, 2, 1, 6, 12] :=
    overlap torus5 torus3074 [5] [0, 8, 1, 6, 4, 5] (by decide)
  have hl : V [0, 8, 1, 6, 4, 5] = V [0, 8, 1, 6, 4, 5] :=
    rfl
  have hr : V [5, 0, 2, 1, 6, 12] = V [5, 0, 2, 1, 6, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4441 : V [6, 1, 5, 2, 1, 2] = V [0, 6, 5, 0, 8, 6] := by
  have h0 : V [0, 6, 5, 0, 8, 6] = V [6, 1, 5, 2, 1, 2] :=
    overlap torus3160 torus6 [6, 1, 5, 2, 1, 2] [6] (by decide)
  have hl : V [0, 6, 5, 0, 8, 6] = V [0, 6, 5, 0, 8, 6] :=
    rfl
  have hr : V [6, 1, 5, 2, 1, 2] = V [6, 1, 5, 2, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4442 : V [8, 0, 4, 1, 7, 11] = V [0, 3, 5, 4, 6, 1] := by
  have h0 : V [3, 8, 7, 6, 5, 4, 4, 3, 5, 1, 2, 0, 6, 1] = V [8, 4, 3, 4, 5, 1, 7, 11] :=
    overlap torus306 torus3165 [8, 4, 3, 4, 5] [4, 3, 5, 1, 2, 0, 6, 1] (by decide)
  have hl : V [3, 8, 7, 6, 5, 4, 4, 3, 5, 1, 2, 0, 6, 1] = V [0, 3, 5, 4, 6, 1] :=
    ((in_context torus1480 [3] [5, 4, 4, 3, 5, 1, 2, 0, 6, 1]).trans ((in_context torus1989 [3] [4, 3, 5, 1, 2, 0, 6, 1]).trans ((in_context torus3 [] [8, 0, 4, 2, 4, 3, 5, 1, 2, 0, 6, 1]).trans ((in_context torus2001 [] [3, 5, 1, 2, 0, 6, 1]).trans ((in_context torus1821 [3] [0, 6, 1]).trans (in_context torus1559 [] [6, 1]))))))
  have hr : V [8, 4, 3, 4, 5, 1, 7, 11] = V [8, 0, 4, 1, 7, 11] :=
    ((in_context torus1448 [8] [5, 1, 7, 11]).trans (in_context torus5 [8, 0, 4] [1, 7, 11]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4445 : V [3, 8, 0, 4, 1, 7] = V [2, 4, 0, 6, 1, 12] := by
  have h0 : V [2, 4, 2, 0, 5, 5, 1, 2, 0, 6, 1, 12] = V [7, 1, 7, 5, 4, 2, 1, 7] :=
    overlap torus2037 torus3174 [7, 1, 7, 5] [5, 1, 2, 0, 6, 1, 12] (by decide)
  have hl : V [2, 4, 2, 0, 5, 5, 1, 2, 0, 6, 1, 12] = V [2, 4, 0, 6, 1, 12] :=
    ((in_context torus5 [2, 4, 2, 0] [1, 2, 0, 6, 1, 12]).trans ((in_context torus0 [2, 4, 2] [2, 0, 6, 1, 12]).trans (in_context torus2 [2, 4] [0, 6, 1, 12])))
  have hr : V [7, 1, 7, 5, 4, 2, 1, 7] = V [3, 8, 0, 4, 1, 7] :=
    (in_context torus1678 [] [1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4455 : V [4, 2, 0, 5, 1, 11] = V [3, 5, 0, 7, 1, 4] := by
  have h0 : V [2, 7, 1, 7, 4, 1, 4, 2, 3, 11] = V [3, 5, 0, 7, 1, 4] :=
    overlap torus2095 torus3191 [3, 5] [1, 4, 2, 3, 11] (by decide)
  have hl : V [2, 7, 1, 7, 4, 1, 4, 2, 3, 11] = V [4, 2, 0, 5, 1, 11] :=
    ((in_context torus2065 [2, 7, 1] [3, 11]).trans ((in_context torus1890 [2, 7, 1] [11]).trans (in_context torus1745 [] [1, 11])))
  have hr : V [3, 5, 0, 7, 1, 4] = V [3, 5, 0, 7, 1, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4456 : V [4, 6, 5, 7, 1, 12] = V [1, 2, 0, 5, 1, 8] := by
  have h0 : V [1, 2, 0, 5, 1, 8] = V [6, 1, 3, 5, 4, 6, 4, 12] :=
    overlap torus3195 torus84 [6, 1, 3, 5, 4, 6] [8] (by decide)
  have hl : V [1, 2, 0, 5, 1, 8] = V [1, 2, 0, 5, 1, 8] :=
    rfl
  have hr : V [6, 1, 3, 5, 4, 6, 4, 12] = V [4, 6, 5, 7, 1, 12] :=
    (in_context torus2915 [] [12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4460 : V [6, 8, 7, 2, 1, 6] = V [1, 4, 0, 7, 1, 11] := by
  have h0 : V [1, 4, 0, 7, 1, 11] = V [8, 1, 5, 7, 6, 8] :=
    overlap torus3248 torus29 [8, 1, 5, 7, 6, 8] [11] (by decide)
  have hl : V [1, 4, 0, 7, 1, 11] = V [1, 4, 0, 7, 1, 11] :=
    rfl
  have hr : V [8, 1, 5, 7, 6, 8] = V [6, 8, 7, 2, 1, 6] :=
    (in_context torus3761 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4461 : V [5, 0, 7, 2, 8, 3] = V [0, 8, 1, 4, 0, 11] := by
  have h0 : V [0, 8, 1, 4, 0, 11] = V [5, 0, 7, 2, 8, 3] :=
    overlap torus5 torus3249 [5] [0, 8, 1, 4, 0, 11] (by decide)
  have hl : V [0, 8, 1, 4, 0, 11] = V [0, 8, 1, 4, 0, 11] :=
    rfl
  have hr : V [5, 0, 7, 2, 8, 3] = V [5, 0, 7, 2, 8, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4477 : V [6, 0, 8, 1, 5, 0] = V [4, 5, 3, 0, 6, 11] := by
  have h0 : V [6, 11, 0, 4, 1, 8, 0, 12] = V [11, 7, 8, 6, 0, 2] :=
    overlap torus47 torus3313 [11] [0, 4, 1, 8, 0, 12] (by decide)
  have hl : V [6, 11, 0, 4, 1, 8, 0, 12] = V [6, 0, 8, 1, 5, 0] :=
    ((in_context torus91 [6] [4, 1, 8, 0, 12]).trans ((in_context torus59 [6, 0] [1, 8, 0, 12]).trans ((in_context torus92 [6, 0, 8] [8, 0, 12]).trans ((in_context torus83 [6, 0, 8, 1] [0, 12]).trans ((in_context torus91 [6, 0, 8, 1, 5] [12]).trans (in_context torus24 [6, 0, 8, 1, 5, 0] []))))))
  have hr : V [11, 7, 8, 6, 0, 2] = V [4, 5, 3, 0, 6, 11] :=
    ((in_context torus77 [] [8, 6, 0, 2]).trans ((in_context torus83 [4] [6, 0, 2]).trans ((in_context torus71 [4, 5] [0, 2]).trans ((in_context torus91 [4, 5, 3] [2]).trans (in_context torus47 [4, 5, 3, 0] [])))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4481 : V [8, 3, 2, 4, 1, 12] = V [1, 6, 0, 2, 1, 5] := by
  have h0 : V [1, 6, 0, 2, 11, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [8, 3, 2, 4, 1, 12] :=
    overlap torus3318 torus2196 [8, 3, 2, 4, 1] [4, 1, 7, 0, 3, 1, 8, 6, 7] (by decide)
  have hl : V [1, 6, 0, 2, 11, 4, 1, 7, 0, 3, 1, 8, 6, 7] = V [1, 6, 0, 2, 1, 5] :=
    ((in_context torus59 [1, 6, 0, 2] [1, 7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus92 [1, 6, 0, 2, 8] [7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus1488 [1, 6, 0] [11, 7, 0, 3, 1, 8, 6, 7]).trans ((in_context torus77 [1, 6, 0, 0, 8, 2] [0, 3, 1, 8, 6, 7]).trans ((in_context torus91 [1, 6, 0, 0, 8, 2, 4] [3, 1, 8, 6, 7]).trans ((in_context torus53 [1, 6, 0, 0, 8, 2, 4, 0] [1, 8, 6, 7]).trans ((in_context torus92 [1, 6, 0, 0, 8, 2, 4, 0, 7] [8, 6, 7]).trans ((in_context torus83 [1, 6, 0, 0, 8, 2, 4, 0, 7, 1] [6, 7]).trans ((in_context torus71 [1, 6, 0, 0, 8, 2, 4, 0, 7, 1, 5] [7]).trans ((in_context torus3200 [1, 6, 0, 0, 8, 2] [7]).trans ((in_context torus1430 [1, 6, 0, 0] [8, 1, 5, 7, 7]).trans ((in_context torus1433 [1, 6, 0] [8, 1, 5, 7, 7]).trans ((in_context torus8 [1, 6, 0, 2] [1, 5, 7, 7]).trans (in_context torus7 [1, 6, 0, 2, 1, 5] []))))))))))))))
  have hr : V [8, 3, 2, 4, 1, 12] = V [8, 3, 2, 4, 1, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4482 : V [5, 0, 7, 1, 4, 6] = V [2, 4, 1, 8, 0, 3] := by
  have h0 : V [4, 5, 7, 6, 6, 0, 7, 2, 3, 4] = V [5, 0, 6, 6, 7, 1, 4, 6] :=
    overlap torus1573 torus3319 [5, 0, 6] [6, 0, 7, 2, 3, 4] (by decide)
  have hl : V [4, 5, 7, 6, 6, 0, 7, 2, 3, 4] = V [2, 4, 1, 8, 0, 3] :=
    ((in_context torus6 [4, 5, 7] [0, 7, 2, 3, 4]).trans ((in_context torus1476 [4, 5] [2, 3, 4]).trans ((in_context torus1805 [] [2, 3, 4]).trans ((in_context torus1439 [2, 4, 1, 8] [4]).trans (in_context torus4 [2, 4, 1, 8, 0, 3] [])))))
  have hr : V [5, 0, 6, 6, 7, 1, 4, 6] = V [5, 0, 7, 1, 4, 6] :=
    (in_context torus6 [5, 0] [7, 1, 4, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4483 : V [8, 0, 4, 2, 3, 11] = V [0, 5, 1, 2, 0, 4] := by
  have h0 : V [8, 0, 4, 2, 3, 11] = V [0, 5, 1, 2, 0, 4] :=
    overlap torus3326 torus29 [0, 5, 1, 2, 0, 4] [11] (by decide)
  have hl : V [8, 0, 4, 2, 3, 11] = V [8, 0, 4, 2, 3, 11] :=
    rfl
  have hr : V [0, 5, 1, 2, 0, 4] = V [0, 5, 1, 2, 0, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4490 : V [6, 8, 7, 2, 1, 12] = V [1, 4, 0, 7, 1, 3] := by
  have h0 : V [1, 4, 0, 7, 1, 3] = V [6, 8, 7, 2, 1, 12] :=
    overlap torus6 torus3342 [6] [1, 4, 0, 7, 1, 3] (by decide)
  have hl : V [1, 4, 0, 7, 1, 3] = V [1, 4, 0, 7, 1, 3] :=
    rfl
  have hr : V [6, 8, 7, 2, 1, 12] = V [6, 8, 7, 2, 1, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4492 : V [2, 1, 6, 0, 3, 12] = V [1, 7, 5, 6, 4, 0] := by
  have h0 : V [2, 1, 6, 0, 3, 12] = V [1, 7, 5, 6, 4, 0] :=
    overlap torus3363 torus24 [1, 7, 5, 6, 4, 0] [12] (by decide)
  have hl : V [2, 1, 6, 0, 3, 12] = V [2, 1, 6, 0, 3, 12] :=
    rfl
  have hr : V [1, 7, 5, 6, 4, 0] = V [1, 7, 5, 6, 4, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4506 : V [5, 4, 6, 1, 3, 0] = V [3, 1, 8, 0, 4, 11] := by
  have h0 : V [11, 8, 7, 2, 1, 6, 0, 12] = V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 1, 4, 0, 7] :=
    overlap torus2351 torus3764 [5, 1, 2, 0, 6, 1, 3, 0, 5, 7] [8, 7, 2, 1, 6, 0, 12] (by decide)
  have hl : V [11, 8, 7, 2, 1, 6, 0, 12] = V [5, 4, 6, 1, 3, 0] :=
    ((in_context torus83 [] [7, 2, 1, 6, 0, 12]).trans ((in_context torus77 [5] [2, 1, 6, 0, 12]).trans ((in_context torus47 [5, 4] [1, 6, 0, 12]).trans ((in_context torus92 [5, 4, 6] [6, 0, 12]).trans ((in_context torus71 [5, 4, 6, 1] [0, 12]).trans ((in_context torus91 [5, 4, 6, 1, 3] [12]).trans (in_context torus24 [5, 4, 6, 1, 3, 0] [])))))))
  have hr : V [5, 1, 2, 0, 6, 1, 3, 0, 5, 7, 1, 4, 0, 7] = V [3, 1, 8, 0, 4, 11] :=
    ((in_context torus2352 [] [1, 4, 0, 7]).trans ((in_context torus92 [3] [4, 0, 7]).trans ((in_context torus59 [3, 1] [0, 7]).trans ((in_context torus91 [3, 1, 8] [7]).trans (in_context torus77 [3, 1, 8, 0] [])))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4577 : V [3, 0, 6, 4, 6, 5, 7] = V [5, 4, 6, 4, 0] := by
  have h0 : V [5, 3, 2, 8, 7, 5, 7] = V [4, 1, 4, 1, 0, 3, 6, 4, 0] :=
    overlap torus1555 torus2059 [4, 1, 4, 1] [8, 7, 5, 7] (by decide)
  have hl : V [5, 3, 2, 8, 7, 5, 7] = V [3, 0, 6, 4, 6, 5, 7] :=
    ((in_context torus1434 [5] [7, 5, 7]).trans (in_context torus2010 [] [5, 7]))
  have hr : V [4, 1, 4, 1, 0, 3, 6, 4, 0] = V [5, 4, 6, 4, 0] :=
    ((in_context torus1 [4, 1, 4] [3, 6, 4, 0]).trans (in_context torus1454 [] [6, 4, 0]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4581 : V [4, 1, 2, 0, 5, 3, 6] = V [7, 5, 0, 8, 1] := by
  have h0 : V [4, 1, 4, 2, 8, 7, 6, 5, 6] = V [7, 5, 0, 8, 3, 4, 3, 2, 3] :=
    overlap torus2080 torus120 [7, 5, 0, 8] [7, 6, 5, 6] (by decide)
  have hl : V [4, 1, 4, 2, 8, 7, 6, 5, 6] = V [4, 1, 2, 0, 5, 3, 6] :=
    ((in_context torus186 [4, 1] [6]).trans ((in_context torus1457 [4, 1, 2] [6, 3, 6]).trans (in_context torus6 [4, 1, 2, 0, 5] [3, 6])))
  have hr : V [7, 5, 0, 8, 3, 4, 3, 2, 3] = V [7, 5, 0, 8, 1] :=
    ((in_context torus146 [7, 5, 0, 8] []).trans ((in_context torus145 [7, 5, 0] [2]).trans ((in_context torus1484 [7, 5, 0, 2] [2, 2]).trans ((in_context torus1491 [7, 5, 0] [2, 2]).trans ((in_context torus1501 [7, 5, 0] [2]).trans (in_context torus1491 [7, 5, 0] []))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4582 : V [3, 1, 3, 7, 1, 7, 4] = V [4, 5, 3, 0, 6] := by
  have h0 : V [3, 1, 3, 8, 7, 6, 4] = V [4, 5, 3, 0, 6] :=
    overlap torus1553 torus2093 [4] [7, 6, 4] (by decide)
  have hl : V [3, 1, 3, 8, 7, 6, 4] = V [3, 1, 3, 7, 1, 7, 4] :=
    (in_context torus1480 [3, 1, 3] [4])
  have hr : V [4, 5, 3, 0, 6] = V [4, 5, 3, 0, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4609 : V [0, 0, 2, 3, 1, 8, 7] = V [8, 7, 0, 2, 3] := by
  have h0 : V [0, 7, 8, 8, 7, 0, 2, 3, 1, 8, 7] = V [8, 7, 0, 2, 3] :=
    overlap torus1479 torus2174 [8, 7] [8, 7, 0, 2, 3, 1, 8, 7] (by decide)
  have hl : V [0, 7, 8, 8, 7, 0, 2, 3, 1, 8, 7] = V [0, 0, 2, 3, 1, 8, 7] :=
    ((in_context torus8 [0, 7] [7, 0, 2, 3, 1, 8, 7]).trans (in_context torus7 [0] [0, 2, 3, 1, 8, 7]))
  have hr : V [8, 7, 0, 2, 3] = V [8, 7, 0, 2, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4611 : V [0, 0, 2, 3, 8, 3, 2] = V [8, 7, 2, 8, 0] := by
  have h0 : V [0, 7, 8, 8, 7, 0, 2, 3, 8, 3, 2] = V [8, 7, 2, 8, 0] :=
    overlap torus1479 torus2256 [8, 7] [8, 7, 0, 2, 3, 8, 3, 2] (by decide)
  have hl : V [0, 7, 8, 8, 7, 0, 2, 3, 8, 3, 2] = V [0, 0, 2, 3, 8, 3, 2] :=
    ((in_context torus8 [0, 7] [7, 0, 2, 3, 8, 3, 2]).trans (in_context torus7 [0] [0, 2, 3, 8, 3, 2]))
  have hr : V [8, 7, 2, 8, 0] = V [8, 7, 2, 8, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4612 : V [0, 0, 2, 3, 8, 0, 2] = V [8, 7, 2, 8, 3] := by
  have h0 : V [0, 7, 8, 8, 7, 0, 2, 3, 8, 0, 2] = V [8, 7, 2, 8, 3] :=
    overlap torus1479 torus2257 [8, 7] [8, 7, 0, 2, 3, 8, 0, 2] (by decide)
  have hl : V [0, 7, 8, 8, 7, 0, 2, 3, 8, 0, 2] = V [0, 0, 2, 3, 8, 0, 2] :=
    ((in_context torus8 [0, 7] [7, 0, 2, 3, 8, 0, 2]).trans (in_context torus7 [0] [0, 2, 3, 8, 0, 2]))
  have hr : V [8, 7, 2, 8, 3] = V [8, 7, 2, 8, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus4614 : V [0, 0, 3, 4, 1, 2, 8] = V [2, 8, 0, 3, 4] := by
  have h0 : V [3, 2, 3, 4, 1, 2, 8, 3, 2] = V [0, 2, 3, 1, 2, 8, 3] :=
    overlap torus1437 torus2266 [0, 2, 3] [3, 4, 1, 2, 8, 3, 2] (by decide)
  have hl : V [3, 2, 3, 4, 1, 2, 8, 3, 2] = V [0, 0, 3, 4, 1, 2, 8] :=
    ((in_context torus1439 [] [4, 1, 2, 8, 3, 2]).trans ((in_context torus4 [0, 3] [1, 2, 8, 3, 2]).trans ((in_context torus1541 [0] [3, 2]).trans (in_context torus1436 [0, 0, 3, 4] []))))
  have hr : V [0, 2, 3, 1, 2, 8, 3] = V [2, 8, 0, 3, 4] :=
    ((in_context torus1541 [0, 2] [3]).trans ((in_context torus1517 [] [2, 3]).trans (in_context torus1439 [2, 8] [])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4636 : V [7, 2, 0, 4, 1, 8, 0] = V [8, 6, 0, 2, 11] := by
  have h0 : V [7, 2, 7, 0, 1, 7, 0, 4, 1, 8, 0] = V [5, 1, 5, 3, 8, 8, 2, 7, 11] :=
    overlap torus1778 torus2477 [5, 1, 5, 3, 8] [1, 7, 0, 4, 1, 8, 0] (by decide)
  have hl : V [7, 2, 7, 0, 1, 7, 0, 4, 1, 8, 0] = V [7, 2, 0, 4, 1, 8, 0] :=
    ((in_context torus0 [7, 2, 7] [7, 0, 4, 1, 8, 0]).trans (in_context torus7 [7, 2] [0, 4, 1, 8, 0]))
  have hr : V [5, 1, 5, 3, 8, 8, 2, 7, 11] = V [8, 6, 0, 2, 11] :=
    ((in_context torus8 [5, 1, 5, 3] [2, 7, 11]).trans (in_context torus1744 [] [11]))
  exact hl.symm.trans (h0.trans hr)

private theorem torus4670 : V [0, 4, 1, 8, 3, 2, 11] = V [7, 0, 3, 1, 8, 14] := by
  have h0 : V [7, 0, 3, 1, 8, 14] = V [0, 4, 1, 8, 3, 2, 11] :=
    overlap torus3072 torus32 [0, 4, 1, 8, 3, 2] [14] (by decide)
  have hl : V [7, 0, 3, 1, 8, 14] = V [7, 0, 3, 1, 8, 14] :=
    rfl
  have hr : V [0, 4, 1, 8, 3, 2, 11] = V [0, 4, 1, 8, 3, 2, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4739 : V [0, 3, 1, 7, 0, 2, 11] = V [6, 0, 2, 7, 8, 14] := by
  have h0 : V [6, 0, 2, 7, 8, 14] = V [0, 3, 1, 7, 0, 2, 11] :=
    overlap torus3335 torus32 [0, 3, 1, 7, 0, 2] [14] (by decide)
  have hl : V [6, 0, 2, 7, 8, 14] = V [6, 0, 2, 7, 8, 14] :=
    rfl
  have hr : V [0, 3, 1, 7, 0, 2, 11] = V [0, 3, 1, 7, 0, 2, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus4841 : V [1, 2, 0, 5, 3, 4, 9] = V [6, 1, 3, 0, 5, 13] := by
  have h0 : V [6, 9, 1, 4, 0, 6, 12] = V [9, 1, 3, 0, 6, 4, 5] :=
    overlap torus75 torus4218 [9] [1, 4, 0, 6, 12] (by decide)
  have hl : V [6, 9, 1, 4, 0, 6, 12] = V [6, 1, 3, 0, 5, 13] :=
    ((in_context torus88 [6] [4, 0, 6, 12]).trans ((in_context torus57 [6, 1] [0, 6, 12]).trans ((in_context torus87 [6, 1, 3] [6, 12]).trans ((in_context torus69 [6, 1, 3, 0] [12]).trans (in_context torus12 [6, 1, 3, 0, 5] [])))))
  have hr : V [9, 1, 3, 0, 6, 4, 5] = V [1, 2, 0, 5, 3, 4, 9] :=
    ((in_context torus88 [] [3, 0, 6, 4, 5]).trans ((in_context torus51 [1] [0, 6, 4, 5]).trans ((in_context torus87 [1, 2] [6, 4, 5]).trans ((in_context torus69 [1, 2, 0] [4, 5]).trans ((in_context torus57 [1, 2, 0, 5] [5]).trans (in_context torus63 [1, 2, 0, 5, 3] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5219 : V [4, 1, 2, 0, 5, 1, 3, 7, 1, 7, 4, 11] = V [7, 0] := by
  have h0 : V [7, 5, 0, 8, 1, 0, 8, 1, 5, 0] = V [4, 1, 2, 0, 5, 3, 4, 5, 3, 0, 6, 11] :=
    overlap torus4581 torus4477 [4, 1, 2, 0, 5, 3] [0, 8, 1, 5, 0] (by decide)
  have hl : V [7, 5, 0, 8, 1, 0, 8, 1, 5, 0] = V [7, 0] :=
    ((in_context torus1 [7, 5, 0, 8] [8, 1, 5, 0]).trans ((in_context torus8 [7, 5, 0] [1, 5, 0]).trans ((in_context torus0 [7, 5] [5, 0]).trans (in_context torus5 [7] [0]))))
  have hr : V [4, 1, 2, 0, 5, 3, 4, 5, 3, 0, 6, 11] = V [4, 1, 2, 0, 5, 1, 3, 7, 1, 7, 4, 11] :=
    (in_context torus3997 [4, 1, 2, 0, 5] [11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5223 : V [0, 3, 2, 0, 5, 1, 2, 1, 2, 3, 1] = V [3, 1, 7] := by
  have h0 : V [3, 1, 2, 7, 6, 6, 7, 2, 7] = V [0, 3, 2, 0, 5, 3, 4, 3, 8, 3, 1] :=
    overlap torus2618 torus1781 [0, 3, 2, 0, 5, 3] [6, 7, 2, 7] (by decide)
  have hl : V [3, 1, 2, 7, 6, 6, 7, 2, 7] = V [3, 1, 7] :=
    ((in_context torus6 [3, 1, 2, 7] [7, 2, 7]).trans ((in_context torus7 [3, 1, 2] [2, 7]).trans (in_context torus2 [3, 1] [7])))
  have hr : V [0, 3, 2, 0, 5, 3, 4, 3, 8, 3, 1] = V [0, 3, 2, 0, 5, 1, 2, 1, 2, 3, 1] :=
    ((in_context torus1442 [0, 3, 2, 0, 5] [8, 3, 1]).trans ((in_context torus1446 [0, 3, 2, 0, 5] [8, 3, 1]).trans (in_context torus1434 [0, 3, 2, 0, 5, 1] [3, 1])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5229 : V [1, 2, 3, 1, 7, 0, 2, 3, 4, 2, 0] = V [2, 0, 5] := by
  have h0 : V [2, 0, 3, 6, 0, 1, 6, 3, 5] = V [1, 2, 3, 1, 7, 0, 2, 3, 4, 2, 0] :=
    overlap torus2838 torus3689 [1, 2, 3, 1, 7] [1, 6, 3, 5] (by decide)
  have hl : V [2, 0, 3, 6, 0, 1, 6, 3, 5] = V [2, 0, 5] :=
    ((in_context torus0 [2, 0, 3, 6] [6, 3, 5]).trans ((in_context torus6 [2, 0, 3] [3, 5]).trans (in_context torus3 [2, 0] [5])))
  have hr : V [1, 2, 3, 1, 7, 0, 2, 3, 4, 2, 0] = V [1, 2, 3, 1, 7, 0, 2, 3, 4, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5230 : V [1, 2, 3, 1, 7, 0, 2, 5, 0, 7, 1, 4] = V [2, 11] := by
  have h0 : V [2, 0, 5, 5, 1, 11] = V [1, 2, 3, 1, 7, 0, 2, 3, 3, 5, 0, 7, 1, 4] :=
    overlap torus5229 torus4455 [1, 2, 3, 1, 7, 0, 2, 3] [5, 1, 11] (by decide)
  have hl : V [2, 0, 5, 5, 1, 11] = V [2, 11] :=
    ((in_context torus5 [2, 0] [1, 11]).trans (in_context torus0 [2] [11]))
  have hr : V [1, 2, 3, 1, 7, 0, 2, 3, 3, 5, 0, 7, 1, 4] = V [1, 2, 3, 1, 7, 0, 2, 5, 0, 7, 1, 4] :=
    (in_context torus3 [1, 2, 3, 1, 7, 0, 2] [5, 0, 7, 1, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5232 : V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2, 1] = V [6, 0, 2] := by
  have h0 : V [6, 8, 6, 5, 5, 6, 8, 0, 2] = V [0, 2, 7, 2, 3, 2, 4, 1, 8, 2, 1] :=
    overlap torus1664 torus3816 [0, 2, 7, 2, 3] [5, 6, 8, 0, 2] (by decide)
  have hl : V [6, 8, 6, 5, 5, 6, 8, 0, 2] = V [6, 0, 2] :=
    ((in_context torus5 [6, 8, 6] [6, 8, 0, 2]).trans ((in_context torus6 [6, 8] [8, 0, 2]).trans (in_context torus8 [6] [0, 2])))
  have hr : V [0, 2, 7, 2, 3, 2, 4, 1, 8, 2, 1] = V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2, 1] :=
    (in_context torus1436 [0, 2, 7] [4, 1, 8, 2, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5248 : V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 3] = V [8, 1, 1] := by
  have h0 : V [8, 1, 6, 11, 2, 1, 12] = V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 3] :=
    overlap torus3373 torus4490 [1, 5, 0, 2, 1] [2, 1, 12] (by decide)
  have hl : V [8, 1, 6, 11, 2, 1, 12] = V [8, 1, 1] :=
    ((in_context torus47 [8, 1, 6] [1, 12]).trans ((in_context torus6 [8, 1] [11, 1, 12]).trans ((in_context torus92 [8, 1] [12]).trans (in_context torus24 [8, 1, 1] []))))
  have hr : V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 3] = V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5279 : V [6, 0, 2, 1, 7, 4, 1, 2, 0, 11] = V [7, 1, 7, 8] := by
  have h0 : V [8, 5, 1, 3, 3, 0, 5, 7, 6, 8] = V [6, 0, 2, 1, 7, 4, 1, 2, 0, 11] :=
    overlap torus2376 torus2486 [6, 0, 2, 1, 7, 4] [3, 0, 5, 7, 6, 8] (by decide)
  have hl : V [8, 5, 1, 3, 3, 0, 5, 7, 6, 8] = V [7, 1, 7, 8] :=
    ((in_context torus3 [8, 5, 1] [0, 5, 7, 6, 8]).trans ((in_context torus1 [8, 5] [5, 7, 6, 8]).trans ((in_context torus5 [8] [7, 6, 8]).trans (in_context torus1480 [] [8]))))
  have hr : V [6, 0, 2, 1, 7, 4, 1, 2, 0, 11] = V [6, 0, 2, 1, 7, 4, 1, 2, 0, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5284 : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 8] = V [4, 1, 8, 1] := by
  have h0 : V [4, 2, 5, 0, 1, 5, 2, 1, 8, 1] = V [1, 8, 3, 8, 7, 8, 6, 0, 2, 8] :=
    overlap torus1792 torus2786 [1, 8, 3, 8, 7] [1, 5, 2, 1, 8, 1] (by decide)
  have hl : V [4, 2, 5, 0, 1, 5, 2, 1, 8, 1] = V [4, 1, 8, 1] :=
    ((in_context torus0 [4, 2, 5] [5, 2, 1, 8, 1]).trans ((in_context torus5 [4, 2] [2, 1, 8, 1]).trans (in_context torus2 [4] [1, 8, 1])))
  have hr : V [1, 8, 3, 8, 7, 8, 6, 0, 2, 8] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 8] :=
    ((in_context torus1484 [1, 8, 3] [6, 0, 2, 8]).trans (in_context torus1543 [1, 8] [6, 0, 2, 8]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5285 : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 2] = V [4, 1] := by
  have h0 : V [4, 1, 8, 1, 0, 8] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 2] :=
    overlap torus5284 torus1485 [1, 8, 2, 1, 2, 1, 6, 0, 2] [0, 8] (by decide)
  have hl : V [4, 1, 8, 1, 0, 8] = V [4, 1] :=
    ((in_context torus1 [4, 1, 8] [8]).trans (in_context torus8 [4, 1] []))
  have hr : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 2] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5287 : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] = V [4, 1, 2] := by
  have h0 : V [4, 1, 2] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] :=
    overlap torus5285 torus2 [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] [2] (by decide)
  have hl : V [4, 1, 2] = V [4, 1, 2] :=
    rfl
  have hr : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5317 : V [0, 7, 1, 4, 0, 6, 0, 8, 0, 2] = V [3, 0, 7, 11] := by
  have h0 : V [3, 0, 6, 4, 11, 7, 2, 3] = V [0, 7, 1, 4, 0, 6, 0, 8, 0, 2] :=
    overlap torus3334 torus1617 [0, 7, 1, 4, 0, 6] [7, 2, 3] (by decide)
  have hl : V [3, 0, 6, 4, 11, 7, 2, 3] = V [3, 0, 7, 11] :=
    ((in_context torus77 [3, 0, 6, 4] [2, 3]).trans ((in_context torus4 [3, 0, 6] [11, 2, 3]).trans ((in_context torus47 [3, 0, 6] [3]).trans ((in_context torus6 [3, 0] [11, 3]).trans (in_context torus53 [3, 0] [])))))
  have hr : V [0, 7, 1, 4, 0, 6, 0, 8, 0, 2] = V [0, 7, 1, 4, 0, 6, 0, 8, 0, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5345 : V [1, 2, 0, 5, 1, 3, 7, 1, 7, 4] = V [4, 7, 0, 12] := by
  have h0 : V [6, 1, 3, 0, 12, 1, 2, 7, 6, 4] = V [1, 2, 0, 5, 3, 4, 5, 3, 0, 6] :=
    overlap torus3720 torus2093 [1, 2, 0, 5, 3, 4] [1, 2, 7, 6, 4] (by decide)
  have hl : V [6, 1, 3, 0, 12, 1, 2, 7, 6, 4] = V [4, 7, 0, 12] :=
    ((in_context torus94 [6, 1, 3, 0] [2, 7, 6, 4]).trans ((in_context torus0 [6, 1, 3] [12, 2, 7, 6, 4]).trans ((in_context torus48 [6, 1, 3] [7, 6, 4]).trans ((in_context torus78 [6, 1, 3, 5] [6, 4]).trans ((in_context torus2022 [] [12, 6, 4]).trans ((in_context torus72 [4, 6, 7, 8, 2] [4]).trans ((in_context torus2 [4, 6, 7, 8] [12, 4]).trans ((in_context torus60 [4, 6, 7, 8] []).trans (in_context torus1477 [4] [12])))))))))
  have hr : V [1, 2, 0, 5, 3, 4, 5, 3, 0, 6] = V [1, 2, 0, 5, 1, 3, 7, 1, 7, 4] :=
    (in_context torus3997 [1, 2, 0, 5] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5349 : V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1] = V [8, 1, 1, 3] := by
  have h0 : V [8, 1, 6, 11, 2, 1, 6, 12] = V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1] :=
    overlap torus3373 torus3762 [1, 5, 0, 2, 1] [2, 1, 6, 12] (by decide)
  have hl : V [8, 1, 6, 11, 2, 1, 6, 12] = V [8, 1, 1, 3] :=
    ((in_context torus47 [8, 1, 6] [1, 6, 12]).trans ((in_context torus6 [8, 1] [11, 1, 6, 12]).trans ((in_context torus92 [8, 1] [6, 12]).trans ((in_context torus71 [8, 1, 1] [12]).trans (in_context torus24 [8, 1, 1, 3] [])))))
  have hr : V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1] = V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5384 : V [2, 1, 5, 0, 0, 3, 1, 7, 0, 4] = V [1, 6, 0, 0] := by
  have h0 : V [1, 6, 0, 8, 3, 12, 7, 5, 0, 11] = V [2, 1, 5, 0, 0, 3, 1, 7, 0, 4] :=
    overlap torus3706 torus4307 [2, 1, 5, 0] [7, 5, 0, 11] (by decide)
  have hl : V [1, 6, 0, 8, 3, 12, 7, 5, 0, 11] = V [1, 6, 0, 0] :=
    ((in_context torus78 [1, 6, 0, 8, 3] [5, 0, 11]).trans ((in_context torus3 [1, 6, 0, 8] [12, 5, 0, 11]).trans ((in_context torus66 [1, 6, 0, 8] [0, 11]).trans ((in_context torus8 [1, 6, 0] [12, 0, 11]).trans ((in_context torus93 [1, 6, 0] [11]).trans (in_context torus29 [1, 6, 0, 0] []))))))
  have hr : V [2, 1, 5, 0, 0, 3, 1, 7, 0, 4] = V [2, 1, 5, 0, 0, 3, 1, 7, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5391 : V [3, 0, 7, 1, 1, 2, 0, 5, 1, 8] = V [0, 6, 1, 1] := by
  have h0 : V [0, 6, 1, 4, 2, 11, 5, 7, 1, 12] = V [3, 0, 7, 1, 1, 2, 0, 5, 1, 8] :=
    overlap torus4208 torus4456 [3, 0, 7, 1] [5, 7, 1, 12] (by decide)
  have hl : V [0, 6, 1, 4, 2, 11, 5, 7, 1, 12] = V [0, 6, 1, 1] :=
    ((in_context torus65 [0, 6, 1, 4, 2] [7, 1, 12]).trans ((in_context torus2 [0, 6, 1, 4] [11, 7, 1, 12]).trans ((in_context torus77 [0, 6, 1, 4] [1, 12]).trans ((in_context torus4 [0, 6, 1] [11, 1, 12]).trans ((in_context torus92 [0, 6, 1] [12]).trans (in_context torus24 [0, 6, 1, 1] []))))))
  have hr : V [3, 0, 7, 1, 1, 2, 0, 5, 1, 8] = V [3, 0, 7, 1, 1, 2, 0, 5, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5399 : V [7, 0, 4, 1, 1, 6, 0, 2, 1, 5] = V [0, 3, 1, 1] := by
  have h0 : V [0, 3, 1, 8, 6, 11, 2, 4, 1, 12] = V [7, 0, 4, 1, 1, 6, 0, 2, 1, 5] :=
    overlap torus4222 torus4481 [7, 0, 4, 1] [2, 4, 1, 12] (by decide)
  have hl : V [0, 3, 1, 8, 6, 11, 2, 4, 1, 12] = V [0, 3, 1, 1] :=
    ((in_context torus47 [0, 3, 1, 8, 6] [4, 1, 12]).trans ((in_context torus6 [0, 3, 1, 8] [11, 4, 1, 12]).trans ((in_context torus59 [0, 3, 1, 8] [1, 12]).trans ((in_context torus8 [0, 3, 1] [11, 1, 12]).trans ((in_context torus92 [0, 3, 1] [12]).trans (in_context torus24 [0, 3, 1, 1] []))))))
  have hr : V [7, 0, 4, 1, 1, 6, 0, 2, 1, 5] = V [7, 0, 4, 1, 1, 6, 0, 2, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5404 : V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] = V [6, 0, 2, 0] := by
  have h0 : V [6, 0, 2, 0] = V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] :=
    overlap torus5232 torus1 [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] [0] (by decide)
  have hl : V [6, 0, 2, 0] = V [6, 0, 2, 0] :=
    rfl
  have hr : V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] = V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5543 : V [5, 3, 5, 1, 2, 0, 4, 0, 5] = V [4, 6, 1, 3, 6] := by
  have h0 : V [6, 7, 8, 2, 3, 5, 6] = V [5, 3, 5, 1, 2, 0, 4, 0, 5] :=
    overlap torus2140 torus1603 [5, 3, 5, 1, 2] [3, 5, 6] (by decide)
  have hl : V [6, 7, 8, 2, 3, 5, 6] = V [4, 6, 1, 3, 6] :=
    ((in_context torus196 [] [6]).trans ((in_context torus1471 [4] [6, 3, 6]).trans (in_context torus6 [4, 6, 1] [3, 6])))
  have hr : V [5, 3, 5, 1, 2, 0, 4, 0, 5] = V [5, 3, 5, 1, 2, 0, 4, 0, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5584 : V [7, 0, 3, 1, 8, 1, 6, 1, 5] = V [0, 4, 1, 7, 12] := by
  have h0 : V [0, 4, 1, 12, 4] = V [7, 0, 3, 1, 8, 1, 6, 1, 5] :=
    overlap torus2446 torus1615 [7, 0, 3, 1, 8] [4] (by decide)
  have hl : V [0, 4, 1, 12, 4] = V [0, 4, 1, 7, 12] :=
    (in_context torus60 [0, 4, 1] [])
  have hr : V [7, 0, 3, 1, 8, 1, 6, 1, 5] = V [7, 0, 3, 1, 8, 1, 6, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5603 : V [3, 1, 7, 0, 2, 0, 4, 6, 5] = V [1, 6, 0, 0, 11] := by
  have h0 : V [1, 6, 0, 11, 0] = V [3, 1, 7, 0, 2, 0, 4, 6, 5] :=
    overlap torus2497 torus1564 [3, 1, 7, 0, 2] [0] (by decide)
  have hl : V [1, 6, 0, 11, 0] = V [1, 6, 0, 0, 11] :=
    (in_context torus91 [1, 6, 0] [])
  have hr : V [3, 1, 7, 0, 2, 0, 4, 6, 5] = V [3, 1, 7, 0, 2, 0, 4, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5617 : V [0, 6, 1, 1, 8, 0, 5, 1, 2] = V [3, 0, 7, 1, 1] := by
  have h0 : V [3, 0, 7, 1, 1] = V [0, 6, 1, 4, 2, 3, 8, 1, 11] :=
    overlap torus2502 torus92 [0, 6, 1, 4, 2, 3, 8] [1] (by decide)
  have hl : V [3, 0, 7, 1, 1] = V [3, 0, 7, 1, 1] :=
    rfl
  have hr : V [0, 6, 1, 4, 2, 3, 8, 1, 11] = V [0, 6, 1, 1, 8, 0, 5, 1, 2] :=
    ((in_context torus1591 [0, 6, 1, 4] [11]).trans (in_context torus4376 [0, 6, 1] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5677 : V [6, 0, 2, 1, 7, 4, 1, 2, 0] = V [7, 1, 7, 8, 12] := by
  have h0 : V [8, 7, 2, 12, 6, 3, 5] = V [6, 0, 2, 1, 7, 4, 1, 2, 0] :=
    overlap torus2722 torus2860 [6, 0, 2, 1] [6, 3, 5] (by decide)
  have hl : V [8, 7, 2, 12, 6, 3, 5] = V [7, 1, 7, 8, 12] :=
    ((in_context torus72 [8, 7, 2] [3, 5]).trans ((in_context torus2 [8, 7] [12, 3, 5]).trans ((in_context torus54 [8, 7] [5]).trans ((in_context torus1480 [] [12, 5]).trans (in_context torus66 [7, 1, 7] [])))))
  have hr : V [6, 0, 2, 1, 7, 4, 1, 2, 0] = V [6, 0, 2, 1, 7, 4, 1, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5678 : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 12] = V [4, 1, 2, 0] := by
  have h0 : V [7, 0, 2, 1, 0, 2, 1, 7, 4, 1, 2, 0] = V [4, 6, 1, 3, 0, 5, 8, 7, 1, 7, 8, 12] :=
    overlap torus2451 torus5677 [4, 6, 1, 3, 0, 5, 8] [0, 2, 1, 7, 4, 1, 2, 0] (by decide)
  have hl : V [7, 0, 2, 1, 0, 2, 1, 7, 4, 1, 2, 0] = V [4, 1, 2, 0] :=
    ((in_context torus1 [7, 0, 2] [2, 1, 7, 4, 1, 2, 0]).trans ((in_context torus2 [7, 0] [1, 7, 4, 1, 2, 0]).trans ((in_context torus0 [7] [7, 4, 1, 2, 0]).trans (in_context torus7 [] [4, 1, 2, 0]))))
  have hr : V [4, 6, 1, 3, 0, 5, 8, 7, 1, 7, 8, 12] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 12] :=
    (in_context torus3252 [] [7, 1, 7, 8, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5679 : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1, 12] = V [4, 1, 2] := by
  have h0 : V [4, 1, 2, 0, 1] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1, 12] :=
    overlap torus5678 torus94 [7, 0, 2, 1, 6, 7, 1, 7, 8] [1] (by decide)
  have hl : V [4, 1, 2, 0, 1] = V [4, 1, 2] :=
    (in_context torus0 [4, 1, 2] [])
  have hr : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1, 12] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5680 : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1] = V [4, 1, 2, 11] := by
  have h0 : V [4, 1, 2, 11] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1] :=
    overlap torus5679 torus29 [7, 0, 2, 1, 6, 7, 1, 7, 8, 1] [11] (by decide)
  have hl : V [4, 1, 2, 11] = V [4, 1, 2, 11] :=
    rfl
  have hr : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5794 : V [1, 3, 0, 6, 1, 4, 1, 2, 1] = V [7, 1, 3, 4, 12] := by
  have h0 : V [7, 1, 4, 0, 12, 8, 2] = V [1, 3, 0, 6, 1, 4, 1, 2, 1] :=
    overlap torus3417 torus1946 [1, 3, 0, 6] [8, 2] (by decide)
  have hl : V [7, 1, 4, 0, 12, 8, 2] = V [7, 1, 3, 4, 12] :=
    ((in_context torus84 [7, 1, 4, 0] [2]).trans ((in_context torus1449 [7, 1] [12, 2]).trans ((in_context torus48 [7, 1, 3, 4, 5] []).trans (in_context torus5 [7, 1, 3, 4] [12]))))
  have hr : V [1, 3, 0, 6, 1, 4, 1, 2, 1] = V [1, 3, 0, 6, 1, 4, 1, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5795 : V [0, 7, 1, 4, 0, 6, 0, 8, 0] = V [3, 0, 7, 6, 11] := by
  have h0 : V [3, 0, 6, 1, 11, 2, 8] = V [0, 7, 1, 4, 0, 6, 0, 8, 0] :=
    overlap torus3419 torus2061 [0, 7, 1, 4] [2, 8] (by decide)
  have hl : V [3, 0, 6, 1, 11, 2, 8] = V [3, 0, 7, 6, 11] :=
    ((in_context torus47 [3, 0, 6, 1] [8]).trans ((in_context torus83 [3, 0, 6, 1, 6] []).trans (in_context torus1472 [3, 0] [11])))
  have hr : V [0, 7, 1, 4, 0, 6, 0, 8, 0] = V [0, 7, 1, 4, 0, 6, 0, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5930 : V [6, 7, 8, 1, 5, 3, 4, 2, 11] = V [7, 4, 0, 8, 1] := by
  have h0 : V [7, 0, 1, 4, 0, 8, 1] = V [6, 7, 8, 1, 5, 3, 4, 2, 11] :=
    overlap torus1477 torus4407 [6, 7, 8] [1, 4, 0, 8, 1] (by decide)
  have hl : V [7, 0, 1, 4, 0, 8, 1] = V [7, 4, 0, 8, 1] :=
    (in_context torus0 [7] [4, 0, 8, 1])
  have hr : V [6, 7, 8, 1, 5, 3, 4, 2, 11] = V [6, 7, 8, 1, 5, 3, 4, 2, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus5977 : V [7, 0, 2, 1, 6, 7, 1, 7, 8] = V [4, 1, 2, 0, 11] := by
  have h0 : V [7, 0, 2, 1, 0, 2, 1, 7, 4, 1, 2, 0, 11] = V [4, 6, 1, 3, 0, 5, 8, 7, 1, 7, 8] :=
    overlap torus2451 torus5279 [4, 6, 1, 3, 0, 5, 8] [0, 2, 1, 7, 4, 1, 2, 0, 11] (by decide)
  have hl : V [7, 0, 2, 1, 0, 2, 1, 7, 4, 1, 2, 0, 11] = V [4, 1, 2, 0, 11] :=
    ((in_context torus1 [7, 0, 2] [2, 1, 7, 4, 1, 2, 0, 11]).trans ((in_context torus2 [7, 0] [1, 7, 4, 1, 2, 0, 11]).trans ((in_context torus0 [7] [7, 4, 1, 2, 0, 11]).trans (in_context torus7 [] [4, 1, 2, 0, 11]))))
  have hr : V [4, 6, 1, 3, 0, 5, 8, 7, 1, 7, 8] = V [7, 0, 2, 1, 6, 7, 1, 7, 8] :=
    (in_context torus3252 [] [7, 1, 7, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus6028 : V [7, 0, 3, 1, 8, 1, 6, 1, 11] = V [0, 4, 1, 7, 8] := by
  have h0 : V [0, 4, 1, 7, 12, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [7, 0, 3, 1, 8, 1, 6, 1, 11] :=
    overlap torus5584 torus2351 [7, 0, 3, 1, 8, 1, 6, 1] [1, 2, 0, 6, 1, 3, 0, 5, 7, 6] (by decide)
  have hl : V [0, 4, 1, 7, 12, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [0, 4, 1, 7, 8] :=
    ((in_context torus94 [0, 4, 1, 7] [2, 0, 6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus48 [0, 4, 1, 7, 1] [0, 6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus93 [0, 4, 1, 7, 1, 5] [6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus72 [0, 4, 1, 7, 1, 5, 0] [1, 3, 0, 5, 7, 6]).trans ((in_context torus94 [0, 4, 1, 7, 1, 5, 0, 2] [3, 0, 5, 7, 6]).trans ((in_context torus54 [0, 4, 1, 7, 1, 5, 0, 2, 1] [0, 5, 7, 6]).trans ((in_context torus3352 [0, 4, 1, 7] [0, 5, 7, 6]).trans ((in_context torus1464 [0, 4, 1, 7, 8, 1, 6] [5, 7, 6]).trans ((in_context torus1569 [0, 4, 1, 7, 8, 1] [5, 7, 6]).trans ((in_context torus1 [0, 4, 1, 7, 8] [6, 7, 5, 5, 7, 6]).trans ((in_context torus5 [0, 4, 1, 7, 8, 6, 7] [7, 6]).trans ((in_context torus7 [0, 4, 1, 7, 8, 6] [6]).trans (in_context torus6 [0, 4, 1, 7, 8] [])))))))))))))
  have hr : V [7, 0, 3, 1, 8, 1, 6, 1, 11] = V [7, 0, 3, 1, 8, 1, 6, 1, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus6120 : V [5, 7, 1, 4, 0, 6, 7, 8] = V [1, 7, 6, 2, 1, 6] := by
  have h0 : V [6, 7, 0, 3, 2, 8, 2, 6] = V [7, 8, 2, 3, 4, 5, 6, 8] :=
    overlap torus1478 torus257 [7, 8] [3, 2, 8, 2, 6] (by decide)
  have hl : V [6, 7, 0, 3, 2, 8, 2, 6] = V [1, 7, 6, 2, 1, 6] :=
    ((in_context torus1434 [6, 7, 0] [2, 6]).trans ((in_context torus2 [6, 7, 0, 2, 1] [6]).trans (in_context torus1482 [] [2, 1, 6])))
  have hr : V [7, 8, 2, 3, 4, 5, 6, 8] = V [5, 7, 1, 4, 0, 6, 7, 8] :=
    ((in_context torus1429 [7] [4, 5, 6, 8]).trans ((in_context torus1863 [] [5, 6, 8]).trans (in_context torus1466 [5, 7, 1, 4] [8])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus6385 : V [8, 2, 1, 4, 0, 7, 1, 11] = V [7, 8, 5, 7, 6, 8] := by
  have h0 : V [7, 8, 5, 7, 5, 4, 4, 5, 6, 8] = V [8, 2, 6, 8, 2, 2, 7, 2, 1, 6] :=
    overlap torus241 torus1764 [8, 2, 6, 8, 2] [4, 5, 6, 8] (by decide)
  have hl : V [7, 8, 5, 7, 5, 4, 4, 5, 6, 8] = V [7, 8, 5, 7, 6, 8] :=
    ((in_context torus4 [7, 8, 5, 7, 5] [5, 6, 8]).trans (in_context torus5 [7, 8, 5, 7] [6, 8]))
  have hr : V [8, 2, 6, 8, 2, 2, 7, 2, 1, 6] = V [8, 2, 1, 4, 0, 7, 1, 11] :=
    ((in_context torus2 [8, 2, 6, 8] [7, 2, 1, 6]).trans (in_context torus4460 [8, 2] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7019 : V [6, 4, 6, 1, 3, 0, 6, 0] = V [7, 6, 8, 1, 5, 6] := by
  have h0 : V [7, 8, 3, 0, 3, 5, 7, 6] = V [6, 4, 6, 1, 3, 4, 1, 0, 4, 0, 6, 0] :=
    overlap torus2404 torus1930 [6, 4, 6, 1, 3, 4, 1] [3, 5, 7, 6] (by decide)
  have hl : V [7, 8, 3, 0, 3, 5, 7, 6] = V [7, 6, 8, 1, 5, 6] :=
    ((in_context torus1440 [7, 8] [5, 7, 6]).trans ((in_context torus236 [7] [6]).trans ((in_context torus1484 [7, 6, 2] [5, 6]).trans (in_context torus1491 [7, 6] [5, 6]))))
  have hr : V [6, 4, 6, 1, 3, 4, 1, 0, 4, 0, 6, 0] = V [6, 4, 6, 1, 3, 0, 6, 0] :=
    ((in_context torus1 [6, 4, 6, 1, 3, 4] [4, 0, 6, 0]).trans (in_context torus4 [6, 4, 6, 1, 3] [0, 6, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7073 : V [3, 1, 7, 0, 2, 0, 4, 6] = V [1, 6, 0, 0, 2, 11] := by
  have h0 : V [1, 6, 0, 11, 0, 5] = V [3, 1, 7, 0, 2, 4, 3, 4, 5, 6] :=
    overlap torus2497 torus1458 [3, 1, 7, 0, 2, 4, 3] [0, 5] (by decide)
  have hl : V [1, 6, 0, 11, 0, 5] = V [1, 6, 0, 0, 2, 11] :=
    ((in_context torus91 [1, 6, 0] [5]).trans (in_context torus65 [1, 6, 0, 0] []))
  have hr : V [3, 1, 7, 0, 2, 4, 3, 4, 5, 6] = V [3, 1, 7, 0, 2, 0, 4, 6] :=
    ((in_context torus1448 [3, 1, 7, 0, 2] [5, 6]).trans (in_context torus5 [3, 1, 7, 0, 2, 0, 4] [6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7092 : V [1, 8, 1, 6, 1, 4, 0, 11] = V [2, 3, 1, 6, 0, 3] := by
  have h0 : V [8, 2, 11, 0, 5, 1, 2, 0, 6, 12] = V [3, 1, 7, 0, 4, 1, 8, 0, 8, 2, 7, 0] :=
    overlap torus2391 torus2512 [3, 1, 7, 0, 4, 1, 8, 0] [0, 5, 1, 2, 0, 6, 12] (by decide)
  have hl : V [8, 2, 11, 0, 5, 1, 2, 0, 6, 12] = V [2, 3, 1, 6, 0, 3] :=
    ((in_context torus91 [8, 2] [5, 1, 2, 0, 6, 12]).trans ((in_context torus1430 [] [11, 5, 1, 2, 0, 6, 12]).trans ((in_context torus1436 [] [11, 5, 1, 2, 0, 6, 12]).trans ((in_context torus65 [1, 2, 8] [1, 2, 0, 6, 12]).trans ((in_context torus1428 [1] [11, 1, 2, 0, 6, 12]).trans ((in_context torus1 [] [2, 3, 11, 1, 2, 0, 6, 12]).trans ((in_context torus92 [2, 3] [2, 0, 6, 12]).trans ((in_context torus47 [2, 3, 1] [0, 6, 12]).trans ((in_context torus91 [2, 3, 1, 6] [6, 12]).trans ((in_context torus71 [2, 3, 1, 6, 0] [12]).trans (in_context torus24 [2, 3, 1, 6, 0, 3] [])))))))))))
  have hr : V [3, 1, 7, 0, 4, 1, 8, 0, 8, 2, 7, 0] = V [1, 8, 1, 6, 1, 4, 0, 11] :=
    ((in_context torus2477 [] [8, 2, 7, 0]).trans ((in_context torus83 [8, 2, 7] [2, 7, 0]).trans ((in_context torus47 [8, 2, 7, 5] [7, 0]).trans ((in_context torus2126 [] [11, 7, 0]).trans ((in_context torus77 [1, 8, 1, 6, 1] [0]).trans (in_context torus91 [1, 8, 1, 6, 1, 4] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7112 : V [0, 2, 3, 7, 0, 3, 1, 6] = V [1, 3, 2, 5, 1, 12] := by
  have h0 : V [0, 2, 3, 0, 2, 4, 3, 5, 1, 12] = V [1, 8, 7, 0, 2, 3, 1, 8, 0, 3, 1, 6] :=
    overlap torus2174 torus2527 [1, 8, 7, 0, 2, 3, 1, 8] [0, 2, 4, 3, 5, 1, 12] (by decide)
  have hl : V [0, 2, 3, 0, 2, 4, 3, 5, 1, 12] = V [1, 3, 2, 5, 1, 12] :=
    ((in_context torus1437 [] [2, 4, 3, 5, 1, 12]).trans ((in_context torus2 [3] [4, 3, 5, 1, 12]).trans ((in_context torus1442 [] [5, 1, 12]).trans (in_context torus1446 [] [5, 1, 12]))))
  have hr : V [1, 8, 7, 0, 2, 3, 1, 8, 0, 3, 1, 6] = V [0, 2, 3, 7, 0, 3, 1, 6] :=
    (in_context torus2443 [] [0, 3, 1, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7291 : V [5, 1, 8, 0, 0, 4, 5, 3] = V [1, 2, 0, 4, 0, 12] := by
  have h0 : V [1, 2, 0, 4, 12, 0] = V [5, 1, 8, 0, 4, 1, 3, 2] :=
    overlap torus2904 torus1446 [5, 1, 8, 0, 4] [0] (by decide)
  have hl : V [1, 2, 0, 4, 12, 0] = V [1, 2, 0, 4, 0, 12] :=
    (in_context torus93 [1, 2, 0, 4] [])
  have hr : V [5, 1, 8, 0, 4, 1, 3, 2] = V [5, 1, 8, 0, 0, 4, 5, 3] :=
    (in_context torus1554 [5, 1, 8, 0] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7366 : V [0, 2, 3, 7, 1, 5, 0, 8] = V [2, 3, 1, 7, 0, 12] := by
  have h0 : V [0, 2, 3, 2, 8, 3, 1, 7, 0, 12] = V [1, 8, 7, 0, 2, 3, 1, 8, 1, 5, 0, 8] :=
    overlap torus2174 torus2966 [1, 8, 7, 0, 2, 3, 1, 8] [2, 8, 3, 1, 7, 0, 12] (by decide)
  have hl : V [0, 2, 3, 2, 8, 3, 1, 7, 0, 12] = V [2, 3, 1, 7, 0, 12] :=
    ((in_context torus1433 [] [8, 3, 1, 7, 0, 12]).trans (in_context torus8 [2] [3, 1, 7, 0, 12]))
  have hr : V [1, 8, 7, 0, 2, 3, 1, 8, 1, 5, 0, 8] = V [0, 2, 3, 7, 1, 5, 0, 8] :=
    (in_context torus2443 [] [1, 5, 0, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7367 : V [1, 1, 8, 7, 3, 1, 7, 0, 12] = V [7, 8, 5, 0, 8] := by
  have h0 : V [1, 8, 3, 2, 2, 3, 7, 1, 5, 0, 8] = V [2, 3, 1, 8, 7, 2, 8, 2, 3, 1, 7, 0, 12] :=
    overlap torus2610 torus7366 [2, 3, 1, 8, 7, 2, 8] [2, 3, 7, 1, 5, 0, 8] (by decide)
  have hl : V [1, 8, 3, 2, 2, 3, 7, 1, 5, 0, 8] = V [7, 8, 5, 0, 8] :=
    ((in_context torus2 [1, 8, 3] [3, 7, 1, 5, 0, 8]).trans ((in_context torus3 [1, 8] [7, 1, 5, 0, 8]).trans ((in_context torus1479 [1] [5, 0, 8]).trans (in_context torus1 [] [7, 8, 5, 0, 8]))))
  have hr : V [2, 3, 1, 8, 7, 2, 8, 2, 3, 1, 7, 0, 12] = V [1, 1, 8, 7, 3, 1, 7, 0, 12] :=
    ((in_context torus3092 [] [2, 3, 1, 7, 0, 12]).trans (in_context torus2 [1, 1, 8, 7] [3, 1, 7, 0, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7368 : V [0, 2, 3, 7, 1, 5, 0, 11] = V [2, 3, 1, 7, 0, 4] := by
  have h0 : V [0, 2, 3, 2, 8, 3, 1, 7, 0, 4] = V [1, 8, 7, 0, 2, 3, 1, 8, 1, 5, 0, 11] :=
    overlap torus2174 torus2972 [1, 8, 7, 0, 2, 3, 1, 8] [2, 8, 3, 1, 7, 0, 4] (by decide)
  have hl : V [0, 2, 3, 2, 8, 3, 1, 7, 0, 4] = V [2, 3, 1, 7, 0, 4] :=
    ((in_context torus1433 [] [8, 3, 1, 7, 0, 4]).trans (in_context torus8 [2] [3, 1, 7, 0, 4]))
  have hr : V [1, 8, 7, 0, 2, 3, 1, 8, 1, 5, 0, 11] = V [0, 2, 3, 7, 1, 5, 0, 11] :=
    (in_context torus2443 [] [1, 5, 0, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7369 : V [1, 1, 8, 7, 3, 1, 7, 0, 4] = V [7, 8, 5, 0, 11] := by
  have h0 : V [1, 8, 3, 2, 2, 3, 7, 1, 5, 0, 11] = V [2, 3, 1, 8, 7, 2, 8, 2, 3, 1, 7, 0, 4] :=
    overlap torus2610 torus7368 [2, 3, 1, 8, 7, 2, 8] [2, 3, 7, 1, 5, 0, 11] (by decide)
  have hl : V [1, 8, 3, 2, 2, 3, 7, 1, 5, 0, 11] = V [7, 8, 5, 0, 11] :=
    ((in_context torus2 [1, 8, 3] [3, 7, 1, 5, 0, 11]).trans ((in_context torus3 [1, 8] [7, 1, 5, 0, 11]).trans ((in_context torus1479 [1] [5, 0, 11]).trans (in_context torus1 [] [7, 8, 5, 0, 11]))))
  have hr : V [2, 3, 1, 8, 7, 2, 8, 2, 3, 1, 7, 0, 4] = V [1, 1, 8, 7, 3, 1, 7, 0, 4] :=
    ((in_context torus3092 [] [2, 3, 1, 7, 0, 4]).trans (in_context torus2 [1, 1, 8, 7] [3, 1, 7, 0, 4]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7494 : V [1, 2, 8, 4, 0, 6, 1, 12] = V [2, 8, 0, 4, 1, 7] := by
  have h0 : V [1, 2, 8, 2, 3, 8, 0, 4, 1, 7] = V [0, 3, 4, 1, 2, 8, 0, 3, 0, 6, 1, 12] :=
    overlap torus2156 torus3170 [0, 3, 4, 1, 2, 8, 0, 3] [2, 3, 8, 0, 4, 1, 7] (by decide)
  have hl : V [1, 2, 8, 2, 3, 8, 0, 4, 1, 7] = V [2, 8, 0, 4, 1, 7] :=
    ((in_context torus1428 [1] [3, 8, 0, 4, 1, 7]).trans ((in_context torus1 [] [2, 3, 3, 8, 0, 4, 1, 7]).trans (in_context torus3 [2] [8, 0, 4, 1, 7])))
  have hr : V [0, 3, 4, 1, 2, 8, 0, 3, 0, 6, 1, 12] = V [1, 2, 8, 4, 0, 6, 1, 12] :=
    (in_context torus2413 [] [0, 6, 1, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7573 : V [0, 4, 5, 2, 1, 7, 0, 11] = V [4, 5, 1, 2, 0, 6] := by
  have h0 : V [5, 4, 3, 4, 0, 5, 1, 2, 0, 6] = V [4, 3, 4, 3, 2, 8, 2, 7, 0, 11] :=
    overlap torus105 torus3261 [4, 3, 4, 3, 2] [0, 5, 1, 2, 0, 6] (by decide)
  have hl : V [5, 4, 3, 4, 0, 5, 1, 2, 0, 6] = V [4, 5, 1, 2, 0, 6] :=
    ((in_context torus1453 [] [4, 0, 5, 1, 2, 0, 6]).trans ((in_context torus4 [4, 1] [0, 5, 1, 2, 0, 6]).trans (in_context torus1 [4] [5, 1, 2, 0, 6])))
  have hr : V [4, 3, 4, 3, 2, 8, 2, 7, 0, 11] = V [0, 4, 5, 2, 1, 7, 0, 11] :=
    ((in_context torus1448 [] [3, 2, 8, 2, 7, 0, 11]).trans ((in_context torus1614 [0] [8, 2, 7, 0, 11]).trans ((in_context torus0 [] [4, 1, 3, 8, 2, 7, 0, 11]).trans (in_context torus1925 [] [7, 0, 11]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7592 : V [0, 6, 1, 4, 1, 2, 1, 8] = V [3, 0, 7, 1, 3, 12] := by
  have h0 : V [3, 0, 7, 1, 12, 7] = V [0, 6, 1, 4, 1, 2, 1, 8] :=
    overlap torus3266 torus1611 [0, 6, 1, 4] [7] (by decide)
  have hl : V [3, 0, 7, 1, 12, 7] = V [3, 0, 7, 1, 3, 12] :=
    (in_context torus78 [3, 0, 7, 1] [])
  have hr : V [0, 6, 1, 4, 1, 2, 1, 8] = V [0, 6, 1, 4, 1, 2, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7686 : V [0, 6, 0, 2, 1, 6, 8, 6] = V [6, 7, 1, 4, 6, 5] := by
  have h0 : V [6, 7, 1, 4, 6, 5] = V [0, 6, 0, 2, 1, 6, 8, 6] :=
    overlap torus3319 torus1767 [0, 6, 0] [5] (by decide)
  have hl : V [6, 7, 1, 4, 6, 5] = V [6, 7, 1, 4, 6, 5] :=
    rfl
  have hr : V [0, 6, 0, 2, 1, 6, 8, 6] = V [0, 6, 0, 2, 1, 6, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus7999 : V [0, 2, 3, 7, 0, 3, 8, 2] = V [4, 2, 0, 5, 1, 3] := by
  have h0 : V [4, 2, 0, 5, 1, 3] = V [3, 5, 0, 7, 1, 4, 6, 12] :=
    overlap torus3429 torus54 [3, 5, 0, 7, 1, 4] [3] (by decide)
  have hl : V [4, 2, 0, 5, 1, 3] = V [4, 2, 0, 5, 1, 3] :=
    rfl
  have hr : V [3, 5, 0, 7, 1, 4, 6, 12] = V [0, 2, 3, 7, 0, 3, 8, 2] :=
    ((in_context torus4482 [3] [12]).trans ((in_context torus4231 [3, 2] []).trans (in_context torus1432 [] [7, 0, 3, 8, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8040 : V [1, 8, 7, 3, 4, 1, 2, 8] = V [7, 2, 0, 0, 3, 4] := by
  have h0 : V [7, 8, 2, 0, 3, 4, 2, 3] = V [8, 0, 2, 0, 0, 3, 4, 2] :=
    overlap torus1485 torus3450 [8, 0] [0, 3, 4, 2, 3] (by decide)
  have hl : V [7, 8, 2, 0, 3, 4, 2, 3] = V [7, 2, 0, 0, 3, 4] :=
    ((in_context torus1430 [7] [3, 4, 2, 3]).trans ((in_context torus1436 [7] [3, 4, 2, 3]).trans ((in_context torus1516 [7] [2, 3]).trans (in_context torus1439 [7, 2, 0] []))))
  have hr : V [8, 0, 2, 0, 0, 3, 4, 2] = V [1, 8, 7, 3, 4, 1, 2, 8] :=
    ((in_context torus1587 [] [0, 3, 4, 2]).trans ((in_context torus1544 [7, 8, 3] [2]).trans ((in_context torus1541 [7, 8] [3, 2]).trans ((in_context torus1490 [] [3, 4, 2, 3, 2]).trans (in_context torus1436 [1, 8, 7, 3, 4] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8078 : V [0, 3, 4, 8, 0, 4, 2, 3] = V [2, 1, 7, 0, 3, 8] := by
  have h0 : V [2, 1, 2, 7, 6, 4, 1, 4] = V [3, 2, 3, 8, 0, 4, 2, 3] :=
    overlap torus1866 torus3588 [3, 2] [4, 1, 4] (by decide)
  have hl : V [2, 1, 2, 7, 6, 4, 1, 4] = V [2, 1, 7, 0, 3, 8] :=
    ((in_context torus2093 [] [1, 4]).trans (in_context torus3918 [] []))
  have hr : V [3, 2, 3, 8, 0, 4, 2, 3] = V [0, 3, 4, 8, 0, 4, 2, 3] :=
    (in_context torus1439 [] [8, 0, 4, 2, 3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8159 : V [1, 2, 8, 4, 1, 8, 3, 2] = V [3, 0, 5, 1, 2, 4] := by
  have h0 : V [3, 0, 5, 1, 2, 4] = V [2, 3, 2, 4, 1, 8, 3, 2] :=
    overlap torus1441 torus3831 [2, 3] [5, 1, 2, 4] (by decide)
  have hl : V [3, 0, 5, 1, 2, 4] = V [3, 0, 5, 1, 2, 4] :=
    rfl
  have hr : V [2, 3, 2, 4, 1, 8, 3, 2] = V [1, 2, 8, 4, 1, 8, 3, 2] :=
    (in_context torus1436 [] [4, 1, 8, 3, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8202 : V [5, 6, 1, 2, 4, 2, 3, 8] = V [1, 4, 1, 2, 4, 1] := by
  have h0 : V [4, 5, 0, 3, 4, 2, 4, 1] = V [5, 6, 1, 2, 4, 2, 3, 8] :=
    overlap torus1460 torus3928 [5, 6] [3, 4, 2, 4, 1] (by decide)
  have hl : V [4, 5, 0, 3, 4, 2, 4, 1] = V [1, 4, 1, 2, 4, 1] :=
    ((in_context torus1464 [] [3, 4, 2, 4, 1]).trans ((in_context torus1453 [1] [4, 2, 4, 1]).trans (in_context torus4 [1, 4, 1] [2, 4, 1])))
  have hr : V [5, 6, 1, 2, 4, 2, 3, 8] = V [5, 6, 1, 2, 4, 2, 3, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8529 : V [0, 5, 6, 3, 0, 6, 4, 5] = V [4, 1, 2, 0, 5, 3] := by
  have h0 : V [4, 1, 2, 0, 5, 11, 6, 12] = V [6, 5, 1, 3, 0, 6, 4, 5] :=
    overlap torus4405 torus4218 [6, 5] [6, 12] (by decide)
  have hl : V [4, 1, 2, 0, 5, 11, 6, 12] = V [4, 1, 2, 0, 5, 3] :=
    ((in_context torus71 [4, 1, 2, 0, 5] [12]).trans (in_context torus24 [4, 1, 2, 0, 5, 3] []))
  have hr : V [6, 5, 1, 3, 0, 6, 4, 5] = V [0, 5, 6, 3, 0, 6, 4, 5] :=
    (in_context torus1461 [] [3, 0, 6, 4, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8731 : V [0, 3, 0, 6, 1, 3, 5, 4] = V [3, 4, 1, 8, 0, 3] := by
  have h0 : V [3, 1, 7, 7, 0, 4, 1, 8, 0, 3] = V [0, 3, 2, 0, 5, 1, 2, 1, 2, 8, 2, 11] :=
    overlap torus5223 torus2391 [0, 3, 2, 0, 5, 1, 2, 1, 2] [7, 0, 4, 1, 8, 0, 3] (by decide)
  have hl : V [3, 1, 7, 7, 0, 4, 1, 8, 0, 3] = V [3, 4, 1, 8, 0, 3] :=
    ((in_context torus7 [3, 1] [0, 4, 1, 8, 0, 3]).trans (in_context torus1 [3] [4, 1, 8, 0, 3]))
  have hr : V [0, 3, 2, 0, 5, 1, 2, 1, 2, 8, 2, 11] = V [0, 3, 0, 6, 1, 3, 5, 4] :=
    ((in_context torus1435 [0, 3, 2, 0, 5, 1] [2, 11]).trans ((in_context torus2 [0, 3, 2, 0, 5, 1, 3] [11]).trans (in_context torus4229 [0, 3] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8756 : V [3, 0, 7, 1, 1, 4, 3, 12] = V [0, 6, 1, 4, 1, 2] := by
  have h0 : V [0, 6, 1, 1, 0, 4, 1, 2] = V [3, 0, 7, 1, 1, 2, 0, 1, 2, 4, 3, 12] :=
    overlap torus5391 torus3325 [3, 0, 7, 1, 1, 2, 0] [0, 4, 1, 2] (by decide)
  have hl : V [0, 6, 1, 1, 0, 4, 1, 2] = V [0, 6, 1, 4, 1, 2] :=
    (in_context torus1 [0, 6, 1] [4, 1, 2])
  have hr : V [3, 0, 7, 1, 1, 2, 0, 1, 2, 4, 3, 12] = V [3, 0, 7, 1, 1, 4, 3, 12] :=
    ((in_context torus0 [3, 0, 7, 1, 1, 2] [2, 4, 3, 12]).trans (in_context torus2 [3, 0, 7, 1, 1] [4, 3, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8761 : V [7, 0, 4, 1, 1, 8, 7, 12] = V [0, 3, 1, 8, 1, 6] := by
  have h0 : V [0, 3, 1, 1, 0, 8, 1, 6] = V [7, 0, 4, 1, 1, 8, 7, 12] :=
    overlap torus5399 torus2720 [7, 0, 4, 1, 1] [0, 8, 1, 6] (by decide)
  have hl : V [0, 3, 1, 1, 0, 8, 1, 6] = V [0, 3, 1, 8, 1, 6] :=
    (in_context torus1 [0, 3, 1] [8, 1, 6])
  have hr : V [7, 0, 4, 1, 1, 8, 7, 12] = V [7, 0, 4, 1, 1, 8, 7, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8857 : V [0, 3, 4, 7, 0, 4, 1, 12] = V [4, 1, 8, 6, 7, 5] := by
  have h0 : V [3, 12, 7, 8, 1, 5, 3, 4, 2, 11] = V [8, 0, 4, 1, 7, 0, 3, 1, 8, 7, 4, 0, 8, 1] :=
    overlap torus2197 torus5930 [8, 0, 4, 1, 7, 0, 3, 1, 8] [7, 8, 1, 5, 3, 4, 2, 11] (by decide)
  have hl : V [3, 12, 7, 8, 1, 5, 3, 4, 2, 11] = V [4, 1, 8, 6, 7, 5] :=
    ((in_context torus78 [3] [8, 1, 5, 3, 4, 2, 11]).trans ((in_context torus3 [] [12, 8, 1, 5, 3, 4, 2, 11]).trans ((in_context torus84 [] [1, 5, 3, 4, 2, 11]).trans ((in_context torus94 [4] [5, 3, 4, 2, 11]).trans ((in_context torus66 [4, 1] [3, 4, 2, 11]).trans ((in_context torus54 [4, 1, 8] [4, 2, 11]).trans ((in_context torus60 [4, 1, 8, 6] [2, 11]).trans ((in_context torus48 [4, 1, 8, 6, 7] [11]).trans (in_context torus29 [4, 1, 8, 6, 7, 5] [])))))))))
  have hr : V [8, 0, 4, 1, 7, 0, 3, 1, 8, 7, 4, 0, 8, 1] = V [0, 3, 4, 7, 0, 4, 1, 12] :=
    ((in_context torus2261 [] [7, 4, 0, 8, 1]).trans ((in_context torus78 [3, 2] [4, 0, 8, 1]).trans ((in_context torus1439 [] [12, 4, 0, 8, 1]).trans ((in_context torus60 [0, 3, 4] [0, 8, 1]).trans ((in_context torus93 [0, 3, 4, 7] [8, 1]).trans ((in_context torus84 [0, 3, 4, 7, 0] [1]).trans (in_context torus94 [0, 3, 4, 7, 0, 4] [])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8944 : V [1, 1, 8, 7, 3, 1, 7, 0] = V [7, 8, 5, 0, 8, 11] := by
  have h0 : V [7, 8, 5, 0, 8, 11] = V [1, 1, 8, 7, 3, 1, 7, 0] :=
    overlap torus7367 torus29 [1, 1, 8, 7, 3, 1, 7, 0] [11] (by decide)
  have hl : V [7, 8, 5, 0, 8, 11] = V [7, 8, 5, 0, 8, 11] :=
    rfl
  have hr : V [1, 1, 8, 7, 3, 1, 7, 0] = V [1, 1, 8, 7, 3, 1, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus8968 : V [1, 5, 4, 7, 1, 4, 6, 5] = V [3, 5, 1, 2, 0, 4] := by
  have h0 : V [5, 7, 6, 6, 0, 2, 1, 6, 8, 6] = V [0, 6, 7, 1, 5, 4, 6, 5, 6, 7, 1, 4, 6, 5] :=
    overlap torus2246 torus7686 [0, 6, 7, 1, 5, 4, 6, 5] [6, 0, 2, 1, 6, 8, 6] (by decide)
  have hl : V [5, 7, 6, 6, 0, 2, 1, 6, 8, 6] = V [3, 5, 1, 2, 0, 4] :=
    ((in_context torus6 [5, 7] [0, 2, 1, 6, 8, 6]).trans ((in_context torus3953 [5] [6]).trans ((in_context torus4506 [] [5, 6]).trans ((in_context torus65 [3, 1, 8, 0, 4] [6]).trans ((in_context torus71 [3, 1, 8, 0, 4, 2] []).trans ((in_context torus4483 [3, 1] []).trans (in_context torus1 [3] [5, 1, 2, 0, 4])))))))
  have hr : V [0, 6, 7, 1, 5, 4, 6, 5, 6, 7, 1, 4, 6, 5] = V [1, 5, 4, 7, 1, 4, 6, 5] :=
    ((in_context torus2274 [] [6, 7, 1, 4, 6, 5]).trans (in_context torus6 [1, 5, 4] [7, 1, 4, 6, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus9740 : V [3, 2, 4, 1, 8, 3, 2] = V [1, 3, 2, 5, 1, 2, 4] := by
  have h0 : V [2, 7, 2, 1, 6, 0, 8] = V [3, 4, 5, 6, 7, 8, 2] :=
    overlap torus1764 torus1485 [3, 4, 5, 6] [0, 8] (by decide)
  have hl : V [2, 7, 2, 1, 6, 0, 8] = V [1, 3, 2, 5, 1, 2, 4] :=
    ((in_context torus4379 [2] []).trans (in_context torus1446 [] [5, 1, 2, 4]))
  have hr : V [3, 4, 5, 6, 7, 8, 2] = V [3, 2, 4, 1, 8, 3, 2] :=
    (in_context torus1805 [3] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus9755 : V [7, 6, 2, 1, 6, 8, 6] = V [0, 5, 7, 1, 4, 6, 5] := by
  have h0 : V [0, 7, 8, 2, 3, 4, 5] = V [7, 6, 2, 1, 6, 8, 6] :=
    overlap torus1475 torus1767 [7, 6] [2, 3, 4, 5] (by decide)
  have hl : V [0, 7, 8, 2, 3, 4, 5] = V [0, 5, 7, 1, 4, 6, 5] :=
    ((in_context torus1429 [0, 7] [4, 5]).trans (in_context torus1863 [0] [5]))
  have hr : V [7, 6, 2, 1, 6, 8, 6] = V [7, 6, 2, 1, 6, 8, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10246 : V [6, 1, 3, 5, 1, 3, 2] = V [4, 5, 3, 5, 1, 2, 3] := by
  have h0 : V [4, 6, 7, 2, 0, 3, 0] = V [6, 1, 3, 5, 1, 3, 2] :=
    overlap torus1968 torus1446 [6, 1, 3, 5] [3, 0] (by decide)
  have hl : V [4, 6, 7, 2, 0, 3, 0] = V [4, 5, 3, 5, 1, 2, 3] :=
    (in_context torus3824 [4] [])
  have hr : V [6, 1, 3, 5, 1, 3, 2] = V [6, 1, 3, 5, 1, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10286 : V [3, 8, 0, 4, 1, 2, 8] = V [0, 8, 2, 6, 0, 2, 7] := by
  have h0 : V [0, 8, 2, 6, 0, 2, 7] = V [8, 7, 5, 1, 5, 3, 2] :=
    overlap torus1484 torus1981 [8, 7] [6, 0, 2, 7] (by decide)
  have hl : V [0, 8, 2, 6, 0, 2, 7] = V [0, 8, 2, 6, 0, 2, 7] :=
    rfl
  have hr : V [8, 7, 5, 1, 5, 3, 2] = V [3, 8, 0, 4, 1, 2, 8] :=
    ((in_context torus1576 [8] [3, 2]).trans ((in_context torus1584 [] [4, 3, 2]).trans ((in_context torus1453 [7, 1, 7] [2]).trans ((in_context torus3588 [] [2]).trans (in_context torus1436 [3, 8, 0, 4] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10301 : V [2, 3, 8, 0, 4, 2, 3] = V [0, 2, 3, 7, 0, 3, 8] := by
  have h0 : V [2, 8, 2, 7, 0, 3, 8] = V [4, 2, 0, 5, 3, 5, 6, 5, 1, 5, 3] :=
    overlap torus1954 torus1984 [4, 2, 0, 5, 3, 5, 6] [2, 7, 0, 3, 8] (by decide)
  have hl : V [2, 8, 2, 7, 0, 3, 8] = V [0, 2, 3, 7, 0, 3, 8] :=
    (in_context torus1428 [] [7, 0, 3, 8])
  have hr : V [4, 2, 0, 5, 3, 5, 6, 5, 1, 5, 3] = V [2, 3, 8, 0, 4, 2, 3] :=
    ((in_context torus1956 [] [5, 1, 5, 3]).trans ((in_context torus1576 [2, 8] [3]).trans ((in_context torus1584 [2] [4, 3]).trans ((in_context torus1453 [2, 7, 1, 7] []).trans (in_context torus3588 [2] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10326 : V [2, 1, 2, 6, 1, 6, 4] = V [0, 3, 4, 8, 0, 4, 2] := by
  have h0 : V [2, 1, 2, 7, 6, 5, 4] = V [3, 2, 3, 8, 0, 4, 2] :=
    overlap torus1866 torus1989 [3, 2] [5, 4] (by decide)
  have hl : V [2, 1, 2, 7, 6, 5, 4] = V [2, 1, 2, 6, 1, 6, 4] :=
    (in_context torus1471 [2, 1, 2] [4])
  have hr : V [3, 2, 3, 8, 0, 4, 2] = V [0, 3, 4, 8, 0, 4, 2] :=
    (in_context torus1439 [] [8, 0, 4, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem torus10346 : V [4, 5, 2, 0, 5, 3, 5] = V [1, 3, 1, 3, 7, 1, 7] := by
  have h0 : V [3, 4, 0, 2, 7, 1, 7] = V [4, 5, 2, 0, 5, 3, 5] :=
    overlap torus1451 torus1998 [4, 5] [2, 7, 1, 7] (by decide)
  have hl : V [3, 4, 0, 2, 7, 1, 7] = V [1, 3, 1, 3, 7, 1, 7] :=
    ((in_context torus1455 [] [2, 7, 1, 7]).trans (in_context torus1444 [1] [7, 1, 7]))
  have hr : V [4, 5, 2, 0, 5, 3, 5] = V [4, 5, 2, 0, 5, 3, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10351 : V [3, 1, 3, 7, 1, 7, 5] = V [0, 4, 5, 2, 0, 5, 3] := by
  have h0 : V [0, 4, 5, 2, 0, 5, 3] = V [4, 3, 2, 7, 1, 7, 5] :=
    overlap torus1448 torus1999 [4, 3] [2, 0, 5, 3] (by decide)
  have hl : V [0, 4, 5, 2, 0, 5, 3] = V [0, 4, 5, 2, 0, 5, 3] :=
    rfl
  have hr : V [4, 3, 2, 7, 1, 7, 5] = V [3, 1, 3, 7, 1, 7, 5] :=
    (in_context torus1444 [] [7, 1, 7, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10378 : V [4, 1, 2, 0, 5, 3, 5] = V [0, 5, 6, 3, 0, 6, 4] := by
  have h0 : V [0, 5, 6, 3, 0, 6, 4] = V [5, 4, 2, 1, 2, 7, 6] :=
    overlap torus1457 torus2009 [5, 4] [3, 0, 6, 4] (by decide)
  have hl : V [0, 5, 6, 3, 0, 6, 4] = V [0, 5, 6, 3, 0, 6, 4] :=
    rfl
  have hr : V [5, 4, 2, 1, 2, 7, 6] = V [4, 1, 2, 0, 5, 3, 5] :=
    ((in_context torus1553 [5] [7, 6]).trans ((in_context torus1563 [] [8, 7, 6]).trans ((in_context torus1480 [4, 1, 4, 2] []).trans (in_context torus1998 [4, 1] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10547 : V [3, 0, 5, 1, 2, 4, 3] = V [2, 4, 0, 6, 1, 3, 5] := by
  have h0 : V [2, 3, 4, 5, 6, 7, 2, 0, 2] = V [7, 2, 1, 6, 0, 8, 3] :=
    overlap torus2050 torus1529 [7, 2, 1, 6] [7, 2, 0, 2] (by decide)
  have hl : V [2, 3, 4, 5, 6, 7, 2, 0, 2] = V [2, 4, 0, 6, 1, 3, 5] :=
    ((in_context torus1783 [2, 3] [0, 2]).trans ((in_context torus3 [2] [8, 3, 1, 7, 0, 2]).trans (in_context torus4380 [2] [])))
  have hr : V [7, 2, 1, 6, 0, 8, 3] = V [3, 0, 5, 1, 2, 4, 3] :=
    (in_context torus4379 [] [3])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10549 : V [5, 7, 1, 4, 0, 6, 7] = V [1, 7, 6, 2, 1, 6, 8] := by
  have h0 : V [6, 7, 0, 2, 1, 6, 8] = V [7, 8, 2, 3, 4, 5, 6] :=
    overlap torus1478 torus2050 [7, 8] [2, 1, 6, 8] (by decide)
  have hl : V [6, 7, 0, 2, 1, 6, 8] = V [1, 7, 6, 2, 1, 6, 8] :=
    (in_context torus1482 [] [2, 1, 6, 8])
  have hr : V [7, 8, 2, 3, 4, 5, 6] = V [5, 7, 1, 4, 0, 6, 7] :=
    ((in_context torus1429 [7] [4, 5, 6]).trans ((in_context torus1863 [] [5, 6]).trans (in_context torus1466 [5, 7, 1, 4] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10572 : V [2, 0, 2, 4, 5, 6, 7] = V [1, 8, 7, 3, 1, 7, 2] := by
  have h0 : V [7, 8, 0, 3, 1, 7, 2] = V [8, 2, 3, 4, 5, 6, 7] :=
    overlap torus1487 torus2054 [8, 2] [3, 1, 7, 2] (by decide)
  have hl : V [7, 8, 0, 3, 1, 7, 2] = V [1, 8, 7, 3, 1, 7, 2] :=
    (in_context torus1490 [] [3, 1, 7, 2])
  have hr : V [8, 2, 3, 4, 5, 6, 7] = V [2, 0, 2, 4, 5, 6, 7] :=
    (in_context torus1429 [] [4, 5, 6, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10630 : V [7, 8, 5, 0, 8, 6, 8] = V [1, 2, 7, 0, 3, 8, 2] := by
  have h0 : V [6, 7, 0, 4, 1, 4, 2] = V [7, 8, 5, 0, 8, 6, 8] :=
    overlap torus1478 torus2065 [7, 8] [4, 1, 4, 2] (by decide)
  have hl : V [6, 7, 0, 4, 1, 4, 2] = V [1, 2, 7, 0, 3, 8, 2] :=
    ((in_context torus1482 [] [4, 1, 4, 2]).trans ((in_context torus1568 [1, 7] [2]).trans ((in_context torus1576 [1] [3, 2]).trans (in_context torus1982 [1] [2]))))
  have hr : V [7, 8, 5, 0, 8, 6, 8] = V [7, 8, 5, 0, 8, 6, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10717 : V [2, 7, 0, 3, 1, 8, 7] = V [0, 7, 8, 5, 0, 8, 6] := by
  have h0 : V [0, 7, 8, 5, 0, 8, 6] = V [7, 6, 4, 1, 4, 2, 8] :=
    overlap torus1475 torus2080 [7, 6] [5, 0, 8, 6] (by decide)
  have hl : V [0, 7, 8, 5, 0, 8, 6] = V [0, 7, 8, 5, 0, 8, 6] :=
    rfl
  have hr : V [7, 6, 4, 1, 4, 2, 8] = V [2, 7, 0, 3, 1, 8, 7] :=
    ((in_context torus1568 [7] [2, 8]).trans ((in_context torus1576 [] [3, 2, 8]).trans ((in_context torus1982 [] [2, 8]).trans ((in_context torus1487 [2, 7, 0, 3] []).trans (in_context torus1490 [2, 7, 0, 3] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10939 : V [4, 6, 1, 3, 0, 5, 6] = V [1, 6, 5, 8, 1, 5, 7] := by
  have h0 : V [5, 6, 0, 8, 1, 5, 7] = V [6, 7, 2, 0, 2, 4, 5] :=
    overlap torus1469 torus2149 [6, 7] [8, 1, 5, 7] (by decide)
  have hl : V [5, 6, 0, 8, 1, 5, 7] = V [1, 6, 5, 8, 1, 5, 7] :=
    (in_context torus1473 [] [8, 1, 5, 7])
  have hr : V [6, 7, 2, 0, 2, 4, 5] = V [4, 6, 1, 3, 0, 5, 6] :=
    ((in_context torus1839 [] [4, 5]).trans (in_context torus1457 [4, 6, 1, 3] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10968 : V [5, 0, 8, 1, 6, 3, 1] = V [0, 7, 2, 3, 4, 6, 12] := by
  have h0 : V [7, 6, 12, 2, 4, 1, 8] = V [5, 0, 8, 1, 4, 0, 7, 1, 0, 5, 7, 8, 3] :=
    overlap torus2260 torus1810 [5, 0, 8, 1, 4, 0, 7, 1] [2, 4, 1, 8] (by decide)
  have hl : V [7, 6, 12, 2, 4, 1, 8] = V [0, 7, 2, 3, 4, 6, 12] :=
    ((in_context torus48 [7, 6] [4, 1, 8]).trans ((in_context torus1471 [] [12, 4, 1, 8]).trans ((in_context torus60 [6, 1, 6] [1, 8]).trans ((in_context torus94 [6, 1, 6, 7] [8]).trans ((in_context torus84 [6, 1, 6, 7, 1] []).trans (in_context torus3857 [] [12]))))))
  have hr : V [5, 0, 8, 1, 4, 0, 7, 1, 0, 5, 7, 8, 3] = V [5, 0, 8, 1, 6, 3, 1] :=
    ((in_context torus1 [5, 0, 8, 1, 4, 0, 7] [5, 7, 8, 3]).trans ((in_context torus2151 [5, 0, 8, 1] [3]).trans (in_context torus3 [5, 0, 8, 1, 6, 3, 1] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus10979 : V [7, 1, 1, 5, 4, 6, 5] = V [0, 7, 8, 1, 5, 4, 6] := by
  have h0 : V [8, 7, 6, 7, 1, 5, 4, 6, 5] = V [0, 7, 8, 1, 5, 4, 6] :=
    overlap torus1483 torus2274 [0, 7, 8] [6, 7, 1, 5, 4, 6, 5] (by decide)
  have hl : V [8, 7, 6, 7, 1, 5, 4, 6, 5] = V [7, 1, 1, 5, 4, 6, 5] :=
    ((in_context torus1480 [] [7, 1, 5, 4, 6, 5]).trans (in_context torus7 [7, 1] [1, 5, 4, 6, 5]))
  have hr : V [0, 7, 8, 1, 5, 4, 6] = V [0, 7, 8, 1, 5, 4, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus11000 : V [3, 5, 1, 2, 0, 4, 5] = V [1, 5, 4, 7, 1, 4, 6] := by
  have h0 : V [5, 4, 4, 6, 5, 7, 1, 4, 6] = V [3, 0, 6, 4, 6, 5, 7, 1, 4, 1, 3, 5, 4] :=
    overlap torus2155 torus2344 [3, 0, 6, 4, 6, 5, 7, 1, 4] [4, 6, 5, 7, 1, 4, 6] (by decide)
  have hl : V [5, 4, 4, 6, 5, 7, 1, 4, 6] = V [1, 5, 4, 7, 1, 4, 6] :=
    ((in_context torus4 [5] [6, 5, 7, 1, 4, 6]).trans ((in_context torus1460 [] [7, 1, 4, 6]).trans (in_context torus1464 [] [7, 1, 4, 6])))
  have hr : V [3, 0, 6, 4, 6, 5, 7, 1, 4, 1, 3, 5, 4] = V [3, 5, 1, 2, 0, 4, 5] :=
    ((in_context torus2343 [3] [1, 3, 5, 4]).trans ((in_context torus3 [] [5, 4, 6, 1, 3, 5, 4]).trans ((in_context torus3828 [] [4]).trans (in_context torus1448 [3, 5, 1, 2] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11151 : V [8, 2, 6, 0, 2, 7, 8] = V [1, 3, 8, 0, 4, 1, 2] := by
  have h0 : V [7, 8, 0, 5, 1, 5, 2, 1, 2] = V [8, 2, 6, 0, 2, 7, 8] :=
    overlap torus1487 torus2538 [8, 2] [5, 1, 5, 2, 1, 2] (by decide)
  have hl : V [7, 8, 0, 5, 1, 5, 2, 1, 2] = V [1, 3, 8, 0, 4, 1, 2] :=
    ((in_context torus1490 [] [5, 1, 5, 2, 1, 2]).trans ((in_context torus1576 [1, 8] [2, 1, 2]).trans ((in_context torus1584 [1] [4, 2, 1, 2]).trans (in_context torus1678 [1] [1, 2]))))
  have hr : V [8, 2, 6, 0, 2, 7, 8] = V [8, 2, 6, 0, 2, 7, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11152 : V [4, 0, 6, 1, 3, 5, 12] = V [2, 3, 8, 0, 4, 1, 2] := by
  have h0 : V [2, 8, 7, 5, 1, 5, 2, 1, 2] = V [8, 1, 6, 0, 2, 7, 8] :=
    overlap torus1489 torus2538 [8, 1] [5, 1, 5, 2, 1, 2] (by decide)
  have hl : V [2, 8, 7, 5, 1, 5, 2, 1, 2] = V [2, 3, 8, 0, 4, 1, 2] :=
    ((in_context torus1576 [2, 8] [2, 1, 2]).trans ((in_context torus1584 [2] [4, 2, 1, 2]).trans (in_context torus1678 [2] [1, 2])))
  have hr : V [8, 1, 6, 0, 2, 7, 8] = V [4, 0, 6, 1, 3, 5, 12] :=
    ((in_context torus4202 [] [8]).trans (in_context torus4228 [4] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11159 : V [4, 5, 1, 2, 8, 3, 2] = V [1, 4, 1, 1, 2, 8, 3] := by
  have h0 : V [4, 5, 3, 1, 2, 8, 0, 3, 4] = V [0, 5, 6, 1, 4, 3, 5, 1, 3, 1, 1, 2, 8] :=
    overlap torus2241 torus2545 [0, 5, 6, 1, 4, 3, 5, 1] [1, 2, 8, 0, 3, 4] (by decide)
  have hl : V [4, 5, 3, 1, 2, 8, 0, 3, 4] = V [1, 4, 1, 1, 2, 8, 3] :=
    ((in_context torus1594 [] [2, 8, 0, 3, 4]).trans ((in_context torus1436 [1, 4] [8, 0, 3, 4]).trans ((in_context torus8 [1, 4, 1, 2] [0, 3, 4]).trans (in_context torus1544 [1, 4, 1] []))))
  have hr : V [0, 5, 6, 1, 4, 3, 5, 1, 3, 1, 1, 2, 8] = V [4, 5, 1, 2, 8, 3, 2] :=
    ((in_context torus2422 [] [3, 1, 1, 2, 8]).trans ((in_context torus1442 [4, 5] [1, 1, 2, 8]).trans ((in_context torus1446 [4, 5] [1, 1, 2, 8]).trans ((in_context torus1432 [4, 5, 1] [1, 2, 8]).trans ((in_context torus1 [4, 5] [2, 3, 1, 2, 8]).trans ((in_context torus1541 [4, 5, 2] []).trans (in_context torus1544 [4, 5] [2])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11179 : V [6, 7, 1, 4, 3, 5, 4] = V [1, 6, 1, 1, 4, 3, 5] := by
  have h0 : V [6, 7, 5, 1, 4, 3, 0, 5, 6] = V [0, 7, 8, 1, 6, 5, 7, 1, 5, 1, 1, 4, 3] :=
    overlap torus2249 torus2566 [0, 7, 8, 1, 6, 5, 7, 1] [1, 4, 3, 0, 5, 6] (by decide)
  have hl : V [6, 7, 5, 1, 4, 3, 0, 5, 6] = V [1, 6, 1, 1, 4, 3, 5] :=
    ((in_context torus1596 [] [4, 3, 0, 5, 6]).trans ((in_context torus1451 [1, 6] [3, 0, 5, 6]).trans ((in_context torus1455 [1, 6] [3, 0, 5, 6]).trans ((in_context torus3 [1, 6, 1, 4] [0, 5, 6]).trans (in_context torus1561 [1, 6, 1] [])))))
  have hr : V [0, 7, 8, 1, 6, 5, 7, 1, 5, 1, 1, 4, 3] = V [6, 7, 1, 4, 3, 5, 4] :=
    ((in_context torus2430 [] [5, 1, 1, 4, 3]).trans ((in_context torus1460 [6, 7] [1, 1, 4, 3]).trans ((in_context torus1464 [6, 7] [1, 1, 4, 3]).trans ((in_context torus1452 [6, 7, 1] [1, 4, 3]).trans ((in_context torus1 [6, 7] [4, 5, 1, 4, 3]).trans ((in_context torus1546 [6, 7, 4] []).trans (in_context torus1561 [6, 7] [4])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11227 : V [5, 6, 3, 0, 6, 5, 0] = V [1, 7, 5, 0, 8, 1, 5] := by
  have h0 : V [4, 5, 0, 2, 1, 2, 6, 1, 5] = V [5, 6, 3, 0, 6, 5, 0] :=
    overlap torus1460 torus2674 [5, 6] [2, 1, 2, 6, 1, 5] (by decide)
  have hl : V [4, 5, 0, 2, 1, 2, 6, 1, 5] = V [1, 7, 5, 0, 8, 1, 5] :=
    ((in_context torus1464 [] [2, 1, 2, 6, 1, 5]).trans ((in_context torus1553 [1, 5] [6, 1, 5]).trans ((in_context torus1563 [1] [8, 6, 1, 5]).trans (in_context torus2111 [1] [1, 5]))))
  have hr : V [5, 6, 3, 0, 6, 5, 0] = V [5, 6, 3, 0, 6, 5, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11232 : V [8, 0, 3, 1, 7, 8, 1] = V [5, 1, 3, 0, 6, 5, 11] := by
  have h0 : V [7, 8, 2, 3, 4, 5, 7, 0, 8] = V [8, 0, 3, 1, 7, 8, 1] :=
    overlap torus1485 torus2687 [8, 0] [3, 4, 5, 7, 0, 8] (by decide)
  have hl : V [7, 8, 2, 3, 4, 5, 7, 0, 8] = V [5, 1, 3, 0, 6, 5, 11] :=
    ((in_context torus236 [7] [0, 8]).trans ((in_context torus1484 [7, 6, 2] [5, 0, 8]).trans ((in_context torus1491 [7, 6] [5, 0, 8]).trans ((in_context torus4431 [] [8]).trans (in_context torus83 [5, 1, 3, 0, 6] [])))))
  have hr : V [8, 0, 3, 1, 7, 8, 1] = V [8, 0, 3, 1, 7, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11371 : V [8, 7, 3, 1, 7, 2, 8] = V [0, 2, 0, 4, 1, 8, 3] := by
  have h0 : V [0, 8, 2, 3, 2, 4, 1, 8, 3] = V [8, 7, 3, 1, 7, 2, 8] :=
    overlap torus1484 torus2830 [8, 7] [3, 2, 4, 1, 8, 3] (by decide)
  have hl : V [0, 8, 2, 3, 2, 4, 1, 8, 3] = V [0, 2, 0, 4, 1, 8, 3] :=
    ((in_context torus1429 [0] [2, 4, 1, 8, 3]).trans (in_context torus2 [0, 2, 0] [4, 1, 8, 3]))
  have hr : V [8, 7, 3, 1, 7, 2, 8] = V [8, 7, 3, 1, 7, 2, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11414 : V [6, 1, 2, 0, 5, 4, 0] = V [1, 3, 0, 5, 8, 7, 12] := by
  have h0 : V [1, 3, 0, 5, 12, 5, 4] = V [6, 1, 2, 0, 5, 3, 3, 4, 0] :=
    overlap torus2872 torus1451 [6, 1, 2, 0, 5, 3] [5, 4] (by decide)
  have hl : V [1, 3, 0, 5, 12, 5, 4] = V [1, 3, 0, 5, 8, 7, 12] :=
    ((in_context torus66 [1, 3, 0, 5] [4]).trans (in_context torus60 [1, 3, 0, 5, 8] []))
  have hr : V [6, 1, 2, 0, 5, 3, 3, 4, 0] = V [6, 1, 2, 0, 5, 4, 0] :=
    (in_context torus3 [6, 1, 2, 0, 5] [4, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11454 : V [5, 1, 8, 0, 0, 4, 5] = V [1, 2, 0, 4, 0, 6, 12] := by
  have h0 : V [1, 2, 0, 4, 12, 0, 3] = V [5, 1, 8, 0, 4, 2, 2, 3, 4] :=
    overlap torus2904 torus1440 [5, 1, 8, 0, 4, 2] [0, 3] (by decide)
  have hl : V [1, 2, 0, 4, 12, 0, 3] = V [1, 2, 0, 4, 0, 6, 12] :=
    ((in_context torus93 [1, 2, 0, 4] [3]).trans (in_context torus54 [1, 2, 0, 4, 0] []))
  have hr : V [5, 1, 8, 0, 4, 2, 2, 3, 4] = V [5, 1, 8, 0, 0, 4, 5] :=
    ((in_context torus2 [5, 1, 8, 0, 4] [3, 4]).trans (in_context torus1448 [5, 1, 8, 0] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11502 : V [4, 1, 7, 0, 0, 5, 1] = V [1, 8, 0, 0, 6, 1, 2] := by
  have h0 : V [1, 8, 0, 3, 12, 7, 0, 3, 1, 6, 11] = V [4, 1, 7, 0, 0, 5, 1] :=
    overlap torus2934 torus2509 [4, 1, 7, 0] [7, 0, 3, 1, 6, 11] (by decide)
  have hl : V [1, 8, 0, 3, 12, 7, 0, 3, 1, 6, 11] = V [1, 8, 0, 0, 6, 1, 2] :=
    ((in_context torus78 [1, 8, 0, 3] [0, 3, 1, 6, 11]).trans ((in_context torus3 [1, 8, 0] [12, 0, 3, 1, 6, 11]).trans ((in_context torus93 [1, 8, 0] [3, 1, 6, 11]).trans ((in_context torus54 [1, 8, 0, 0] [1, 6, 11]).trans ((in_context torus94 [1, 8, 0, 0, 6] [6, 11]).trans ((in_context torus72 [1, 8, 0, 0, 6, 1] [11]).trans (in_context torus29 [1, 8, 0, 0, 6, 1, 2] [])))))))
  have hr : V [4, 1, 7, 0, 0, 5, 1] = V [4, 1, 7, 0, 0, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11666 : V [8, 2, 1, 6, 5, 7, 6] = V [1, 8, 1, 1, 6, 5, 7] := by
  have h0 : V [2, 3, 2, 7, 8, 1, 6, 5, 7] = V [8, 2, 1, 6, 5, 7, 6] :=
    overlap torus1430 torus3059 [8, 2] [7, 8, 1, 6, 5, 7] (by decide)
  have hl : V [2, 3, 2, 7, 8, 1, 6, 5, 7] = V [1, 8, 1, 1, 6, 5, 7] :=
    ((in_context torus1436 [] [7, 8, 1, 6, 5, 7]).trans ((in_context torus1484 [1, 2] [1, 6, 5, 7]).trans (in_context torus1491 [1] [1, 6, 5, 7])))
  have hr : V [8, 2, 1, 6, 5, 7, 6] = V [8, 2, 1, 6, 5, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus11830 : V [2, 4, 3, 5, 1, 8, 1] = V [1, 7, 0, 3, 5, 6, 11] := by
  have h0 : V [1, 7, 11, 6, 3, 5, 1, 2, 4] = V [2, 4, 3, 5, 1, 2, 0, 8, 2] :=
    overlap torus3165 torus1824 [2, 4, 3, 5, 1, 2, 0] [6, 3, 5, 1, 2, 4] (by decide)
  have hl : V [1, 7, 11, 6, 3, 5, 1, 2, 4] = V [1, 7, 0, 3, 5, 6, 11] :=
    ((in_context torus71 [1, 7] [3, 5, 1, 2, 4]).trans ((in_context torus53 [1, 7, 3] [5, 1, 2, 4]).trans ((in_context torus65 [1, 7, 3, 7] [1, 2, 4]).trans ((in_context torus92 [1, 7, 3, 7, 2] [2, 4]).trans ((in_context torus47 [1, 7, 3, 7, 2, 1] [4]).trans ((in_context torus2049 [1, 7] [11, 4]).trans ((in_context torus59 [1, 7, 0, 3, 5, 6, 8] []).trans (in_context torus8 [1, 7, 0, 3, 5, 6] [11]))))))))
  have hr : V [2, 4, 3, 5, 1, 2, 0, 8, 2] = V [2, 4, 3, 5, 1, 8, 1] :=
    (in_context torus1491 [2, 4, 3, 5, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus12178 : V [7, 1, 5, 1, 3, 0, 11] = V [0, 8, 2, 1, 5, 0, 2] := by
  have h0 : V [8, 7, 8, 1, 5, 0, 2] = V [7, 1, 5, 1, 3, 0, 11] :=
    overlap torus1481 torus3349 [7, 1] [8, 1, 5, 0, 2] (by decide)
  have hl : V [8, 7, 8, 1, 5, 0, 2] = V [0, 8, 2, 1, 5, 0, 2] :=
    (in_context torus1484 [] [1, 5, 0, 2])
  have hr : V [7, 1, 5, 1, 3, 0, 11] = V [7, 1, 5, 1, 3, 0, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus12305 : V [3, 0, 6, 1, 1, 8, 0] = V [0, 7, 1, 1, 2, 0, 5] := by
  have h0 : V [3, 0, 6, 1, 11, 1, 4, 0, 12] = V [0, 7, 1, 4, 4, 1, 2, 0, 5] :=
    overlap torus3419 torus3401 [0, 7, 1, 4] [1, 4, 0, 12] (by decide)
  have hl : V [3, 0, 6, 1, 11, 1, 4, 0, 12] = V [3, 0, 6, 1, 1, 8, 0] :=
    ((in_context torus92 [3, 0, 6, 1] [4, 0, 12]).trans ((in_context torus59 [3, 0, 6, 1, 1] [0, 12]).trans ((in_context torus91 [3, 0, 6, 1, 1, 8] [12]).trans (in_context torus24 [3, 0, 6, 1, 1, 8, 0] []))))
  have hr : V [0, 7, 1, 4, 4, 1, 2, 0, 5] = V [0, 7, 1, 1, 2, 0, 5] :=
    (in_context torus4 [0, 7, 1] [1, 2, 0, 5])
  exact hl.symm.trans (h0.trans hr)

private theorem torus12532 : V [1, 4, 3, 6, 1, 3, 12] = V [0, 3, 4, 8, 0, 4, 1] := by
  have h0 : V [4, 12, 2, 8, 3, 1, 7] = V [2, 0, 5, 1, 8, 0, 4, 1, 2, 2, 1, 6, 8, 7, 2] :=
    overlap torus2228 torus3788 [2, 0, 5, 1, 8, 0, 4, 1, 2] [2, 8, 3, 1, 7] (by decide)
  have hl : V [4, 12, 2, 8, 3, 1, 7] = V [1, 4, 3, 6, 1, 3, 12] :=
    ((in_context torus48 [4] [8, 3, 1, 7]).trans ((in_context torus84 [4, 5] [3, 1, 7]).trans ((in_context torus1451 [] [12, 3, 1, 7]).trans ((in_context torus1455 [] [12, 3, 1, 7]).trans ((in_context torus54 [1, 4, 3] [1, 7]).trans ((in_context torus94 [1, 4, 3, 6] [7]).trans (in_context torus78 [1, 4, 3, 6, 1] [])))))))
  have hr : V [2, 0, 5, 1, 8, 0, 4, 1, 2, 2, 1, 6, 8, 7, 2] = V [0, 3, 4, 8, 0, 4, 1] :=
    ((in_context torus2264 [] [2, 1, 6, 8, 7, 2]).trans ((in_context torus48 [4, 3] [1, 6, 8, 7, 2]).trans ((in_context torus94 [4, 3, 5] [6, 8, 7, 2]).trans ((in_context torus72 [4, 3, 5, 1] [8, 7, 2]).trans ((in_context torus84 [4, 3, 5, 1, 2] [7, 2]).trans ((in_context torus78 [4, 3, 5, 1, 2, 4] [2]).trans ((in_context torus48 [4, 3, 5, 1, 2, 4, 3] []).trans ((in_context torus3265 [4, 3] []).trans (in_context torus1443 [] [8, 0, 4, 1])))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus12584 : V [5, 0, 8, 1, 5, 6, 1] = V [1, 5, 6, 1, 3, 0, 6] := by
  have h0 : V [1, 5, 6, 1, 3, 5, 5, 0, 6] = V [5, 0, 8, 1, 5, 6, 1] :=
    overlap torus3840 torus2672 [5, 0] [5, 0, 6] (by decide)
  have hl : V [1, 5, 6, 1, 3, 5, 5, 0, 6] = V [1, 5, 6, 1, 3, 0, 6] :=
    (in_context torus5 [1, 5, 6, 1, 3] [0, 6])
  have hr : V [5, 0, 8, 1, 5, 6, 1] = V [5, 0, 8, 1, 5, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus12838 : V [8, 7, 2, 8, 0, 3, 4] = V [0, 0, 2, 3, 8, 0, 3] := by
  have h0 : V [0, 0, 2, 3, 8, 0, 3] = V [8, 7, 2, 8, 0, 3, 4] :=
    overlap torus4190 torus1439 [8, 7, 2, 8] [3] (by decide)
  have hl : V [0, 0, 2, 3, 8, 0, 3] = V [0, 0, 2, 3, 8, 0, 3] :=
    rfl
  have hr : V [8, 7, 2, 8, 0, 3, 4] = V [8, 7, 2, 8, 0, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus12984 : V [3, 1, 8, 1, 6, 1, 5] = V [1, 7, 0, 4, 1, 7, 12] := by
  have h0 : V [1, 7, 0, 4, 1, 12, 4] = V [3, 1, 8, 1, 6, 1, 5] :=
    overlap torus4255 torus1615 [3, 1, 8] [4] (by decide)
  have hl : V [1, 7, 0, 4, 1, 12, 4] = V [1, 7, 0, 4, 1, 7, 12] :=
    (in_context torus60 [1, 7, 0, 4, 1] [])
  have hr : V [3, 1, 8, 1, 6, 1, 5] = V [3, 1, 8, 1, 6, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13024 : V [8, 0, 5, 1, 1, 2, 8] = V [0, 4, 1, 2, 1, 7, 11] := by
  have h0 : V [0, 4, 2, 3, 8, 11, 2, 3, 0] = V [8, 0, 5, 1, 2, 3, 2] :=
    overlap torus4267 torus1437 [8, 0, 5, 1, 2] [2, 3, 0] (by decide)
  have hl : V [0, 4, 2, 3, 8, 11, 2, 3, 0] = V [0, 4, 1, 2, 1, 7, 11] :=
    ((in_context torus47 [0, 4, 2, 3, 8] [3, 0]).trans ((in_context torus53 [0, 4, 2, 3, 8, 6] [0]).trans ((in_context torus2014 [0, 4] [11, 0]).trans ((in_context torus91 [0, 4, 1, 2, 1, 7, 1] []).trans (in_context torus1 [0, 4, 1, 2, 1, 7] [11])))))
  have hr : V [8, 0, 5, 1, 2, 3, 2] = V [8, 0, 5, 1, 1, 2, 8] :=
    (in_context torus1436 [8, 0, 5, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13041 : V [1, 6, 5, 8, 1, 5, 12] = V [0, 5, 6, 3, 0, 6, 1] := by
  have h0 : V [6, 12, 4, 3, 5, 1, 2] = V [4, 0, 7, 1, 3, 0, 6, 1, 4, 1, 7, 0, 3, 1, 11] :=
    overlap torus2410 torus4274 [4, 0, 7, 1, 3, 0, 6, 1, 4] [4, 3, 5, 1, 2] (by decide)
  have hl : V [6, 12, 4, 3, 5, 1, 2] = V [1, 6, 5, 8, 1, 5, 12] :=
    ((in_context torus60 [6] [3, 5, 1, 2]).trans ((in_context torus54 [6, 7] [5, 1, 2]).trans ((in_context torus1469 [] [12, 5, 1, 2]).trans ((in_context torus1473 [] [12, 5, 1, 2]).trans ((in_context torus66 [1, 6, 5] [1, 2]).trans ((in_context torus94 [1, 6, 5, 8] [2]).trans (in_context torus48 [1, 6, 5, 8, 1] [])))))))
  have hr : V [4, 0, 7, 1, 3, 0, 6, 1, 4, 1, 7, 0, 3, 1, 11] = V [0, 5, 6, 3, 0, 6, 1] :=
    ((in_context torus2411 [] [1, 7, 0, 3, 1, 11]).trans ((in_context torus94 [6, 5] [7, 0, 3, 1, 11]).trans ((in_context torus1461 [] [12, 7, 0, 3, 1, 11]).trans ((in_context torus78 [0, 5, 6] [0, 3, 1, 11]).trans ((in_context torus93 [0, 5, 6, 3] [3, 1, 11]).trans ((in_context torus54 [0, 5, 6, 3, 0] [1, 11]).trans ((in_context torus94 [0, 5, 6, 3, 0, 6] [11]).trans (in_context torus29 [0, 5, 6, 3, 0, 6, 1] []))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus13067 : V [3, 5, 4, 6, 1, 2, 1] = V [1, 8, 0, 4, 6, 7, 11] := by
  have h0 : V [1, 8, 0, 4, 1, 11, 0, 2, 3] = V [3, 5, 4, 6, 1, 2, 1] :=
    overlap torus4282 torus1492 [3, 5, 4, 6, 1] [0, 2, 3] (by decide)
  have hl : V [1, 8, 0, 4, 1, 11, 0, 2, 3] = V [1, 8, 0, 4, 6, 7, 11] :=
    ((in_context torus91 [1, 8, 0, 4, 1] [2, 3]).trans ((in_context torus1 [1, 8, 0, 4] [11, 2, 3]).trans ((in_context torus47 [1, 8, 0, 4] [3]).trans (in_context torus53 [1, 8, 0, 4, 6] []))))
  have hr : V [3, 5, 4, 6, 1, 2, 1] = V [3, 5, 4, 6, 1, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13083 : V [3, 0, 5, 0, 7, 0, 8] = V [0, 6, 1, 2, 0, 6, 11] := by
  have h0 : V [0, 6, 1, 2, 0, 11, 2] = V [3, 0, 5, 0, 7, 0, 8] :=
    overlap torus4286 torus1609 [3, 0, 5] [2] (by decide)
  have hl : V [0, 6, 1, 2, 0, 11, 2] = V [0, 6, 1, 2, 0, 6, 11] :=
    (in_context torus47 [0, 6, 1, 2, 0] [])
  have hr : V [3, 0, 5, 0, 7, 0, 8] = V [3, 0, 5, 0, 7, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13352 : V [7, 0, 4, 1, 7, 0, 3] = V [1, 8, 7, 3, 5, 4, 12] := by
  have h0 : V [1, 8, 7, 3, 5, 4, 12] = V [7, 0, 4, 1, 7, 0, 3] :=
    overlap torus1490 torus4399 [7] [3, 5, 4, 12] (by decide)
  have hl : V [1, 8, 7, 3, 5, 4, 12] = V [1, 8, 7, 3, 5, 4, 12] :=
    rfl
  have hr : V [7, 0, 4, 1, 7, 0, 3] = V [7, 0, 4, 1, 7, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13428 : V [5, 0, 0, 3, 1, 7, 0] = V [0, 2, 1, 6, 0, 0, 4] := by
  have h0 : V [0, 2, 1, 6, 0, 12, 0, 8, 11] = V [5, 0, 0, 3, 1, 7, 0] :=
    overlap torus4420 torus3398 [5, 0] [0, 8, 11] (by decide)
  have hl : V [0, 2, 1, 6, 0, 12, 0, 8, 11] = V [0, 2, 1, 6, 0, 0, 4] :=
    ((in_context torus93 [0, 2, 1, 6, 0] [8, 11]).trans ((in_context torus84 [0, 2, 1, 6, 0, 0] [11]).trans (in_context torus29 [0, 2, 1, 6, 0, 0, 4] [])))
  have hr : V [5, 0, 0, 3, 1, 7, 0] = V [5, 0, 0, 3, 1, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13511 : V [6, 1, 3, 0, 6, 4, 6] = V [0, 6, 5, 0, 8, 6, 7] := by
  have h0 : V [0, 6, 5, 0, 8, 6, 7] = V [6, 1, 3, 0, 6, 4, 6] :=
    overlap torus4441 torus2010 [6, 1] [7] (by decide)
  have hl : V [0, 6, 5, 0, 8, 6, 7] = V [0, 6, 5, 0, 8, 6, 7] :=
    rfl
  have hr : V [6, 1, 3, 0, 6, 4, 6] = V [6, 1, 3, 0, 6, 4, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13532 : V [2, 0, 4, 0, 6, 1, 12] = V [1, 8, 7, 0, 4, 1, 7] := by
  have h0 : V [8, 2, 8, 0, 4, 1, 7] = V [2, 0, 2, 2, 4, 0, 6, 1, 12] :=
    overlap torus1438 torus4445 [2, 0, 2] [8, 0, 4, 1, 7] (by decide)
  have hl : V [8, 2, 8, 0, 4, 1, 7] = V [1, 8, 7, 0, 4, 1, 7] :=
    ((in_context torus1487 [] [0, 4, 1, 7]).trans (in_context torus1490 [] [0, 4, 1, 7]))
  have hr : V [2, 0, 2, 2, 4, 0, 6, 1, 12] = V [2, 0, 4, 0, 6, 1, 12] :=
    (in_context torus2 [2, 0] [4, 0, 6, 1, 12])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13581 : V [3, 0, 5, 0, 7, 1, 12] = V [1, 2, 8, 0, 5, 1, 8] := by
  have h0 : V [3, 0, 5, 0, 7, 1, 12] = V [1, 3, 2, 1, 2, 0, 5, 1, 8] :=
    overlap torus1711 torus4456 [1, 3, 2] [7, 1, 12] (by decide)
  have hl : V [3, 0, 5, 0, 7, 1, 12] = V [3, 0, 5, 0, 7, 1, 12] :=
    rfl
  have hr : V [1, 3, 2, 1, 2, 0, 5, 1, 8] = V [1, 2, 8, 0, 5, 1, 8] :=
    ((in_context torus1432 [1] [2, 0, 5, 1, 8]).trans ((in_context torus1 [] [2, 3, 2, 0, 5, 1, 8]).trans (in_context torus1436 [] [0, 5, 1, 8])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus13838 : V [4, 5, 3, 0, 6, 1, 3] = V [3, 1, 8, 0, 4, 3, 0] := by
  have h0 : V [4, 5, 3, 0, 6, 1, 3] = V [3, 1, 3, 3, 8, 0, 4, 3, 0] :=
    overlap torus4582 torus3714 [3, 1, 3] [1, 3] (by decide)
  have hl : V [4, 5, 3, 0, 6, 1, 3] = V [4, 5, 3, 0, 6, 1, 3] :=
    rfl
  have hr : V [3, 1, 3, 3, 8, 0, 4, 3, 0] = V [3, 1, 8, 0, 4, 3, 0] :=
    (in_context torus3 [3, 1] [8, 0, 4, 3, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem torus13902 : V [3, 2, 5, 0, 7, 1, 4] = V [0, 3, 2, 0, 5, 1, 11] := by
  have h0 : V [3, 1, 7, 7, 0, 2, 5, 0, 7, 1, 4] = V [0, 3, 2, 0, 5, 1, 2, 2, 11] :=
    overlap torus5223 torus5230 [0, 3, 2, 0, 5, 1, 2] [7, 0, 2, 5, 0, 7, 1, 4] (by decide)
  have hl : V [3, 1, 7, 7, 0, 2, 5, 0, 7, 1, 4] = V [3, 2, 5, 0, 7, 1, 4] :=
    ((in_context torus7 [3, 1] [0, 2, 5, 0, 7, 1, 4]).trans (in_context torus1 [3] [2, 5, 0, 7, 1, 4]))
  have hr : V [0, 3, 2, 0, 5, 1, 2, 2, 11] = V [0, 3, 2, 0, 5, 1, 11] :=
    (in_context torus2 [0, 3, 2, 0, 5, 1] [11])
  exact hl.symm.trans (h0.trans hr)

private theorem torus13922 : V [2, 1, 5, 0, 0, 8, 2] = V [1, 6, 0, 8, 0, 3, 12] := by
  have h0 : V [1, 6, 0, 0, 1, 8, 0, 3, 12] = V [2, 1, 5, 0, 0, 3, 1, 7, 0, 1, 7, 0, 3, 8, 2] :=
    overlap torus5384 torus4231 [2, 1, 5, 0, 0, 3, 1, 7, 0] [1, 8, 0, 3, 12] (by decide)
  have hl : V [1, 6, 0, 0, 1, 8, 0, 3, 12] = V [1, 6, 0, 8, 0, 3, 12] :=
    (in_context torus0 [1, 6, 0] [8, 0, 3, 12])
  have hr : V [2, 1, 5, 0, 0, 3, 1, 7, 0, 1, 7, 0, 3, 8, 2] = V [2, 1, 5, 0, 0, 8, 2] :=
    ((in_context torus0 [2, 1, 5, 0, 0, 3, 1, 7] [7, 0, 3, 8, 2]).trans ((in_context torus7 [2, 1, 5, 0, 0, 3, 1] [0, 3, 8, 2]).trans ((in_context torus1 [2, 1, 5, 0, 0, 3] [3, 8, 2]).trans (in_context torus3 [2, 1, 5, 0, 0] [8, 2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus13986 : V [3, 1, 8, 1, 6, 1, 11] = V [1, 7, 0, 4, 1, 7, 8] := by
  have h0 : V [1, 7, 11, 3, 0, 6, 1, 4, 1, 2, 1] = V [2, 4, 3, 5, 1, 2, 0, 6, 7, 1, 3, 4, 12] :=
    overlap torus3165 torus5794 [2, 4, 3, 5, 1, 2, 0, 6] [3, 0, 6, 1, 4, 1, 2, 1] (by decide)
  have hl : V [1, 7, 11, 3, 0, 6, 1, 4, 1, 2, 1] = V [3, 1, 8, 1, 6, 1, 11] :=
    ((in_context torus53 [1, 7] [0, 6, 1, 4, 1, 2, 1]).trans ((in_context torus7 [1] [11, 0, 6, 1, 4, 1, 2, 1]).trans ((in_context torus91 [1] [6, 1, 4, 1, 2, 1]).trans ((in_context torus1 [] [11, 6, 1, 4, 1, 2, 1]).trans ((in_context torus71 [] [1, 4, 1, 2, 1]).trans ((in_context torus92 [3] [4, 1, 2, 1]).trans ((in_context torus59 [3, 1] [1, 2, 1]).trans ((in_context torus92 [3, 1, 8] [2, 1]).trans ((in_context torus47 [3, 1, 8, 1] [1]).trans (in_context torus92 [3, 1, 8, 1, 6] []))))))))))
  have hr : V [2, 4, 3, 5, 1, 2, 0, 6, 7, 1, 3, 4, 12] = V [1, 7, 0, 4, 1, 7, 8] :=
    ((in_context torus3171 [] [7, 1, 3, 4, 12]).trans ((in_context torus77 [1, 7, 0] [1, 3, 4, 12]).trans ((in_context torus92 [1, 7, 0, 4] [3, 4, 12]).trans ((in_context torus53 [1, 7, 0, 4, 1] [4, 12]).trans ((in_context torus59 [1, 7, 0, 4, 1, 7] [12]).trans (in_context torus24 [1, 7, 0, 4, 1, 7, 8] []))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus14021 : V [5, 1, 2, 4, 1, 2, 1] = V [3, 4, 2, 4, 1, 7, 8] := by
  have h0 : V [5, 1, 2, 0, 12, 1, 8, 1, 6, 1, 11] = V [1, 3, 8, 2, 0, 4, 1, 7, 8] :=
    overlap torus3395 torus6028 [1, 3, 8, 2] [1, 8, 1, 6, 1, 11] (by decide)
  have hl : V [5, 1, 2, 0, 12, 1, 8, 1, 6, 1, 11] = V [5, 1, 2, 4, 1, 2, 1] :=
    ((in_context torus94 [5, 1, 2, 0] [8, 1, 6, 1, 11]).trans ((in_context torus0 [5, 1, 2] [12, 8, 1, 6, 1, 11]).trans ((in_context torus84 [5, 1, 2] [1, 6, 1, 11]).trans ((in_context torus94 [5, 1, 2, 4] [6, 1, 11]).trans ((in_context torus72 [5, 1, 2, 4, 1] [1, 11]).trans ((in_context torus94 [5, 1, 2, 4, 1, 2] [11]).trans (in_context torus29 [5, 1, 2, 4, 1, 2, 1] [])))))))
  have hr : V [1, 3, 8, 2, 0, 4, 1, 7, 8] = V [3, 4, 2, 4, 1, 7, 8] :=
    ((in_context torus1430 [1, 3] [4, 1, 7, 8]).trans ((in_context torus1439 [1] [2, 4, 1, 7, 8]).trans (in_context torus1 [] [3, 4, 2, 4, 1, 7, 8])))
  exact hl.symm.trans (h0.trans hr)

private theorem torus14071 : V [6, 7, 4, 0, 7, 1, 11] = V [1, 1, 7, 6, 2, 1, 6] := by
  have h0 : V [1, 7, 6, 2, 2, 1, 4, 0, 7, 1, 11] = V [0, 8, 2, 1, 7, 6, 0, 7, 8, 5, 7, 6, 8] :=
    overlap torus2433 torus6385 [0, 8, 2, 1, 7, 6, 0] [2, 1, 4, 0, 7, 1, 11] (by decide)
  have hl : V [1, 7, 6, 2, 2, 1, 4, 0, 7, 1, 11] = V [6, 7, 4, 0, 7, 1, 11] :=
    ((in_context torus2 [1, 7, 6] [1, 4, 0, 7, 1, 11]).trans ((in_context torus1470 [1] [4, 0, 7, 1, 11]).trans (in_context torus1 [] [6, 7, 4, 0, 7, 1, 11])))
  have hr : V [0, 8, 2, 1, 7, 6, 0, 7, 8, 5, 7, 6, 8] = V [1, 1, 7, 6, 2, 1, 6] :=
    ((in_context torus3063 [] [7, 8, 5, 7, 6, 8]).trans ((in_context torus237 [1, 7] [6, 8]).trans ((in_context torus1429 [1, 7] [4, 5, 6, 8]).trans ((in_context torus1863 [1] [5, 6, 8]).trans ((in_context torus1466 [1, 5, 7, 1, 4] [8]).trans (in_context torus6120 [1] []))))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus14147 : V [5, 6, 1, 3, 0, 6, 0] = V [0, 5, 0, 8, 1, 5, 6] := by
  have h0 : V [5, 4, 4, 6, 1, 3, 0, 6, 0] = V [3, 0, 6, 4, 6, 5, 7, 1, 4, 7, 6, 8, 1, 5, 6] :=
    overlap torus2155 torus7019 [3, 0, 6, 4, 6, 5, 7, 1, 4] [4, 6, 1, 3, 0, 6, 0] (by decide)
  have hl : V [5, 4, 4, 6, 1, 3, 0, 6, 0] = V [5, 6, 1, 3, 0, 6, 0] :=
    (in_context torus4 [5] [6, 1, 3, 0, 6, 0])
  have hr : V [3, 0, 6, 4, 6, 5, 7, 1, 4, 7, 6, 8, 1, 5, 6] = V [0, 5, 0, 8, 1, 5, 6] :=
    ((in_context torus4577 [] [1, 4, 7, 6, 8, 1, 5, 6]).trans ((in_context torus0 [5, 4, 6, 4] [4, 7, 6, 8, 1, 5, 6]).trans ((in_context torus4 [5, 4, 6] [7, 6, 8, 1, 5, 6]).trans ((in_context torus1605 [] [6, 8, 1, 5, 6]).trans (in_context torus6 [0, 5, 0] [8, 1, 5, 6])))))
  exact hl.symm.trans (h0.trans hr)

private theorem torus14155 : V [2, 3, 1, 6, 0, 3, 12] = V [1, 8, 1, 6, 1, 4, 0] := by
  have h0 : V [2, 3, 1, 6, 0, 3, 12] = V [1, 8, 1, 6, 1, 4, 0] :=
    overlap torus7092 torus24 [1, 8, 1, 6, 1, 4, 0] [12] (by decide)
  have hl : V [2, 3, 1, 6, 0, 3, 12] = V [2, 3, 1, 6, 0, 3, 12] :=
    rfl
  have hr : V [1, 8, 1, 6, 1, 4, 0] = V [1, 8, 1, 6, 1, 4, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus14156 : V [5, 6, 1, 2, 0, 6, 12] = V [1, 4, 1, 2, 1, 7, 0] := by
  have h0 : V [1, 12, 8, 1, 6, 1, 4, 0, 11] = V [12, 2, 3, 1, 6, 0, 3] :=
    overlap torus94 torus7092 [12] [8, 1, 6, 1, 4, 0, 11] (by decide)
  have hl : V [1, 12, 8, 1, 6, 1, 4, 0, 11] = V [1, 4, 1, 2, 1, 7, 0] :=
    ((in_context torus84 [1] [1, 6, 1, 4, 0, 11]).trans ((in_context torus94 [1, 4] [6, 1, 4, 0, 11]).trans ((in_context torus72 [1, 4, 1] [1, 4, 0, 11]).trans ((in_context torus94 [1, 4, 1, 2] [4, 0, 11]).trans ((in_context torus60 [1, 4, 1, 2, 1] [0, 11]).trans ((in_context torus93 [1, 4, 1, 2, 1, 7] [11]).trans (in_context torus29 [1, 4, 1, 2, 1, 7, 0] [])))))))
  have hr : V [12, 2, 3, 1, 6, 0, 3] = V [5, 6, 1, 2, 0, 6, 12] :=
    ((in_context torus48 [] [3, 1, 6, 0, 3]).trans ((in_context torus54 [5] [1, 6, 0, 3]).trans ((in_context torus94 [5, 6] [6, 0, 3]).trans ((in_context torus72 [5, 6, 1] [0, 3]).trans ((in_context torus93 [5, 6, 1, 2] [3]).trans (in_context torus54 [5, 6, 1, 2, 0] []))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus14163 : V [2, 3, 7, 0, 3, 1, 6] = V [1, 1, 3, 2, 5, 1, 12] := by
  have h0 : V [2, 3, 7, 0, 3, 1, 6] = V [1, 1, 3, 2, 5, 1, 12] :=
    overlap torus1 torus7112 [1] [2, 3, 7, 0, 3, 1, 6] (by decide)
  have hl : V [2, 3, 7, 0, 3, 1, 6] = V [2, 3, 7, 0, 3, 1, 6] :=
    rfl
  have hr : V [1, 1, 3, 2, 5, 1, 12] = V [1, 1, 3, 2, 5, 1, 12] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus14193 : V [3, 4, 8, 0, 4, 1, 7] = V [1, 1, 4, 3, 6, 1, 12] := by
  have h0 : V [1, 3, 8, 2, 2, 8, 4, 0, 6, 1, 12] = V [3, 4, 2, 2, 8, 0, 4, 1, 7] :=
    overlap torus1592 torus7494 [3, 4, 2] [2, 8, 4, 0, 6, 1, 12] (by decide)
  have hl : V [1, 3, 8, 2, 2, 8, 4, 0, 6, 1, 12] = V [1, 1, 4, 3, 6, 1, 12] :=
    ((in_context torus2 [1, 3, 8] [8, 4, 0, 6, 1, 12]).trans ((in_context torus8 [1, 3] [4, 0, 6, 1, 12]).trans (in_context torus1455 [1] [6, 1, 12])))
  have hr : V [3, 4, 2, 2, 8, 0, 4, 1, 7] = V [3, 4, 8, 0, 4, 1, 7] :=
    (in_context torus2 [3, 4] [8, 0, 4, 1, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus14207 : V [4, 1, 2, 1, 7, 0, 11] = V [0, 5, 6, 1, 2, 0, 6] := by
  have h0 : V [4, 1, 5, 5, 2, 1, 7, 0, 11] = V [5, 4, 5, 1, 2, 0, 6] :=
    overlap torus1503 torus7573 [5] [5, 2, 1, 7, 0, 11] (by decide)
  have hl : V [4, 1, 5, 5, 2, 1, 7, 0, 11] = V [4, 1, 2, 1, 7, 0, 11] :=
    (in_context torus5 [4, 1] [2, 1, 7, 0, 11])
  have hr : V [5, 4, 5, 1, 2, 0, 6] = V [0, 5, 6, 1, 2, 0, 6] :=
    (in_context torus1457 [] [1, 2, 0, 6])
  exact hl.symm.trans (h0.trans hr)

private theorem torus14252 : V [8, 7, 3, 4, 1, 2, 8] = V [0, 7, 2, 0, 0, 3, 4] := by
  have h0 : V [8, 7, 3, 4, 1, 2, 8] = V [0, 7, 2, 0, 0, 3, 4] :=
    overlap torus0 torus8040 [0] [8, 7, 3, 4, 1, 2, 8] (by decide)
  have hl : V [8, 7, 3, 4, 1, 2, 8] = V [8, 7, 3, 4, 1, 2, 8] :=
    rfl
  have hr : V [0, 7, 2, 0, 0, 3, 4] = V [0, 7, 2, 0, 0, 3, 4] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem torus14302 : V [5, 6, 1, 2, 0, 6, 1] = V [1, 4, 1, 2, 1, 7, 11] := by
  have h0 : V [1, 4, 1, 2, 4, 1, 0, 4, 1, 7, 11] = V [5, 6, 1, 2, 4, 2, 3, 0, 3, 5, 4, 6, 1] :=
    overlap torus8202 torus4442 [5, 6, 1, 2, 4, 2, 3] [0, 4, 1, 7, 11] (by decide)
  have hl : V [1, 4, 1, 2, 4, 1, 0, 4, 1, 7, 11] = V [1, 4, 1, 2, 1, 7, 11] :=
    ((in_context torus1 [1, 4, 1, 2, 4] [4, 1, 7, 11]).trans (in_context torus4 [1, 4, 1, 2] [1, 7, 11]))
  have hr : V [5, 6, 1, 2, 4, 2, 3, 0, 3, 5, 4, 6, 1] = V [5, 6, 1, 2, 0, 6, 1] :=
    ((in_context torus1446 [5, 6, 1, 2, 4] [3, 5, 4, 6, 1]).trans ((in_context torus1554 [5, 6, 1, 2] [3, 5, 4, 6, 1]).trans ((in_context torus3 [5, 6, 1, 2, 0, 4, 5] [5, 4, 6, 1]).trans ((in_context torus5 [5, 6, 1, 2, 0, 4] [4, 6, 1]).trans (in_context torus4 [5, 6, 1, 2, 0] [6, 1])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem torus14944 : V [4, 1, 5, 1, 8, 0, 5, 1] = V [5, 2, 7, 8, 6, 11] := by
  have h0 : V [4, 1, 5, 1, 8, 0, 5, 1] = V [5, 0, 1, 2, 7, 8, 6, 11] :=
    overlap torus1503 torus4298 [5, 0] [1, 8, 0, 5, 1] (by decide)
  have hl : V [4, 1, 5, 1, 8, 0, 5, 1] = V [4, 1, 5, 1, 8, 0, 5, 1] :=
    rfl
  have hr : V [5, 0, 1, 2, 7, 8, 6, 11] = V [5, 2, 7, 8, 6, 11] :=
    (in_context torus0 [5] [2, 7, 8, 6, 11])
  exact hl.symm.trans (h0.trans hr)

private theorem torus15037 : V [2, 3, 8, 0, 4, 1, 2, 12] = V [4, 0, 6, 1, 3, 5, 9] := by
  have h0 : V [8, 3, 1, 12, 2, 3, 8, 0, 4, 1, 7, 0] = V [2, 7, 1, 5, 0, 8, 1, 0, 6, 12] :=
    overlap torus3359 torus3169 [2, 7, 1, 5, 0, 8, 1] [2, 3, 8, 0, 4, 1, 7, 0] (by decide)
  have hl : V [8, 3, 1, 12, 2, 3, 8, 0, 4, 1, 7, 0] = V [4, 0, 6, 1, 3, 5, 9] :=
    ((in_context torus48 [8, 3, 1] [3, 8, 0, 4, 1, 7, 0]).trans ((in_context torus54 [8, 3, 1, 5] [8, 0, 4, 1, 7, 0]).trans ((in_context torus84 [8, 3, 1, 5, 6] [0, 4, 1, 7, 0]).trans ((in_context torus93 [8, 3, 1, 5, 6, 4] [4, 1, 7, 0]).trans ((in_context torus60 [8, 3, 1, 5, 6, 4, 0] [1, 7, 0]).trans ((in_context torus94 [8, 3, 1, 5, 6, 4, 0, 7] [7, 0]).trans ((in_context torus78 [8, 3, 1, 5, 6, 4, 0, 7, 1] [0]).trans ((in_context torus3344 [8, 3, 1] [12, 0]).trans ((in_context torus30 [8, 3, 1, 7, 0, 2, 1] [0]).trans ((in_context torus87 [8, 3, 1, 7, 0, 2, 1] []).trans ((in_context torus1 [8, 3, 1, 7, 0, 2] [9]).trans (in_context torus4380 [] [9]))))))))))))
  have hr : V [2, 7, 1, 5, 0, 8, 1, 0, 6, 12] = V [2, 3, 8, 0, 4, 1, 2, 12] :=
    ((in_context torus1 [2, 7, 1, 5, 0, 8] [6, 12]).trans (in_context torus3909 [2] [12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17941 : V [2, 4, 0, 6, 1, 3, 5, 10] = V [3, 8, 0, 4, 1, 2, 13] := by
  have h0 : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6] = V [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5] :=
    relation_split _ seventeenth_seventh false 0 _ _ (by decide)
  have hl : V [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6] = V [3, 8, 0, 4, 1, 2, 13] :=
    ((in_context torus1408 [] [3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1429 [7] [4, 5, 6, 12, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1863 [] [5, 6, 12, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1466 [5, 7, 1, 4] [12, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus10549 [] [12, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus54 [1, 7, 6, 2, 1, 6, 8] [2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus9755 [1] [12, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1 [] [5, 7, 1, 4, 6, 5, 12, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4225 [5] [2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus3441 [5] [8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus84 [5, 7, 1, 4, 6] [7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2024 [5] [12, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus5 [] [7, 2, 0, 2, 12, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus78 [7, 2, 0, 2] [6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1438 [7] [12, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus72 [7, 8, 2] [5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2 [7, 8] [12, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus66 [7, 8] [4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus8 [7] [12, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus60 [7] [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus7 [] [12, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus72 [] [5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus66 [2] [4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus60 [2, 8] [3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus54 [2, 8, 7] [2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1480 [2] [12, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus48 [2, 7, 1, 7] [8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus84 [2, 7, 1, 7, 5] [7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1989 [2] [12, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus78 [2, 3, 8, 0, 4, 2] [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus10301 [] [12, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus72 [0, 2, 3, 7, 0, 3, 8] [5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus7999 [] [12, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus66 [4, 2, 0, 5, 1, 3] [4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4228 [4] [12, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus11152 [] [12, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus15037 [] [4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus57 [4, 0, 6, 1, 3, 5] [3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2022 [4, 0] [9, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1449 [] [6, 7, 8, 2, 9, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1805 [3] [2, 9, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus9740 [] [9, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus51 [1, 3, 2, 5, 1, 2, 4] [2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2018 [1, 3, 2] [9, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1439 [1] [5, 6, 7, 8, 9, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1 [] [3, 4, 5, 6, 7, 8, 9, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1805 [3] [9, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus45 [3, 2, 4, 1, 8, 3] [8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2074 [3, 2] [9, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2 [3] [4, 5, 6, 7, 9, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus81 [3, 4, 5, 6, 7] [7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus7 [3, 4, 5, 6] [9, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus75 [3, 4, 5, 6] [6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus6 [3, 4, 5] [9, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus69 [3, 4, 5] [5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus5 [3, 4] [9, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus63 [3, 4] [4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4 [3] [9, 4, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus57 [3] [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus3 [] [9, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus69 [] [5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus63 [5] [4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus57 [5, 4] [3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1453 [] [9, 3, 2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus51 [4, 1, 4] [2, 8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus45 [4, 1, 4, 2] [8, 7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus81 [4, 1, 4, 2, 8] [7, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus75 [4, 1, 4, 2, 8, 7] [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1480 [4, 1, 4, 2] [9, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1998 [4, 1] [9, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus10378 [] [9, 6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus69 [0, 5, 6, 3, 0, 6, 4] [5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus8529 [] [9, 5, 4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus63 [4, 1, 2, 0, 5, 3] [4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4841 [4] [4, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus61 [4, 6, 1, 3, 0, 5] [3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus10939 [] [13, 3, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus55 [1, 6, 5, 8, 1, 5, 7] [2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1972 [1, 6, 5] [13, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1466 [1] [2, 0, 2, 4, 13, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1 [] [6, 7, 2, 0, 2, 4, 13, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus1839 [] [4, 13, 2, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus49 [4, 6, 1, 3, 5, 4] [8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4 [4, 6, 1, 3, 5] [13, 8, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus85 [4, 6, 1, 3, 5] [7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2022 [4] [13, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus4 [] [6, 7, 8, 2, 13, 7, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus79 [6, 7, 8, 2] [6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus2 [6, 7, 8] [13, 6, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus73 [6, 7, 8] [5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus8 [6, 7] [13, 5, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus67 [6, 7] [4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus7 [6] [13, 4, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus61 [6] [6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus6 [] [13, 6, 5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus73 [] [5, 4, 3, 2, 8, 7, 6]).trans ((in_context torus67 [8] [4, 3, 2, 8, 7, 6]).trans ((in_context torus61 [8, 7] [3, 2, 8, 7, 6]).trans ((in_context torus1480 [] [13, 3, 2, 8, 7, 6]).trans ((in_context torus55 [7, 1, 7] [2, 8, 7, 6]).trans ((in_context torus49 [7, 1, 7, 5] [8, 7, 6]).trans ((in_context torus1989 [] [13, 8, 7, 6]).trans ((in_context torus85 [3, 8, 0, 4, 2] [7, 6]).trans ((in_context torus79 [3, 8, 0, 4, 2, 3] [6]).trans ((in_context torus1436 [3, 8, 0, 4] [13, 6]).trans ((in_context torus10286 [] [13, 6]).trans ((in_context torus73 [0, 8, 2, 6, 0, 2, 7] []).trans ((in_context torus11151 [0] [13]).trans (in_context torus0 [] [3, 8, 0, 4, 1, 2, 13])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have hr : V [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5] = V [2, 4, 0, 6, 1, 3, 5, 10] :=
    ((in_context torus1423 [] [6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1434 [] [7, 6, 5, 4, 3, 11, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1471 [2, 1, 2] [4, 3, 11, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10326 [] [3, 11, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus8078 [] [11, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus71 [2, 1, 7, 0, 3, 8] [7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1988 [2, 1] [11, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10326 [] [11, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus77 [0, 3, 4, 8, 0, 4, 2] [8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus2001 [0, 3, 4] [11, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1442 [0] [7, 1, 7, 5, 11, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1437 [] [7, 1, 7, 5, 11, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1866 [] [5, 11, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1471 [2, 1, 2] [11, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus83 [2, 1, 2, 6, 1, 6] [2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1472 [2, 1, 2] [11, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus47 [2, 1, 2, 7, 6] [3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus6 [2, 1, 2, 7] [11, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus53 [2, 1, 2, 7] [4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus7 [2, 1, 2] [11, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus59 [2, 1, 2] [5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1435 [] [11, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus65 [3, 2] [6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus2 [3] [11, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus71 [3] [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus3 [] [11, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus59 [] [5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus65 [8] [6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus71 [8, 2] [7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1429 [] [11, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus77 [2, 0, 2] [8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus83 [2, 0, 2, 4] [2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus47 [2, 0, 2, 4, 5] [3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus53 [2, 0, 2, 4, 5, 6] [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10572 [] [11, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus59 [1, 8, 7, 3, 1, 7, 2] [5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus11371 [1] [11, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1 [] [2, 0, 4, 1, 8, 3, 11, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus65 [2, 0, 4, 1, 8, 3] [6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus4670 [2] [6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus74 [2, 7, 0, 3, 1, 8] [7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10717 [] [14, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus80 [0, 7, 8, 5, 0, 8, 6] [8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10630 [0] [14, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus0 [] [2, 7, 0, 3, 8, 2, 14, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus86 [2, 7, 0, 3, 8, 2] [2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus2 [2, 7, 0, 3, 8] [14, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus50 [2, 7, 0, 3, 8] [3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1988 [2] [14, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus2 [] [6, 1, 6, 4, 14, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus56 [6, 1, 6, 4] [4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus4 [6, 1, 6] [14, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus62 [6, 1, 6] [5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1472 [] [14, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus68 [7, 6] [6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus6 [7] [14, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus74 [7] [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus7 [] [14, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus62 [] [5, 6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus68 [5] [6, 7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus74 [5, 6] [7, 8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus80 [5, 6, 7] [8, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus86 [5, 6, 7, 8] [2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1823 [] [14, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus50 [3, 5, 1, 2, 4] [3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus56 [3, 5, 1, 2, 4, 3] [4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1448 [3, 5, 1, 2] [14, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus11000 [] [14, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus62 [1, 5, 4, 7, 1, 4, 6] [5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus8968 [] [14, 5, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus68 [3, 5, 1, 2, 0, 4] [6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus4203 [3] [14, 6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus26 [3, 1, 8, 0, 4, 2] [6, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus70 [3, 1, 8, 0, 4, 2] [7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus2001 [3, 1] [10, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10351 [] [10, 7, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus76 [0, 4, 5, 2, 0, 5, 3] [8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus10346 [0] [10, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus0 [] [3, 1, 3, 7, 1, 7, 10, 8, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus82 [3, 1, 3, 7, 1, 7] [2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1481 [3, 1, 3] [10, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus46 [3, 1, 3, 8, 7] [3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus7 [3, 1, 3, 8] [10, 3, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus52 [3, 1, 3, 8] [4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus8 [3, 1, 3] [10, 4, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus58 [3, 1, 3] [5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus1445 [] [10, 5, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus64 [4, 3] [6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus3 [4] [10, 6, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus70 [4] [4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus4 [] [10, 4, 5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus58 [] [5, 6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus64 [2] [6, 7, 8, 2, 3, 4, 5]).trans ((in_context torus70 [2, 3] [7, 8, 2, 3, 4, 5]).trans ((in_context torus76 [2, 3, 4] [8, 2, 3, 4, 5]).trans ((in_context torus82 [2, 3, 4, 5] [2, 3, 4, 5]).trans ((in_context torus46 [2, 3, 4, 5, 6] [3, 4, 5]).trans ((in_context torus52 [2, 3, 4, 5, 6, 7] [4, 5]).trans ((in_context torus1805 [2, 3] [10, 4, 5]).trans ((in_context torus1436 [] [4, 1, 8, 3, 10, 4, 5]).trans ((in_context torus58 [1, 2, 8, 4, 1, 8, 3] [5]).trans ((in_context torus8159 [] [10, 5]).trans ((in_context torus64 [3, 0, 5, 1, 2, 4] []).trans (in_context torus10547 [] [10]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17969 : V [0, 3, 0, 5, 1, 1, 3, 2, 5, 14] = V [8, 1, 7, 0, 2, 7, 8, 13] := by
  have h0 : V [0, 8, 2, 7, 0, 8, 4, 0, 6, 1, 3, 5, 10] = V [1, 7, 6, 8, 7, 3, 8, 0, 4, 1, 2, 13] :=
    overlap torus4140 focused17941 [1, 7, 6, 8, 7] [4, 0, 6, 1, 3, 5, 10] (by decide)
  have hl : V [0, 8, 2, 7, 0, 8, 4, 0, 6, 1, 3, 5, 10] = V [0, 3, 0, 5, 1, 1, 3, 2, 5, 14] :=
    ((in_context torus2844 [0, 8, 2, 7, 0] [10]).trans ((in_context torus4277 [0] [7, 0, 2, 10]).trans ((in_context torus78 [0, 3, 0, 5, 1, 2] [0, 2, 10]).trans ((in_context torus93 [0, 3, 0, 5, 1, 2, 3] [2, 10]).trans ((in_context torus1446 [0, 3, 0, 5, 1] [12, 2, 10]).trans ((in_context torus48 [0, 3, 0, 5, 1, 1, 3, 2] [10]).trans (in_context torus28 [0, 3, 0, 5, 1, 1, 3, 2, 5] [])))))))
  have hr : V [1, 7, 6, 8, 7, 3, 8, 0, 4, 1, 2, 13] = V [8, 1, 7, 0, 2, 7, 8, 13] :=
    ((in_context torus1992 [1, 7, 6, 8] [1, 2, 13]).trans ((in_context torus4269 [] [5, 4, 2, 1, 2, 13]).trans ((in_context torus1616 [0, 8, 2] [4, 2, 1, 2, 13]).trans ((in_context torus1553 [0, 8, 2, 1, 7, 1, 6] [13]).trans ((in_context torus4199 [0, 8, 2, 1] [8, 13]).trans ((in_context torus1 [0, 8, 2] [7, 6, 0, 2, 7, 8, 13]).trans (in_context torus1620 [] [0, 2, 7, 8, 13])))))))
  exact hl.symm.trans (h0.trans hr)

private theorem focused17970 : V [1, 7, 0, 3, 5, 6, 4, 0, 6, 4, 5, 9] = V [0, 5, 4, 0, 5, 1, 3, 5, 14] := by
  have h0 : V [2, 4, 3, 5, 3, 0, 5, 1, 1, 3, 2, 5, 14] = V [4, 1, 8, 3, 2, 4, 2, 8, 1, 7, 0, 2, 7, 8, 13] :=
    overlap torus2454 focused17969 [4, 1, 8, 3, 2, 4, 2] [3, 0, 5, 1, 1, 3, 2, 5, 14] (by decide)
  have hl : V [2, 4, 3, 5, 3, 0, 5, 1, 1, 3, 2, 5, 14] = V [0, 5, 4, 0, 5, 1, 3, 5, 14] :=
    ((in_context torus3843 [] [5, 1, 1, 3, 2, 5, 14]).trans ((in_context torus1461 [0, 5, 3, 5, 4] [1, 3, 2, 5, 14]).trans ((in_context torus1561 [0, 5, 3, 5] [1, 3, 2, 5, 14]).trans ((in_context torus1546 [0, 5, 3] [5, 1, 3, 2, 5, 14]).trans ((in_context torus3299 [0, 5] [3, 2, 5, 14]).trans ((in_context torus1442 [0, 5, 4, 0, 5] [2, 5, 14]).trans ((in_context torus1446 [0, 5, 4, 0, 5] [2, 5, 14]).trans (in_context torus2 [0, 5, 4, 0, 5, 1, 3] [5, 14]))))))))
  have hr : V [4, 1, 8, 3, 2, 4, 2, 8, 1, 7, 0, 2, 7, 8, 13] = V [1, 7, 0, 3, 5, 6, 4, 0, 6, 4, 5, 9] :=
    ((in_context torus2980 [] [8, 1, 7, 0, 2, 7, 8, 13]).trans ((in_context torus11830 [] [7, 0, 2, 7, 8, 13]).trans ((in_context torus77 [1, 7, 0, 3, 5, 6] [0, 2, 7, 8, 13]).trans ((in_context torus91 [1, 7, 0, 3, 5, 6, 4] [2, 7, 8, 13]).trans ((in_context torus47 [1, 7, 0, 3, 5, 6, 4, 0] [7, 8, 13]).trans ((in_context torus77 [1, 7, 0, 3, 5, 6, 4, 0, 6] [8, 13]).trans ((in_context torus83 [1, 7, 0, 3, 5, 6, 4, 0, 6, 4] [13]).trans (in_context torus25 [1, 7, 0, 3, 5, 6, 4, 0, 6, 4, 5] []))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17971 : V [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12] = V [0, 4, 5, 3, 6, 5, 8, 2, 1, 6, 8, 11] := by
  have h0 : V [1, 8, 0, 4, 6, 7, 11, 7, 0, 3, 5, 6, 4, 0, 6, 4, 5, 9] = V [3, 5, 4, 6, 1, 2, 0, 5, 4, 0, 5, 1, 3, 5, 14] :=
    overlap torus13067 focused17970 [3, 5, 4, 6, 1, 2] [7, 0, 3, 5, 6, 4, 0, 6, 4, 5, 9] (by decide)
  have hl : V [1, 8, 0, 4, 6, 7, 11, 7, 0, 3, 5, 6, 4, 0, 6, 4, 5, 9] = V [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12] :=
    ((in_context torus77 [1, 8, 0, 4, 6, 7] [0, 3, 5, 6, 4, 0, 6, 4, 5, 9]).trans ((in_context torus91 [1, 8, 0, 4, 6, 7, 4] [3, 5, 6, 4, 0, 6, 4, 5, 9]).trans ((in_context torus53 [1, 8, 0, 4, 6, 7, 4, 0] [5, 6, 4, 0, 6, 4, 5, 9]).trans ((in_context torus65 [1, 8, 0, 4, 6, 7, 4, 0, 7] [6, 4, 0, 6, 4, 5, 9]).trans ((in_context torus71 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2] [4, 0, 6, 4, 5, 9]).trans ((in_context torus59 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3] [0, 6, 4, 5, 9]).trans ((in_context torus91 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8] [6, 4, 5, 9]).trans ((in_context torus71 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0] [4, 5, 9]).trans ((in_context torus59 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3] [5, 9]).trans ((in_context torus65 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8] [9]).trans (in_context torus21 [1, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2] [])))))))))))
  have hr : V [3, 5, 4, 6, 1, 2, 0, 5, 4, 0, 5, 1, 3, 5, 14] = V [0, 4, 5, 3, 6, 5, 8, 2, 1, 6, 8, 11] :=
    ((in_context torus11414 [3, 5, 4] [5, 1, 3, 5, 14]).trans ((in_context torus1452 [3] [3, 0, 5, 8, 7, 12, 5, 1, 3, 5, 14]).trans ((in_context torus1550 [] [3, 0, 5, 8, 7, 12, 5, 1, 3, 5, 14]).trans ((in_context torus3470 [] [5, 8, 7, 12, 5, 1, 3, 5, 14]).trans ((in_context torus1457 [0, 4, 5, 3] [8, 7, 12, 5, 1, 3, 5, 14]).trans ((in_context torus66 [0, 4, 5, 3, 0, 5, 6, 8, 7] [1, 3, 5, 14]).trans ((in_context torus1484 [0, 4, 5, 3, 0, 5, 6] [12, 1, 3, 5, 14]).trans ((in_context torus1465 [0, 4, 5, 3] [8, 2, 12, 1, 3, 5, 14]).trans ((in_context torus94 [0, 4, 5, 3, 6, 5, 8, 2] [3, 5, 14]).trans ((in_context torus54 [0, 4, 5, 3, 6, 5, 8, 2, 1] [5, 14]).trans ((in_context torus66 [0, 4, 5, 3, 6, 5, 8, 2, 1, 6] [14]).trans (in_context torus32 [0, 4, 5, 3, 6, 5, 8, 2, 1, 6, 8] []))))))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem focused17972 : V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5, 6] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4] := by
  have h0 : V [5, 2, 7, 8, 6, 11, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12] = V [4, 1, 5, 1, 8, 0, 5, 0, 4, 5, 3, 6, 5, 8, 2, 1, 6, 8, 11] :=
    overlap torus14944 focused17971 [4, 1, 5, 1, 8, 0, 5] [8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12] (by decide)
  have hl : V [5, 2, 7, 8, 6, 11, 8, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12] = V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5, 6] :=
    ((in_context torus83 [5, 2, 7, 8, 6] [0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus1616 [5, 2] [11, 0, 4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus91 [5, 2, 1, 7, 1, 6] [4, 6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus59 [5, 2, 1, 7, 1, 6, 0] [6, 7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus71 [5, 2, 1, 7, 1, 6, 0, 8] [7, 4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus77 [5, 2, 1, 7, 1, 6, 0, 8, 3] [4, 0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus59 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4] [0, 7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus91 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8] [7, 2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus77 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0] [2, 3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus47 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4] [3, 8, 0, 3, 8, 2, 12]).trans ((in_context torus53 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6] [8, 0, 3, 8, 2, 12]).trans ((in_context torus83 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7] [0, 3, 8, 2, 12]).trans ((in_context torus91 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] [3, 8, 2, 12]).trans ((in_context torus53 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0] [8, 2, 12]).trans ((in_context torus83 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] [2, 12]).trans ((in_context torus47 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] [12]).trans (in_context torus24 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5, 6] [])))))))))))))))))
  have hr : V [4, 1, 5, 1, 8, 0, 5, 0, 4, 5, 3, 6, 5, 8, 2, 1, 6, 8, 11] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4] :=
    ((in_context torus1496 [4, 1, 5, 1, 8, 0] [3, 6, 5, 8, 2, 1, 6, 8, 11]).trans ((in_context torus4391 [4, 1] [3, 6, 5, 8, 2, 1, 6, 8, 11]).trans ((in_context torus54 [4, 1, 1, 2, 4, 3, 5] [6, 5, 8, 2, 1, 6, 8, 11]).trans ((in_context torus1603 [4, 1, 1, 2] [12, 6, 5, 8, 2, 1, 6, 8, 11]).trans ((in_context torus72 [4, 1, 1, 2, 0, 4, 0, 5] [5, 8, 2, 1, 6, 8, 11]).trans ((in_context torus66 [4, 1, 1, 2, 0, 4, 0, 5, 2] [8, 2, 1, 6, 8, 11]).trans ((in_context torus84 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8] [2, 1, 6, 8, 11]).trans ((in_context torus48 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4] [1, 6, 8, 11]).trans ((in_context torus94 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5] [6, 8, 11]).trans ((in_context torus72 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1] [8, 11]).trans ((in_context torus84 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2] [11]).trans (in_context torus29 [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4] []))))))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem focused17973 : V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6] := by
  have h0 : V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6] = V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] :=
    overlap focused17972 torus6 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] [6] (by decide)
  have hl : V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6] :=
    rfl
  have hr : V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] = V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17974 : V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] := by
  have h0 : V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] :=
    overlap focused17973 torus5 [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] [5] (by decide)
  have hl : V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] :=
    rfl
  have hr : V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [5, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17975 : V [3, 0, 4, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] := by
  have h0 : V [2, 3, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [7, 1, 7, 4, 6, 1, 3, 4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] :=
    overlap torus1840 focused17974 [7, 1, 7, 4, 6, 1, 3] [2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] (by decide)
  have hl : V [2, 3, 2, 1, 7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] :=
    ((in_context torus1431 [] [7, 1, 6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7]).trans ((in_context torus1598 [] [6, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7]).trans ((in_context torus1469 [1, 8] [0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7]).trans (in_context torus1473 [1, 8] [0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7]))))
  have hr : V [7, 1, 7, 4, 6, 1, 3, 4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [3, 0, 4, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] :=
    ((in_context torus1842 [] [1, 3, 4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans ((in_context torus0 [2, 3, 5, 3] [3, 4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans ((in_context torus3 [2, 3, 5] [4, 1, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans ((in_context torus1452 [2, 3] [1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans ((in_context torus1446 [] [4, 5, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans (in_context torus1518 [] [1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17977 : V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5] := by
  have h0 : V [0, 4, 5, 3, 5, 4, 4, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] :=
    overlap torus3470 focused17975 [1, 3, 2, 4] [4, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] (by decide)
  have hl : V [0, 4, 5, 3, 5, 4, 4, 1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5] = V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5] :=
    ((in_context torus4 [0, 4, 5, 3, 5] [1, 2, 0, 4, 0, 5, 2, 8, 4, 5, 1, 2, 4, 6, 5]).trans ((in_context torus5543 [0, 4] [2, 8, 4, 5, 1, 2, 4, 6, 5]).trans (in_context torus4 [0] [6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5])))
  have hr : V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] = V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17986 : V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] = V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] := by
  have h0 : V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 8, 7, 6, 7] = V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 3, 4, 3, 2, 3] :=
    overlap focused17977 torus129 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0] [8, 7, 6, 7] (by decide)
  have hl : V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 8, 7, 6, 7] = V [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] :=
    ((in_context torus1480 [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5] [7]).trans (in_context torus7 [0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] []))
  have hr : V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 0, 3, 4, 3, 2, 3] = V [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] :=
    ((in_context torus1562 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] [3, 2, 3]).trans ((in_context torus1948 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4] [1, 3, 2, 3]).trans ((in_context torus1563 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1, 6, 1] [2, 3]).trans ((in_context torus1932 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] [2, 2, 3]).trans ((in_context torus1 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4] [6, 7, 5, 3, 2, 2, 3]).trans ((in_context torus2 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5, 3] [3]).trans (in_context torus3 [1, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] [])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17995 : V [3, 1, 8, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] := by
  have h0 : V [1, 4, 2, 3, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] = V [4, 5, 3, 0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] :=
    overlap torus1594 focused17986 [4, 5, 3] [3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] (by decide)
  have hl : V [1, 4, 2, 3, 3, 2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] :=
    ((in_context torus3 [1, 4, 2] [2, 4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5]).trans ((in_context torus2 [1, 4] [4, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5]).trans (in_context torus4 [1] [1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5])))
  have hr : V [4, 5, 3, 0, 6, 1, 3, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] = V [3, 1, 8, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] :=
    (in_context torus13838 [] [6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused17999 : V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] = V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4] := by
  have h0 : V [0, 7, 2, 3, 4, 6, 12, 8, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] = V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] :=
    overlap torus10968 focused17995 [5, 0, 8, 1, 6] [8, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] (by decide)
  have hl : V [0, 7, 2, 3, 4, 6, 12, 8, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1] = V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4] :=
    ((in_context torus84 [0, 7, 2, 3, 4, 6] [0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus3885 [0] [12, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus0 [] [6, 1, 6, 7, 1, 12, 0, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus93 [6, 1, 6, 7, 1] [4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus1 [6, 1, 6, 7] [12, 4, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus60 [6, 1, 6, 7] [3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus7 [6, 1, 6] [12, 3, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus54 [6, 1, 6] [0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus6 [6, 1] [12, 0, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus93 [6, 1] [6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus1 [6] [12, 6, 2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus72 [6] [2, 8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus48 [6, 2] [8, 4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus84 [6, 2, 5] [4, 5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus60 [6, 2, 5, 4] [5, 1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus66 [6, 2, 5, 4, 7] [1, 2, 4, 6, 5, 7, 1]).trans ((in_context torus94 [6, 2, 5, 4, 7, 8] [2, 4, 6, 5, 7, 1]).trans ((in_context torus48 [6, 2, 5, 4, 7, 8, 1] [4, 6, 5, 7, 1]).trans ((in_context torus60 [6, 2, 5, 4, 7, 8, 1, 5] [6, 5, 7, 1]).trans ((in_context torus72 [6, 2, 5, 4, 7, 8, 1, 5, 7] [5, 7, 1]).trans ((in_context torus66 [6, 2, 5, 4, 7, 8, 1, 5, 7, 2] [7, 1]).trans ((in_context torus78 [6, 2, 5, 4, 7, 8, 1, 5, 7, 2, 8] [1]).trans ((in_context torus94 [6, 2, 5, 4, 7, 8, 1, 5, 7, 2, 8, 3] []).trans (in_context torus4397 [6, 2, 5, 4, 7, 8, 1, 5] []))))))))))))))))))))))))
  have hr : V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] = V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18008 : V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] = V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] := by
  have h0 : V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] = V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] :=
    overlap focused17999 torus5 [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] [5] (by decide)
  have hl : V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] = V [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] :=
    rfl
  have hr : V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] = V [5, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18013 : V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] := by
  have h0 : V [6, 0, 8, 1, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] = V [3, 5, 1, 2, 0, 4, 7, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] :=
    overlap torus2341 focused18008 [3, 5, 1, 2, 0, 4, 7] [0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] (by decide)
  have hl : V [6, 0, 8, 1, 0, 8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7] :=
    ((in_context torus1 [6, 0, 8] [8, 1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7]).trans ((in_context torus8 [6, 0] [1, 6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7]).trans ((in_context torus0 [6] [6, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7]).trans (in_context torus6 [] [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7]))))
  have hr : V [3, 5, 1, 2, 0, 4, 7, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] = V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5] :=
    ((in_context torus4035 [3] [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5]).trans (in_context torus3 [] [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18014 : V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] := by
  have h0 : V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 0, 6, 7] = V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 1, 5, 4, 6] :=
    overlap focused18013 torus1566 [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4] [0, 6, 7] (by decide)
  have hl : V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 6, 7, 0, 6, 7] = V [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] :=
    ((in_context torus1482 [1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4] [6, 7]).trans ((in_context torus14193 [1, 1, 8, 1, 6, 5, 0, 8] [6, 6, 7]).trans ((in_context torus72 [1, 1, 8, 1, 6, 5, 0, 8, 1, 1, 4, 3, 6, 1] [6, 7]).trans ((in_context torus72 [1, 1, 8, 1, 6, 5, 0, 8, 1, 1, 4, 3, 6, 1, 2] [7]).trans ((in_context torus2 [1, 1, 8, 1, 6, 5, 0, 8, 1, 1, 4, 3, 6, 1] [12, 7]).trans ((in_context torus78 [1, 1, 8, 1, 6, 5, 0, 8, 1, 1, 4, 3, 6, 1] []).trans ((in_context torus12532 [1, 1, 8, 1, 6, 5, 0, 8, 1] []).trans (in_context torus1 [1, 1, 8, 1, 6, 5, 0, 8] [3, 4, 8, 0, 4, 1]))))))))
  have hr : V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 4, 1, 5, 4, 6] = V [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6] :=
    (in_context torus1508 [6, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1] [6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18018 : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] = V [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 1, 7] := by
  have h0 : V [1, 1, 3, 2, 5, 1, 12, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] :=
    overlap torus14163 focused18014 [2, 3, 7, 0, 3, 1] [0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6] (by decide)
  have hl : V [1, 1, 3, 2, 5, 1, 12, 0, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6] = V [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 1, 7] :=
    ((in_context torus93 [1, 1, 3, 2, 5, 1] [8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus1 [1, 1, 3, 2, 5] [12, 8, 1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus84 [1, 1, 3, 2, 5] [1, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus94 [1, 1, 3, 2, 5, 4] [5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus1452 [1, 1, 3, 2] [12, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus3464 [1] [12, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus1 [] [4, 5, 1, 3, 2, 12, 5, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus66 [4, 5, 1, 3, 2] [6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus1434 [4, 5, 1] [12, 6, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus72 [4, 5, 1, 2, 1, 2] [2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus2 [4, 5, 1, 2, 1] [12, 2, 5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus48 [4, 5, 1, 2, 1] [5, 4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus66 [4, 5, 1, 2, 1, 5] [4, 7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus60 [4, 5, 1, 2, 1, 5, 8] [7, 8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus78 [4, 5, 1, 2, 1, 5, 8, 7] [8, 1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus84 [4, 5, 1, 2, 1, 5, 8, 7, 3] [1, 5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus94 [4, 5, 1, 2, 1, 5, 8, 7, 3, 4] [5, 1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus66 [4, 5, 1, 2, 1, 5, 8, 7, 3, 4, 1] [1, 5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus94 [4, 5, 1, 2, 1, 5, 8, 7, 3, 4, 1, 8] [5, 0, 8, 1, 5, 0, 6]).trans ((in_context torus66 [4, 5, 1, 2, 1, 5, 8, 7, 3, 4, 1, 8, 1] [0, 8, 1, 5, 0, 6]).trans ((in_context torus1489 [4, 5, 1, 2, 1, 5, 8, 7, 3, 4, 1] [12, 0, 8, 1, 5, 0, 6]).trans ((in_context torus14252 [4, 5, 1, 2, 1, 5] [7, 12, 0, 8, 1, 5, 0, 6]).trans ((in_context torus93 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 0, 3, 4, 7] [8, 1, 5, 0, 6]).trans ((in_context torus84 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 0, 3, 4, 7, 0] [1, 5, 0, 6]).trans ((in_context torus94 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 0, 3, 4, 7, 0, 4] [5, 0, 6]).trans ((in_context torus8857 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0] [5, 0, 6]).trans ((in_context torus5 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 6, 7] [0, 6]).trans ((in_context torus1482 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8] [6]).trans ((in_context torus1585 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1] [6]).trans ((in_context torus1 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4] [8, 2, 7, 6]).trans (in_context torus1621 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4] [])))))))))))))))))))))))))))))))
  have hr : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18019 : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4, 3, 0, 6, 1, 2] = V [4, 5, 1, 1, 6, 0, 8, 3] := by
  have h0 : V [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 1, 7, 7, 0, 0, 5, 1] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 1, 8, 0, 0, 6, 1, 2] :=
    overlap focused18018 torus11502 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0] [7, 0, 0, 5, 1] (by decide)
  have hl : V [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 1, 7, 7, 0, 0, 5, 1] = V [4, 5, 1, 1, 6, 0, 8, 3] :=
    ((in_context torus7 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8, 1] [0, 0, 5, 1]).trans ((in_context torus1 [4, 5, 1, 2, 1, 5, 0, 7, 2, 0, 4, 1, 8] [0, 5, 1]).trans ((in_context torus4636 [4, 5, 1, 2, 1, 5, 0] [5, 1]).trans ((in_context torus3706 [4, 5, 1] [0, 2, 11, 5, 1]).trans ((in_context torus93 [4, 5, 1, 1, 6, 0, 8, 3] [2, 11, 5, 1]).trans ((in_context torus48 [4, 5, 1, 1, 6, 0, 8, 3, 0] [11, 5, 1]).trans ((in_context torus29 [4, 5, 1, 1, 6, 0, 8, 3, 0, 5] [5, 1]).trans ((in_context torus5 [4, 5, 1, 1, 6, 0, 8, 3, 0] [1]).trans (in_context torus0 [4, 5, 1, 1, 6, 0, 8, 3] [])))))))))
  have hr : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8, 0, 1, 8, 0, 0, 6, 1, 2] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4, 3, 0, 6, 1, 2] :=
    ((in_context torus0 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4, 8] [8, 0, 0, 6, 1, 2]).trans ((in_context torus8 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 3, 4] [0, 0, 6, 1, 2]).trans (in_context torus1455 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8] [0, 6, 1, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18020 : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6, 5] = V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0] := by
  have h0 : V [4, 5, 1, 1, 6, 0, 8, 3, 3, 1, 8, 7, 2, 8, 3, 2] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4, 3, 0, 6, 1, 1, 8, 0] :=
    overlap focused18019 torus2605 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4, 3, 0, 6, 1] [3, 1, 8, 7, 2, 8, 3, 2] (by decide)
  have hl : V [4, 5, 1, 1, 6, 0, 8, 3, 3, 1, 8, 7, 2, 8, 3, 2] = V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0] :=
    ((in_context torus3 [4, 5, 1, 1, 6, 0, 8] [1, 8, 7, 2, 8, 3, 2]).trans ((in_context torus1489 [4, 5, 1, 1, 6, 0] [7, 2, 8, 3, 2]).trans ((in_context torus7 [4, 5, 1, 1, 6, 0, 2, 8] [2, 8, 3, 2]).trans ((in_context torus1428 [4, 5, 1, 1, 6, 0] [8, 3, 2]).trans (in_context torus4611 [4, 5, 1, 1, 6] [])))))
  have hr : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4, 3, 0, 6, 1, 1, 8, 0] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6, 5] :=
    ((in_context torus12305 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6, 5, 0, 8, 1, 4] []).trans ((in_context torus2449 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 6] [1, 2, 0, 5]).trans ((in_context torus1469 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1] [8, 12, 1, 2, 0, 5]).trans ((in_context torus1473 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1] [8, 12, 1, 2, 0, 5]).trans ((in_context torus94 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 1, 6, 5, 8] [2, 0, 5]).trans ((in_context torus48 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1, 1, 6, 5, 8, 1] [0, 5]).trans ((in_context torus13041 [2, 3, 7, 0, 3, 1, 1, 1, 8, 1] [0, 5]).trans ((in_context torus1 [2, 3, 7, 0, 3, 1, 1, 1, 8] [5, 6, 3, 0, 6, 1, 0, 5]).trans (in_context torus1 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6] [5])))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18021 : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0, 5, 6] = V [4, 5, 1, 1, 6, 8, 7, 2, 8] := by
  have h0 : V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 3, 4, 3, 2, 3] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6, 6, 5, 4, 5] :=
    overlap focused18020 torus113 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6] [3, 4, 3, 2, 3] (by decide)
  have hl : V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 3, 4, 3, 2, 3] = V [4, 5, 1, 1, 6, 8, 7, 2, 8] :=
    ((in_context torus12838 [4, 5, 1, 1, 6] [3, 2, 3]).trans ((in_context torus3 [4, 5, 1, 1, 6, 0, 0, 2, 3, 8, 0] [2, 3]).trans ((in_context torus4612 [4, 5, 1, 1, 6] [3]).trans (in_context torus3 [4, 5, 1, 1, 6, 8, 7, 2, 8] []))))
  have hr : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 6, 6, 5, 4, 5] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0, 5, 6] :=
    ((in_context torus6 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] [5, 4, 5]).trans (in_context torus1457 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18027 : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] = V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] := by
  have h0 : V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0, 5, 5, 1] :=
    overlap focused18021 torus1497 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0, 5] [0, 5, 6] (by decide)
  have hl : V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] :=
    rfl
  have hr : V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0, 5, 5, 1] = V [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] :=
    ((in_context torus5 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0, 0] [1]).trans (in_context torus0 [2, 3, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18029 : V [3, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] := by
  have h0 : V [2, 3, 2, 8, 2, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] = V [3, 4, 3, 4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] :=
    overlap torus146 focused18027 [3, 4, 3] [7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] (by decide)
  have hl : V [2, 3, 2, 8, 2, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] = V [1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] :=
    ((in_context torus1436 [] [8, 2, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0]).trans ((in_context torus8 [1, 2] [2, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0]).trans (in_context torus2 [1] [7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0])))
  have hr : V [3, 4, 3, 4, 5, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [3, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] :=
    ((in_context torus99 [] [1, 1, 6, 8, 7, 2, 8, 0, 5, 6]).trans (in_context torus1441 [] [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18030 : V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] = V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] := by
  have h0 : V [2, 3, 2, 8, 2, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [3, 4, 3, 2, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] :=
    overlap torus146 focused18029 [3, 4, 3, 2] [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] (by decide)
  have hl : V [2, 3, 2, 8, 2, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] = V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6] :=
    ((in_context torus1436 [] [8, 2, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6]).trans ((in_context torus8 [1, 2] [2, 0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6]).trans ((in_context torus2 [1] [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6]).trans (in_context torus1 [] [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6]))))
  have hr : V [3, 4, 3, 2, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] = V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0] :=
    ((in_context torus1442 [] [2, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0]).trans ((in_context torus1446 [] [2, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0]).trans (in_context torus2 [1, 3] [1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18031 : V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] := by
  have h0 : V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] :=
    overlap focused18030 torus0 [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] [1] (by decide)
  have hl : V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] :=
    rfl
  have hr : V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [1, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18032 : V [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] := by
  have h0 : V [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] :=
    overlap torus0 focused18031 [0] [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] (by decide)
  have hl : V [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] :=
    rfl
  have hr : V [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [0, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18033 : V [5, 0, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [8, 7, 3, 2, 5, 6, 1] := by
  have h0 : V [0, 2, 1, 6, 0, 0, 4, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [5, 0, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] :=
    overlap torus13428 focused18032 [5, 0, 0, 3, 1, 7] [4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] (by decide)
  have hl : V [0, 2, 1, 6, 0, 0, 4, 4, 1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1] = V [8, 7, 3, 2, 5, 6, 1] :=
    ((in_context torus4 [0, 2, 1, 6, 0, 0] [1, 1, 6, 8, 7, 2, 8, 0, 5, 6, 1]).trans ((in_context torus0 [0, 2, 1, 6, 0] [1, 6, 8, 7, 2, 8, 0, 5, 6, 1]).trans ((in_context torus0 [0, 2, 1, 6] [6, 8, 7, 2, 8, 0, 5, 6, 1]).trans ((in_context torus6 [0, 2, 1] [8, 7, 2, 8, 0, 5, 6, 1]).trans ((in_context torus1590 [0] [2, 8, 0, 5, 6, 1]).trans ((in_context torus1487 [0, 0, 2, 3] [0, 5, 6, 1]).trans ((in_context torus1490 [0, 0, 2, 3] [0, 5, 6, 1]).trans ((in_context torus4609 [] [0, 5, 6, 1]).trans (in_context torus1437 [8, 7] [5, 6, 1])))))))))
  have hr : V [5, 0, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [5, 0, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18034 : V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [4, 0, 6, 0, 3, 2, 5, 6, 1] := by
  have h0 : V [0, 7, 5, 7, 6, 8, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [4, 6, 5, 7, 8, 7, 3, 2, 5, 6, 1] :=
    overlap torus4044 focused18033 [4, 6, 5, 7] [0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] (by decide)
  have hl : V [0, 7, 5, 7, 6, 8, 0, 3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] :=
    ((in_context torus1588 [0, 7, 5] [3, 1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus4461 [0, 7] [1, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus92 [0, 7, 0, 8, 1, 4, 0] [7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus0 [0, 7, 0, 8, 1, 4] [11, 7, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus77 [0, 7, 0, 8, 1, 4] [3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus4 [0, 7, 0, 8, 1] [11, 3, 1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus53 [0, 7, 0, 8, 1] [1, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus92 [0, 7, 0, 8, 1, 7] [7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus1599 [0, 7, 0] [11, 7, 0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus77 [0, 7, 0, 2, 8, 6, 7] [0, 3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus91 [0, 7, 0, 2, 8, 6, 7, 4] [3, 1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus53 [0, 7, 0, 2, 8, 6, 7, 4, 0] [1, 1, 1, 8, 5, 6, 3]).trans ((in_context torus92 [0, 7, 0, 2, 8, 6, 7, 4, 0, 7] [1, 1, 8, 5, 6, 3]).trans ((in_context torus14071 [0, 7, 0, 2, 8] [1, 1, 8, 5, 6, 3]).trans ((in_context torus1488 [0, 7, 0] [1, 7, 6, 2, 1, 6, 1, 1, 8, 5, 6, 3]).trans ((in_context torus3259 [0] [6, 2, 1, 6, 1, 1, 8, 5, 6, 3]).trans ((in_context torus6 [0, 6, 0, 8, 2] [2, 1, 6, 1, 1, 8, 5, 6, 3]).trans (in_context torus2 [0, 6, 0, 8] [1, 6, 1, 1, 8, 5, 6, 3]))))))))))))))))))
  have hr : V [4, 6, 5, 7, 8, 7, 3, 2, 5, 6, 1] = V [4, 0, 6, 0, 3, 2, 5, 6, 1] :=
    ((in_context torus1607 [4] [7, 3, 2, 5, 6, 1]).trans (in_context torus7 [4, 0, 6, 0] [3, 2, 5, 6, 1]))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18035 : V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6] = V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3] := by
  have h0 : V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6] :=
    overlap focused18034 torus3 [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6] [3] (by decide)
  have hl : V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3] = V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3] :=
    rfl
  have hr : V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18037 : V [6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [1, 4, 0, 6, 0, 3, 2, 5, 6, 1] := by
  have h0 : V [6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [1, 4, 0, 6, 0, 3, 2, 5, 6, 1] :=
    overlap torus1 focused18034 [1] [6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] (by decide)
  have hl : V [6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [6, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] :=
    rfl
  have hr : V [1, 4, 0, 6, 0, 3, 2, 5, 6, 1] = V [1, 4, 0, 6, 0, 3, 2, 5, 6, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18038 : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6, 1] = V [6, 1, 1, 8, 5, 6, 3] := by
  have h0 : V [0, 8, 1, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [5, 7, 4, 1, 2, 0, 5, 3, 1, 4, 0, 6, 0, 3, 2, 5, 6, 1] :=
    overlap torus2194 focused18037 [5, 7, 4, 1, 2, 0, 5, 3] [0, 8, 1, 6, 1, 1, 8, 5, 6, 3] (by decide)
  have hl : V [0, 8, 1, 0, 8, 1, 6, 1, 1, 8, 5, 6, 3] = V [6, 1, 1, 8, 5, 6, 3] :=
    ((in_context torus1 [0, 8] [8, 1, 6, 1, 1, 8, 5, 6, 3]).trans ((in_context torus8 [0] [1, 6, 1, 1, 8, 5, 6, 3]).trans (in_context torus0 [] [6, 1, 1, 8, 5, 6, 3])))
  have hr : V [5, 7, 4, 1, 2, 0, 5, 3, 1, 4, 0, 6, 0, 3, 2, 5, 6, 1] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6, 1] :=
    (in_context torus2337 [] [1, 4, 0, 6, 0, 3, 2, 5, 6, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18039 : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6] = V [6, 1, 1, 8, 5, 6, 3, 0] := by
  have h0 : V [6, 1, 1, 8, 5, 6, 3, 0] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6] :=
    overlap focused18038 torus1 [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6] [0] (by decide)
  have hl : V [6, 1, 1, 8, 5, 6, 3, 0] = V [6, 1, 1, 8, 5, 6, 3, 0] :=
    rfl
  have hr : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18041 : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5] = V [6, 1, 1, 8, 5, 6, 3, 0, 6] := by
  have h0 : V [6, 1, 1, 8, 5, 6, 3, 0, 6] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5] :=
    overlap focused18039 torus6 [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5] [6] (by decide)
  have hl : V [6, 1, 1, 8, 5, 6, 3, 0, 6] = V [6, 1, 1, 8, 5, 6, 3, 0, 6] :=
    rfl
  have hr : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18043 : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2] = V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5] := by
  have h0 : V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2] :=
    overlap focused18041 torus5 [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2] [5] (by decide)
  have hl : V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5] = V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5] :=
    rfl
  have hr : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18047 : V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5] := by
  have h0 : V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5] :=
    overlap focused18035 torus6 [0, 6, 0, 8, 1, 6, 1, 1, 8, 5] [6] (by decide)
  have hl : V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] = V [4, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] :=
    rfl
  have hr : V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5] = V [0, 6, 0, 8, 1, 6, 1, 1, 8, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18048 : V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5] = V [6, 0, 3, 2, 5, 6, 1, 3, 6] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] = V [4, 5, 4, 3, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5] :=
    overlap torus103 focused18047 [4, 5, 4, 3] [0, 6, 0, 3, 2, 5, 6, 1, 3, 6] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6] = V [6, 0, 3, 2, 5, 6, 1, 3, 6] :=
    ((in_context torus146 [] [0, 6, 0, 3, 2, 5, 6, 1, 3, 6]).trans ((in_context torus1436 [] [8, 2, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6]).trans ((in_context torus8 [1, 2] [2, 0, 6, 0, 3, 2, 5, 6, 1, 3, 6]).trans ((in_context torus2 [1] [0, 6, 0, 3, 2, 5, 6, 1, 3, 6]).trans (in_context torus1 [] [6, 0, 3, 2, 5, 6, 1, 3, 6])))))
  have hr : V [4, 5, 4, 3, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5] :=
    ((in_context torus1451 [] [3, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5]).trans ((in_context torus1455 [] [3, 0, 6, 0, 8, 1, 6, 1, 1, 8, 5]).trans (in_context torus3 [1, 4] [0, 6, 0, 8, 1, 6, 1, 1, 8, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18050 : V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8] = V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5] := by
  have h0 : V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8] :=
    overlap focused18048 torus5 [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8] [5] (by decide)
  have hl : V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5] = V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5] :=
    rfl
  have hr : V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18054 : V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3] := by
  have h0 : V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3] :=
    overlap focused18043 torus2 [0, 8, 1, 6, 1, 4, 0, 6, 0, 3] [2] (by decide)
  have hl : V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] = V [6, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] :=
    rfl
  have hr : V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3] = V [0, 8, 1, 6, 1, 4, 0, 6, 0, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18055 : V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 0, 3] = V [1, 8, 5, 6, 3, 0, 6, 5, 2] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] = V [6, 5, 6, 7, 0, 8, 1, 6, 1, 4, 0, 6, 0, 3] :=
    overlap torus117 focused18054 [6, 5, 6, 7] [1, 1, 8, 5, 6, 3, 0, 6, 5, 2] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2] = V [1, 8, 5, 6, 3, 0, 6, 5, 2] :=
    ((in_context torus143 [] [1, 1, 8, 5, 6, 3, 0, 6, 5, 2]).trans ((in_context torus1428 [] [3, 2, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2]).trans ((in_context torus3 [0, 2] [2, 1, 1, 8, 5, 6, 3, 0, 6, 5, 2]).trans ((in_context torus2 [0] [1, 1, 8, 5, 6, 3, 0, 6, 5, 2]).trans (in_context torus0 [] [1, 8, 5, 6, 3, 0, 6, 5, 2])))))
  have hr : V [6, 5, 6, 7, 0, 8, 1, 6, 1, 4, 0, 6, 0, 3] = V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 0, 3] :=
    ((in_context torus1466 [] [7, 0, 8, 1, 6, 1, 4, 0, 6, 0, 3]).trans (in_context torus7 [0, 6] [0, 8, 1, 6, 1, 4, 0, 6, 0, 3]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18059 : V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1] := by
  have h0 : V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1] :=
    overlap focused18050 torus8 [1, 4, 0, 6, 0, 8, 1, 6, 1, 1] [8] (by decide)
  have hl : V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] = V [6, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] :=
    rfl
  have hr : V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1] = V [1, 4, 0, 6, 0, 8, 1, 6, 1, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18060 : V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1] = V [3, 2, 5, 6, 1, 3, 6, 5, 8] := by
  have h0 : V [3, 4, 3, 2, 3, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] = V [6, 7, 6, 5, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1] :=
    overlap torus120 focused18059 [6, 7, 6, 5] [0, 3, 2, 5, 6, 1, 3, 6, 5, 8] (by decide)
  have hl : V [3, 4, 3, 2, 3, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8] = V [3, 2, 5, 6, 1, 3, 6, 5, 8] :=
    ((in_context torus146 [] [0, 3, 2, 5, 6, 1, 3, 6, 5, 8]).trans ((in_context torus1436 [] [8, 2, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8]).trans ((in_context torus8 [1, 2] [2, 0, 3, 2, 5, 6, 1, 3, 6, 5, 8]).trans ((in_context torus2 [1] [0, 3, 2, 5, 6, 1, 3, 6, 5, 8]).trans (in_context torus1 [] [3, 2, 5, 6, 1, 3, 6, 5, 8])))))
  have hr : V [6, 7, 6, 5, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1] = V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1] :=
    ((in_context torus1469 [] [5, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1]).trans ((in_context torus1473 [] [5, 1, 4, 0, 6, 0, 8, 1, 6, 1, 1]).trans (in_context torus5 [1, 6] [1, 4, 0, 6, 0, 8, 1, 6, 1, 1])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18062 : V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0] := by
  have h0 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0] = V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] :=
    overlap focused18060 torus1 [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] [0] (by decide)
  have hl : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0] :=
    rfl
  have hr : V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] = V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18063 : V [1, 8, 5, 6, 3, 0, 6, 5, 2, 3, 1] = V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6] := by
  have h0 : V [1, 8, 5, 6, 3, 0, 6, 5, 2, 4, 3, 2, 3] = V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 0, 2, 3, 2, 8, 2] :=
    overlap focused18055 torus146 [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 0] [4, 3, 2, 3] (by decide)
  have hl : V [1, 8, 5, 6, 3, 0, 6, 5, 2, 4, 3, 2, 3] = V [1, 8, 5, 6, 3, 0, 6, 5, 2, 3, 1] :=
    ((in_context torus1444 [1, 8, 5, 6, 3, 0, 6, 5, 2] [3]).trans (in_context torus3 [1, 8, 5, 6, 3, 0, 6, 5, 2, 3, 1] []))
  have hr : V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 0, 2, 3, 2, 8, 2] = V [0, 6, 0, 8, 1, 6, 1, 4, 0, 6] :=
    ((in_context torus1433 [0, 6, 0, 8, 1, 6, 1, 4, 0, 6] [8, 2]).trans ((in_context torus8 [0, 6, 0, 8, 1, 6, 1, 4, 0, 6, 2] [2]).trans (in_context torus2 [0, 6, 0, 8, 1, 6, 1, 4, 0, 6] [])))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18064 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0, 6] = V [1] := by
  have h0 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 8, 5, 6, 3, 0, 6, 5, 2, 3, 1] = V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1, 0, 6, 0, 8, 1, 6, 1, 4, 0, 6] :=
    overlap focused18060 focused18063 [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1] [8, 5, 6, 3, 0, 6, 5, 2, 3, 1] (by decide)
  have hl : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 8, 5, 6, 3, 0, 6, 5, 2, 3, 1] = V [1] :=
    ((in_context torus8 [3, 2, 5, 6, 1, 3, 6, 5] [5, 6, 3, 0, 6, 5, 2, 3, 1]).trans ((in_context torus5 [3, 2, 5, 6, 1, 3, 6] [6, 3, 0, 6, 5, 2, 3, 1]).trans ((in_context torus6 [3, 2, 5, 6, 1, 3] [3, 0, 6, 5, 2, 3, 1]).trans ((in_context torus3 [3, 2, 5, 6, 1] [0, 6, 5, 2, 3, 1]).trans ((in_context torus1 [3, 2, 5, 6] [6, 5, 2, 3, 1]).trans ((in_context torus6 [3, 2, 5] [5, 2, 3, 1]).trans ((in_context torus5 [3, 2] [2, 3, 1]).trans ((in_context torus2 [3] [3, 1]).trans (in_context torus3 [] [1])))))))))
  have hr : V [1, 6, 1, 4, 0, 6, 0, 8, 1, 6, 1, 0, 6, 0, 8, 1, 6, 1, 4, 0, 6] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0, 6] :=
    (in_context focused18062 [] [0, 6, 0, 8, 1, 6, 1, 4, 0, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18065 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0] = V [1, 6] := by
  have h0 : V [1, 6] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0] :=
    overlap focused18064 torus6 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0] [6] (by decide)
  have hl : V [1, 6] = V [1, 6] :=
    rfl
  have hr : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18068 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6] = V [1, 6, 1, 4, 0] := by
  have h0 : V [1, 6, 5, 6, 1, 4, 3, 5, 4, 6, 5] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 4, 0] :=
    overlap focused18065 torus2163 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4] [5, 6, 1, 4, 3, 5, 4, 6, 5] (by decide)
  have hl : V [1, 6, 5, 6, 1, 4, 3, 5, 4, 6, 5] = V [1, 6, 1, 4, 0] :=
    ((in_context torus1466 [1] [1, 4, 3, 5, 4, 6, 5]).trans ((in_context torus1 [] [6, 7, 1, 4, 3, 5, 4, 6, 5]).trans ((in_context torus11179 [] [6, 5]).trans ((in_context torus1521 [1, 6, 1] [5]).trans (in_context torus5 [1, 6, 1, 4, 0] [])))))
  have hr : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1, 4, 4, 0] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6] :=
    ((in_context torus4 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6, 1] [0]).trans (in_context torus1 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 6] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18070 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8] = V [1, 6, 1, 4, 0, 6, 0] := by
  have h0 : V [1, 6, 1, 4, 0, 5, 6, 7, 6] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 3, 2, 3, 4, 3] :=
    overlap focused18068 torus117 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1] [5, 6, 7, 6] (by decide)
  have hl : V [1, 6, 1, 4, 0, 5, 6, 7, 6] = V [1, 6, 1, 4, 0, 6, 0] :=
    ((in_context torus1561 [1, 6, 1] [7, 6]).trans (in_context torus1714 [1, 6, 1] []))
  have hr : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8, 1, 3, 2, 3, 4, 3] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8] :=
    ((in_context torus1557 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0] [3, 4, 3]).trans ((in_context torus1512 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0] [3]).trans (in_context torus3 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 8] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18073 : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [1, 6, 1, 4, 0, 6, 0, 8, 1] := by
  have h0 : V [1, 6, 1, 4, 0, 6, 0, 2, 8, 7, 8] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 3, 4, 3, 2, 3] :=
    overlap focused18070 torus138 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0] [2, 8, 7, 8] (by decide)
  have hl : V [1, 6, 1, 4, 0, 6, 0, 2, 8, 7, 8] = V [1, 6, 1, 4, 0, 6, 0, 8, 1] :=
    ((in_context torus1484 [1, 6, 1, 4, 0, 6, 0, 2] []).trans (in_context torus1491 [1, 6, 1, 4, 0, 6, 0] []))
  have hr : V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0, 3, 4, 3, 2, 3] = V [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] :=
    ((in_context torus146 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 0] []).trans ((in_context torus1433 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] [8, 2]).trans ((in_context torus8 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6, 2] [2]).trans (in_context torus2 [3, 2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18082 : V [2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [3, 1, 6, 1, 4, 0, 6, 0, 8, 1] := by
  have h0 : V [2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [3, 1, 6, 1, 4, 0, 6, 0, 8, 1] :=
    overlap torus3 focused18073 [3] [2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] (by decide)
  have hl : V [2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [2, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] :=
    rfl
  have hr : V [3, 1, 6, 1, 4, 0, 6, 0, 8, 1] = V [3, 1, 6, 1, 4, 0, 6, 0, 8, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18083 : V [2, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] = V [5, 6, 1, 3, 6, 5, 8, 0, 0, 6] := by
  have h0 : V [5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [2, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] :=
    overlap torus2 focused18082 [2] [5, 6, 1, 3, 6, 5, 8, 0, 0, 6] (by decide)
  have hl : V [5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [5, 6, 1, 3, 6, 5, 8, 0, 0, 6] :=
    rfl
  have hr : V [2, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] = V [2, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18131 : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3, 11] = V [1, 8, 0, 3, 0, 5, 1, 11] := by
  have h0 : V [3, 0, 7, 11, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] = V [0, 7, 1, 4, 0, 6, 0, 8, 0, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] :=
    overlap torus5317 focused18083 [0, 7, 1, 4, 0, 6, 0, 8, 0] [3, 1, 6, 1, 4, 0, 6, 0, 8, 1] (by decide)
  have hl : V [3, 0, 7, 11, 3, 1, 6, 1, 4, 0, 6, 0, 8, 1] = V [1, 8, 0, 3, 0, 5, 1, 11] :=
    ((in_context torus53 [3, 0, 7] [1, 6, 1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus7 [3, 0] [11, 1, 6, 1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus92 [3, 0] [6, 1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus0 [3] [11, 6, 1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus71 [3] [1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus3 [] [11, 1, 4, 0, 6, 0, 8, 1]).trans ((in_context torus92 [] [4, 0, 6, 0, 8, 1]).trans ((in_context torus59 [1] [0, 6, 0, 8, 1]).trans ((in_context torus91 [1, 8] [6, 0, 8, 1]).trans ((in_context torus71 [1, 8, 0] [0, 8, 1]).trans ((in_context torus91 [1, 8, 0, 3] [8, 1]).trans ((in_context torus83 [1, 8, 0, 3, 0] [1]).trans (in_context torus92 [1, 8, 0, 3, 0, 5] [])))))))))))))
  have hr : V [0, 7, 1, 4, 0, 6, 0, 8, 0, 5, 6, 1, 3, 6, 5, 8, 0, 0, 6] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3, 11] :=
    ((in_context torus5795 [] [5, 6, 1, 3, 6, 5, 8, 0, 0, 6]).trans ((in_context torus65 [3, 0, 7, 6] [6, 1, 3, 6, 5, 8, 0, 0, 6]).trans ((in_context torus71 [3, 0, 7, 6, 2] [1, 3, 6, 5, 8, 0, 0, 6]).trans ((in_context torus92 [3, 0, 7, 6, 2, 3] [3, 6, 5, 8, 0, 0, 6]).trans ((in_context torus53 [3, 0, 7, 6, 2, 3, 1] [6, 5, 8, 0, 0, 6]).trans ((in_context torus71 [3, 0, 7, 6, 2, 3, 1, 7] [5, 8, 0, 0, 6]).trans ((in_context torus65 [3, 0, 7, 6, 2, 3, 1, 7, 3] [8, 0, 0, 6]).trans ((in_context torus83 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] [0, 0, 6]).trans ((in_context torus91 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] [0, 6]).trans ((in_context torus91 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0] [6]).trans (in_context torus71 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18132 : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3] = V [1, 8, 0, 3, 0, 5, 1] := by
  have h0 : V [1, 8, 0, 3, 0, 5, 1, 11, 12] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3] :=
    overlap focused18131 torus24 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3] [12] (by decide)
  have hl : V [1, 8, 0, 3, 0, 5, 1, 11, 12] = V [1, 8, 0, 3, 0, 5, 1] :=
    (in_context torus24 [1, 8, 0, 3, 0, 5, 1] [])
  have hr : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18134 : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0] = V [1, 8, 0, 3, 0, 5, 1, 3, 1] := by
  have h0 : V [1, 8, 0, 3, 0, 5, 1, 4, 3, 2, 3] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 2, 3, 2, 8, 2] :=
    overlap focused18132 torus146 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0] [4, 3, 2, 3] (by decide)
  have hl : V [1, 8, 0, 3, 0, 5, 1, 4, 3, 2, 3] = V [1, 8, 0, 3, 0, 5, 1, 3, 1] :=
    ((in_context torus1546 [1, 8, 0, 3, 0] [2, 3]).trans ((in_context torus2015 [1, 8, 0, 3, 0, 0] []).trans (in_context torus0 [1, 8, 0, 3, 0] [5, 1, 3, 1])))
  have hr : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 0, 2, 3, 2, 8, 2] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0] :=
    ((in_context torus1433 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0] [8, 2]).trans ((in_context torus8 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0, 2] [2]).trans (in_context torus2 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5, 0] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18137 : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] = V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1] := by
  have h0 : V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] :=
    overlap focused18134 torus0 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] [1] (by decide)
  have hl : V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1] = V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1] :=
    rfl
  have hr : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18145 : V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] := by
  have h0 : V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] :=
    overlap focused18137 torus5 [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] [5] (by decide)
  have hl : V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] = V [1, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] :=
    rfl
  have hr : V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] = V [3, 0, 7, 6, 2, 3, 1, 7, 3, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18407 : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6, 11] = V [7, 0, 2, 1, 7, 1, 1, 2, 11] := by
  have h0 : V [1, 5, 11, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] = V [7, 2, 8, 3, 1, 7, 0, 4, 3, 0, 7, 6, 2, 3, 1, 7, 3, 2] :=
    overlap torus2971 focused18145 [7, 2, 8, 3, 1, 7, 0, 4] [8, 0, 3, 0, 5, 1, 3, 1, 1, 5] (by decide)
  have hl : V [1, 5, 11, 8, 0, 3, 0, 5, 1, 3, 1, 1, 5] = V [7, 0, 2, 1, 7, 1, 1, 2, 11] :=
    ((in_context torus83 [1, 5] [0, 3, 0, 5, 1, 3, 1, 1, 5]).trans ((in_context torus5 [1] [11, 0, 3, 0, 5, 1, 3, 1, 1, 5]).trans ((in_context torus91 [1] [3, 0, 5, 1, 3, 1, 1, 5]).trans ((in_context torus1 [] [11, 3, 0, 5, 1, 3, 1, 1, 5]).trans ((in_context torus53 [] [0, 5, 1, 3, 1, 1, 5]).trans ((in_context torus91 [7] [5, 1, 3, 1, 1, 5]).trans ((in_context torus65 [7, 0] [1, 3, 1, 1, 5]).trans ((in_context torus92 [7, 0, 2] [3, 1, 1, 5]).trans ((in_context torus53 [7, 0, 2, 1] [1, 1, 5]).trans ((in_context torus92 [7, 0, 2, 1, 7] [1, 5]).trans ((in_context torus92 [7, 0, 2, 1, 7, 1] [5]).trans (in_context torus65 [7, 0, 2, 1, 7, 1, 1] []))))))))))))
  have hr : V [7, 2, 8, 3, 1, 7, 0, 4, 3, 0, 7, 6, 2, 3, 1, 7, 3, 2] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6, 11] :=
    ((in_context torus2972 [] [3, 0, 7, 6, 2, 3, 1, 7, 3, 2]).trans ((in_context torus53 [1, 5, 0] [0, 7, 6, 2, 3, 1, 7, 3, 2]).trans ((in_context torus91 [1, 5, 0, 7] [7, 6, 2, 3, 1, 7, 3, 2]).trans ((in_context torus77 [1, 5, 0, 7, 0] [6, 2, 3, 1, 7, 3, 2]).trans ((in_context torus71 [1, 5, 0, 7, 0, 4] [2, 3, 1, 7, 3, 2]).trans ((in_context torus47 [1, 5, 0, 7, 0, 4, 3] [3, 1, 7, 3, 2]).trans ((in_context torus53 [1, 5, 0, 7, 0, 4, 3, 6] [1, 7, 3, 2]).trans ((in_context torus92 [1, 5, 0, 7, 0, 4, 3, 6, 7] [7, 3, 2]).trans ((in_context torus77 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1] [3, 2]).trans ((in_context torus53 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] [2]).trans (in_context torus47 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18408 : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6] = V [7, 0, 2, 1, 7, 1, 1, 2] := by
  have h0 : V [7, 0, 2, 1, 7, 1, 1, 2, 11, 12] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6] :=
    overlap focused18407 torus24 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6] [12] (by decide)
  have hl : V [7, 0, 2, 1, 7, 1, 1, 2, 11, 12] = V [7, 0, 2, 1, 7, 1, 1, 2] :=
    (in_context torus24 [7, 0, 2, 1, 7, 1, 1, 2] [])
  have hr : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18409 : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] = V [7, 0, 2, 1, 7, 1, 1, 2, 6] := by
  have h0 : V [7, 0, 2, 1, 7, 1, 1, 2, 6] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] :=
    overlap focused18408 torus6 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] [6] (by decide)
  have hl : V [7, 0, 2, 1, 7, 1, 1, 2, 6] = V [7, 0, 2, 1, 7, 1, 1, 2, 6] :=
    rfl
  have hr : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18410 : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] = V [7, 0, 2, 1, 7, 1, 1, 2, 6, 7] := by
  have h0 : V [7, 0, 2, 1, 7, 1, 1, 2, 6, 7] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] :=
    overlap focused18409 torus7 [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] [7] (by decide)
  have hl : V [7, 0, 2, 1, 7, 1, 1, 2, 6, 7] = V [7, 0, 2, 1, 7, 1, 1, 2, 6, 7] :=
    rfl
  have hr : V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] = V [1, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18482 : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4, 11] = V [0, 8, 7, 3, 4, 1, 8, 11] := by
  have h0 : V [4, 1, 2, 11, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] = V [7, 0, 2, 1, 6, 7, 1, 7, 8, 7, 0, 2, 1, 7, 1, 1, 2, 6, 7] :=
    overlap torus5680 focused18410 [7, 0, 2, 1, 6, 7, 1, 7, 8] [5, 0, 7, 0, 4, 3, 6, 7, 1, 4] (by decide)
  have hl : V [4, 1, 2, 11, 5, 0, 7, 0, 4, 3, 6, 7, 1, 4] = V [0, 8, 7, 3, 4, 1, 8, 11] :=
    ((in_context torus65 [4, 1, 2] [0, 7, 0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus2 [4, 1] [11, 0, 7, 0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus91 [4, 1] [7, 0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus1 [4] [11, 7, 0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus77 [4] [0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus4 [] [11, 0, 4, 3, 6, 7, 1, 4]).trans ((in_context torus91 [] [4, 3, 6, 7, 1, 4]).trans ((in_context torus59 [0] [3, 6, 7, 1, 4]).trans ((in_context torus53 [0, 8] [6, 7, 1, 4]).trans ((in_context torus71 [0, 8, 7] [7, 1, 4]).trans ((in_context torus77 [0, 8, 7, 3] [1, 4]).trans ((in_context torus92 [0, 8, 7, 3, 4] [4]).trans (in_context torus59 [0, 8, 7, 3, 4, 1] [])))))))))))))
  have hr : V [7, 0, 2, 1, 6, 7, 1, 7, 8, 7, 0, 2, 1, 7, 1, 1, 2, 6, 7] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4, 11] :=
    ((in_context torus5977 [] [7, 0, 2, 1, 7, 1, 1, 2, 6, 7]).trans ((in_context torus77 [4, 1, 2, 0] [0, 2, 1, 7, 1, 1, 2, 6, 7]).trans ((in_context torus91 [4, 1, 2, 0, 4] [2, 1, 7, 1, 1, 2, 6, 7]).trans ((in_context torus47 [4, 1, 2, 0, 4, 0] [1, 7, 1, 1, 2, 6, 7]).trans ((in_context torus92 [4, 1, 2, 0, 4, 0, 6] [7, 1, 1, 2, 6, 7]).trans ((in_context torus77 [4, 1, 2, 0, 4, 0, 6, 1] [1, 1, 2, 6, 7]).trans ((in_context torus92 [4, 1, 2, 0, 4, 0, 6, 1, 4] [1, 2, 6, 7]).trans ((in_context torus92 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] [2, 6, 7]).trans ((in_context torus47 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] [6, 7]).trans ((in_context torus71 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] [7]).trans (in_context torus77 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18483 : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4] = V [0, 8, 7, 3, 4, 1, 8] := by
  have h0 : V [0, 8, 7, 3, 4, 1, 8, 11, 12] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4] :=
    overlap focused18482 torus24 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4] [12] (by decide)
  have hl : V [0, 8, 7, 3, 4, 1, 8, 11, 12] = V [0, 8, 7, 3, 4, 1, 8] :=
    (in_context torus24 [0, 8, 7, 3, 4, 1, 8] [])
  have hr : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18484 : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [0, 8, 7, 3, 4, 1, 8, 4] := by
  have h0 : V [0, 8, 7, 3, 4, 1, 8, 4] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] :=
    overlap focused18483 torus4 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] [4] (by decide)
  have hl : V [0, 8, 7, 3, 4, 1, 8, 4] = V [0, 8, 7, 3, 4, 1, 8, 4] :=
    rfl
  have hr : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18485 : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] = V [0, 8, 7, 3, 4, 1, 8, 4, 3] := by
  have h0 : V [0, 8, 7, 3, 4, 1, 8, 4, 3] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] :=
    overlap focused18484 torus3 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] [3] (by decide)
  have hl : V [0, 8, 7, 3, 4, 1, 8, 4, 3] = V [0, 8, 7, 3, 4, 1, 8, 4, 3] :=
    rfl
  have hr : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18486 : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] = V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6] := by
  have h0 : V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] :=
    overlap focused18485 torus6 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] [6] (by decide)
  have hl : V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6] = V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6] :=
    rfl
  have hr : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18490 : V [2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [0, 4, 0, 8, 7, 3, 4, 1, 8, 4] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [4, 3, 4, 5, 0, 8, 7, 3, 4, 1, 8, 4] :=
    overlap torus100 focused18484 [4, 3, 4, 5] [1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] :=
    ((in_context torus143 [] [1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3]).trans ((in_context torus1428 [] [3, 2, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3]).trans ((in_context torus3 [0, 2] [2, 1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3]).trans ((in_context torus2 [0] [1, 2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3]).trans (in_context torus0 [] [2, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3])))))
  have hr : V [4, 3, 4, 5, 0, 8, 7, 3, 4, 1, 8, 4] = V [0, 4, 0, 8, 7, 3, 4, 1, 8, 4] :=
    ((in_context torus1448 [] [5, 0, 8, 7, 3, 4, 1, 8, 4]).trans (in_context torus5 [0, 4] [0, 8, 7, 3, 4, 1, 8, 4]))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18491 : V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8, 4] = V [0, 6, 1, 4, 1, 1, 6, 3] := by
  have h0 : V [4, 1, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 0, 4, 0, 8, 7, 3, 4, 1, 8, 4] :=
    overlap torus5285 focused18490 [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8] [0, 4, 0, 6, 1, 4, 1, 1, 6, 3] (by decide)
  have hl : V [4, 1, 0, 4, 0, 6, 1, 4, 1, 1, 6, 3] = V [0, 6, 1, 4, 1, 1, 6, 3] :=
    ((in_context torus1 [4] [4, 0, 6, 1, 4, 1, 1, 6, 3]).trans (in_context torus4 [] [0, 6, 1, 4, 1, 1, 6, 3]))
  have hr : V [1, 8, 2, 1, 2, 1, 6, 0, 2, 7, 8, 0, 4, 0, 8, 7, 3, 4, 1, 8, 4] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8, 4] :=
    (in_context torus5287 [] [0, 4, 0, 8, 7, 3, 4, 1, 8, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18492 : V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8] = V [0, 6, 1, 4, 1, 1, 6, 3, 4] := by
  have h0 : V [0, 6, 1, 4, 1, 1, 6, 3, 4] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8] :=
    overlap focused18491 torus4 [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8] [4] (by decide)
  have hl : V [0, 6, 1, 4, 1, 1, 6, 3, 4] = V [0, 6, 1, 4, 1, 1, 6, 3, 4] :=
    rfl
  have hr : V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18498 : V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] := by
  have h0 : V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] :=
    overlap focused18486 torus1 [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] [0] (by decide)
  have hl : V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] = V [0, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] :=
    rfl
  have hr : V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] = V [4, 1, 2, 0, 4, 0, 6, 1, 4, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18499 : V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1, 4, 1] = V [7, 3, 4, 1, 8, 4, 3, 6, 0] := by
  have h0 : V [8, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] = V [4, 2, 0, 5, 3, 5, 6, 8, 4, 1, 2, 0, 4, 0, 6, 1, 4, 1] :=
    overlap torus1952 focused18498 [4, 2, 0, 5, 3, 5, 6, 8] [8, 7, 3, 4, 1, 8, 4, 3, 6, 0] (by decide)
  have hl : V [8, 8, 7, 3, 4, 1, 8, 4, 3, 6, 0] = V [7, 3, 4, 1, 8, 4, 3, 6, 0] :=
    (in_context torus8 [] [7, 3, 4, 1, 8, 4, 3, 6, 0])
  have hr : V [4, 2, 0, 5, 3, 5, 6, 8, 4, 1, 2, 0, 4, 0, 6, 1, 4, 1] = V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1, 4, 1] :=
    (in_context torus1953 [] [4, 1, 2, 0, 4, 0, 6, 1, 4, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18502 : V [0, 6, 1, 4, 1, 1, 6, 3, 4, 8, 0] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4] := by
  have h0 : V [0, 6, 1, 4, 1, 1, 6, 3, 4, 7, 8, 2, 8] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 3, 2, 3, 4, 3] :=
    overlap focused18492 torus135 [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1] [7, 8, 2, 8] (by decide)
  have hl : V [0, 6, 1, 4, 1, 1, 6, 3, 4, 7, 8, 2, 8] = V [0, 6, 1, 4, 1, 1, 6, 3, 4, 8, 0] :=
    (in_context torus1486 [0, 6, 1, 4, 1, 1, 6, 3, 4] [])
  have hr : V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4, 1, 3, 2, 3, 4, 3] = V [4, 1, 2, 0, 4, 0, 8, 7, 3, 4] :=
    ((in_context torus1554 [4, 1, 2, 0, 4, 0, 8, 7, 3] [3, 4, 3]).trans ((in_context torus1550 [4, 1, 2, 0, 4, 0, 8, 7] [3, 3, 4, 3]).trans ((in_context torus1479 [4, 1, 2, 0, 4, 0] [3, 2, 4, 3, 3, 4, 3]).trans ((in_context torus3 [4, 1, 2, 0, 4, 0, 0, 7, 8, 3, 2, 4] [4, 3]).trans ((in_context torus4 [4, 1, 2, 0, 4, 0, 0, 7, 8, 3, 2] [3]).trans ((in_context torus1439 [4, 1, 2, 0, 4, 0, 0, 7, 8] []).trans (in_context torus1483 [4, 1, 2, 0, 4, 0] [3, 4])))))))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18503 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3, 4] = V [1, 1, 6, 3, 4, 8, 0] := by
  have h0 : V [4, 0, 6, 6, 1, 4, 1, 1, 6, 3, 4, 8, 0] = V [8, 3, 1, 7, 0, 2, 5, 3, 4, 1, 2, 0, 4, 0, 8, 7, 3, 4] :=
    overlap torus2220 focused18502 [8, 3, 1, 7, 0, 2, 5, 3] [6, 1, 4, 1, 1, 6, 3, 4, 8, 0] (by decide)
  have hl : V [4, 0, 6, 6, 1, 4, 1, 1, 6, 3, 4, 8, 0] = V [1, 1, 6, 3, 4, 8, 0] :=
    ((in_context torus6 [4, 0] [1, 4, 1, 1, 6, 3, 4, 8, 0]).trans ((in_context torus0 [4] [4, 1, 1, 6, 3, 4, 8, 0]).trans (in_context torus4 [] [1, 1, 6, 3, 4, 8, 0])))
  have hr : V [8, 3, 1, 7, 0, 2, 5, 3, 4, 1, 2, 0, 4, 0, 8, 7, 3, 4] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3, 4] :=
    (in_context torus2322 [] [4, 1, 2, 0, 4, 0, 8, 7, 3, 4])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18504 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3] = V [1, 1, 6, 3, 4, 8, 0, 4] := by
  have h0 : V [1, 1, 6, 3, 4, 8, 0, 4] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3] :=
    overlap focused18503 torus4 [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3] [4] (by decide)
  have hl : V [1, 1, 6, 3, 4, 8, 0, 4] = V [1, 1, 6, 3, 4, 8, 0, 4] :=
    rfl
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18505 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7] = V [1, 1, 6, 3, 4, 8, 0, 4, 3] := by
  have h0 : V [1, 1, 6, 3, 4, 8, 0, 4, 3] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7] :=
    overlap focused18504 torus3 [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7] [3] (by decide)
  have hl : V [1, 1, 6, 3, 4, 8, 0, 4, 3] = V [1, 1, 6, 3, 4, 8, 0, 4, 3] :=
    rfl
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18507 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7] := by
  have h0 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] :=
    overlap focused18505 torus7 [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] [7] (by decide)
  have hl : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7] :=
    rfl
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18512 : V [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] = V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1] := by
  have h0 : V [7, 3, 4, 1, 8, 4, 3, 6, 0, 8, 0, 5, 1, 2, 0, 4, 6, 5, 12] = V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    overlap focused18499 torus2211 [8, 1, 4, 1, 2, 0, 4, 0, 6, 1] [8, 0, 5, 1, 2, 0, 4, 6, 5, 12] (by decide)
  have hl : V [7, 3, 4, 1, 8, 4, 3, 6, 0, 8, 0, 5, 1, 2, 0, 4, 6, 5, 12] = V [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] :=
    ((in_context torus4267 [7, 3, 4, 1, 8, 4, 3, 6, 0] [4, 6, 5, 12]).trans ((in_context torus59 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 2, 3, 8] [6, 5, 12]).trans ((in_context torus8 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 2, 3] [11, 6, 5, 12]).trans ((in_context torus71 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 2, 3] [5, 12]).trans ((in_context torus3 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 2] [11, 5, 12]).trans ((in_context torus65 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 2] [12]).trans ((in_context torus2 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] [11, 12]).trans (in_context torus24 [7, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] []))))))))
  have hr : V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1] = V [8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18513 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] = V [4] := by
  have h0 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    overlap focused18505 focused18512 [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8] [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] (by decide)
  have hl : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 3, 4, 1, 8, 4, 3, 6, 0, 0, 4] = V [4] :=
    ((in_context torus3 [1, 1, 6, 3, 4, 8, 0, 4] [4, 1, 8, 4, 3, 6, 0, 0, 4]).trans ((in_context torus4 [1, 1, 6, 3, 4, 8, 0] [1, 8, 4, 3, 6, 0, 0, 4]).trans ((in_context torus0 [1, 1, 6, 3, 4, 8] [8, 4, 3, 6, 0, 0, 4]).trans ((in_context torus8 [1, 1, 6, 3, 4] [4, 3, 6, 0, 0, 4]).trans ((in_context torus4 [1, 1, 6, 3] [3, 6, 0, 0, 4]).trans ((in_context torus3 [1, 1, 6] [6, 0, 0, 4]).trans ((in_context torus6 [1, 1] [0, 0, 4]).trans ((in_context torus1 [1] [0, 4]).trans (in_context torus1 [] [4])))))))))
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 0, 8, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    (in_context focused18507 [] [8, 1, 4, 1, 2, 0, 4, 0, 6, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18516 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4] = V [4, 0, 6, 1] := by
  have h0 : V [4, 4, 2, 3, 8, 0, 4, 1, 7, 11] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4] :=
    overlap focused18513 torus2482 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4] [4, 2, 3, 8, 0, 4, 1, 7, 11] (by decide)
  have hl : V [4, 4, 2, 3, 8, 0, 4, 1, 7, 11] = V [4, 0, 6, 1] :=
    ((in_context torus4 [] [2, 3, 8, 0, 4, 1, 7, 11]).trans ((in_context torus4445 [2] [11]).trans ((in_context torus2 [] [4, 0, 6, 1, 12, 11]).trans (in_context torus29 [4, 0, 6, 1] []))))
  have hr : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18517 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] = V [4, 0, 6, 1, 4] := by
  have h0 : V [4, 0, 6, 1, 4] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] :=
    overlap focused18516 torus4 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] [4] (by decide)
  have hl : V [4, 0, 6, 1, 4] = V [4, 0, 6, 1, 4] :=
    rfl
  have hr : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18519 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1] = V [4, 0, 6, 1, 4, 1, 2] := by
  have h0 : V [4, 0, 6, 1, 1, 8, 0, 5, 1, 2, 4, 3, 12] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 1, 2] :=
    overlap focused18516 torus2209 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0] [1, 8, 0, 5, 1, 2, 4, 3, 12] (by decide)
  have hl : V [4, 0, 6, 1, 1, 8, 0, 5, 1, 2, 4, 3, 12] = V [4, 0, 6, 1, 4, 1, 2] :=
    ((in_context torus5617 [4] [4, 3, 12]).trans (in_context torus8756 [4] []))
  have hr : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 0, 1, 2] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1] :=
    ((in_context torus0 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2] [2]).trans (in_context torus2 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18520 : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4] = V [4, 0, 6, 1, 4, 1, 2, 0] := by
  have h0 : V [4, 0, 6, 1, 4, 3, 4, 1, 2, 8, 3, 2, 4, 3] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 2, 0] :=
    overlap focused18517 torus2157 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2] [3, 4, 1, 2, 8, 3, 2, 4, 3] (by decide)
  have hl : V [4, 0, 6, 1, 4, 3, 4, 1, 2, 8, 3, 2, 4, 3] = V [4, 0, 6, 1, 4, 1, 2, 0] :=
    ((in_context torus1448 [4, 0, 6, 1] [1, 2, 8, 3, 2, 4, 3]).trans ((in_context torus1 [4, 0, 6] [4, 5, 1, 2, 8, 3, 2, 4, 3]).trans ((in_context torus11159 [4, 0, 6] [4, 3]).trans ((in_context torus1516 [4, 0, 6, 1, 4, 1] [3]).trans (in_context torus3 [4, 0, 6, 1, 4, 1, 2, 0] [])))))
  have hr : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1, 2, 2, 0] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4] :=
    ((in_context torus2 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 1] [0]).trans (in_context torus1 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18521 : V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] = V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] := by
  have h0 : V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] = V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    overlap torus7 focused18512 [7] [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] (by decide)
  have hl : V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] = V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4] :=
    rfl
  have hr : V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] = V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18528 : V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 0] = V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6] := by
  have h0 : V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 0] = V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6] :=
    overlap focused18521 torus1 [7, 8, 1, 4, 1, 2, 0, 4, 0, 6] [0] (by decide)
  have hl : V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 0] = V [3, 4, 1, 8, 4, 3, 6, 0, 0, 4, 0] :=
    rfl
  have hr : V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6] = V [7, 8, 1, 4, 1, 2, 0, 4, 0, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18529 : V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6] = V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0] := by
  have h0 : V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0] = V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6] :=
    overlap torus3 focused18528 [3] [4, 1, 8, 4, 3, 6, 0, 0, 4, 0] (by decide)
  have hl : V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0] = V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0] :=
    rfl
  have hr : V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6] = V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18536 : V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] = V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0] := by
  have h0 : V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] = V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0] :=
    overlap focused18529 torus6 [3, 7, 8, 1, 4, 1, 2, 0, 4, 0] [6] (by decide)
  have hl : V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] = V [4, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] :=
    rfl
  have hr : V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0] = V [3, 7, 8, 1, 4, 1, 2, 0, 4, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18558 : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0, 11] = V [3, 0, 0, 8, 0, 3, 11] := by
  have h0 : V [7, 8, 5, 0, 11, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] = V [1, 1, 8, 7, 3, 1, 7, 0, 3, 7, 8, 1, 4, 1, 2, 0, 4, 0] :=
    overlap torus7369 focused18536 [1, 1, 8, 7, 3, 1, 7, 0] [1, 8, 4, 3, 6, 0, 0, 4, 0, 6] (by decide)
  have hl : V [7, 8, 5, 0, 11, 1, 8, 4, 3, 6, 0, 0, 4, 0, 6] = V [3, 0, 0, 8, 0, 3, 11] :=
    ((in_context torus92 [7, 8, 5, 0] [8, 4, 3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus0 [7, 8, 5] [11, 8, 4, 3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus83 [7, 8, 5] [4, 3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus5 [7, 8] [11, 4, 3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus59 [7, 8] [3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus8 [7] [11, 3, 6, 0, 0, 4, 0, 6]).trans ((in_context torus53 [7] [6, 0, 0, 4, 0, 6]).trans ((in_context torus7 [] [11, 6, 0, 0, 4, 0, 6]).trans ((in_context torus71 [] [0, 0, 4, 0, 6]).trans ((in_context torus91 [3] [0, 4, 0, 6]).trans ((in_context torus91 [3, 0] [4, 0, 6]).trans ((in_context torus59 [3, 0, 0] [0, 6]).trans ((in_context torus91 [3, 0, 0, 8] [6]).trans (in_context torus71 [3, 0, 0, 8, 0] []))))))))))))))
  have hr : V [1, 1, 8, 7, 3, 1, 7, 0, 3, 7, 8, 1, 4, 1, 2, 0, 4, 0] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0, 11] :=
    ((in_context torus8944 [] [3, 7, 8, 1, 4, 1, 2, 0, 4, 0]).trans ((in_context torus53 [7, 8, 5, 0, 8] [7, 8, 1, 4, 1, 2, 0, 4, 0]).trans ((in_context torus77 [7, 8, 5, 0, 8, 7] [8, 1, 4, 1, 2, 0, 4, 0]).trans ((in_context torus83 [7, 8, 5, 0, 8, 7, 4] [1, 4, 1, 2, 0, 4, 0]).trans ((in_context torus92 [7, 8, 5, 0, 8, 7, 4, 5] [4, 1, 2, 0, 4, 0]).trans ((in_context torus59 [7, 8, 5, 0, 8, 7, 4, 5, 1] [1, 2, 0, 4, 0]).trans ((in_context torus92 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8] [2, 0, 4, 0]).trans ((in_context torus47 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1] [0, 4, 0]).trans ((in_context torus91 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6] [4, 0]).trans ((in_context torus59 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] [0]).trans (in_context torus91 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18559 : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0] = V [3, 0, 0, 8, 0, 3] := by
  have h0 : V [3, 0, 0, 8, 0, 3, 11, 12] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0] :=
    overlap focused18558 torus24 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0] [12] (by decide)
  have hl : V [3, 0, 0, 8, 0, 3, 11, 12] = V [3, 0, 0, 8, 0, 3] :=
    (in_context torus24 [3, 0, 0, 8, 0, 3] [])
  have hr : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18560 : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] = V [3, 0, 0, 8, 0, 3, 1] := by
  have h0 : V [3, 0, 0, 8, 0, 3, 1] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] :=
    overlap focused18559 torus0 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] [1] (by decide)
  have hl : V [3, 0, 0, 8, 0, 3, 1] = V [3, 0, 0, 8, 0, 3, 1] :=
    rfl
  have hr : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18561 : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] = V [3, 0, 0, 8, 0, 3, 1, 8] := by
  have h0 : V [3, 0, 0, 8, 0, 3, 1, 8] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] :=
    overlap focused18560 torus8 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] [8] (by decide)
  have hl : V [3, 0, 0, 8, 0, 3, 1, 8] = V [3, 0, 0, 8, 0, 3, 1, 8] :=
    rfl
  have hr : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18567 : V [3, 0, 0, 8, 0, 3, 1, 8, 1, 6, 0] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8] := by
  have h0 : V [3, 0, 0, 8, 0, 3, 1, 8, 7, 8, 1, 6, 5, 7, 6, 8, 7] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 6, 0] :=
    overlap focused18561 torus2169 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6] [7, 8, 1, 6, 5, 7, 6, 8, 7] (by decide)
  have hl : V [3, 0, 0, 8, 0, 3, 1, 8, 7, 8, 1, 6, 5, 7, 6, 8, 7] = V [3, 0, 0, 8, 0, 3, 1, 8, 1, 6, 0] :=
    ((in_context torus1484 [3, 0, 0, 8, 0, 3, 1] [1, 6, 5, 7, 6, 8, 7]).trans ((in_context torus1 [3, 0, 0, 8, 0, 3] [8, 2, 1, 6, 5, 7, 6, 8, 7]).trans ((in_context torus11666 [3, 0, 0, 8, 0, 3] [8, 7]).trans ((in_context torus1525 [3, 0, 0, 8, 0, 3, 1, 8, 1] [7]).trans (in_context torus7 [3, 0, 0, 8, 0, 3, 1, 8, 1, 6, 0] [])))))
  have hr : V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1, 6, 6, 0] = V [7, 8, 5, 0, 8, 7, 4, 5, 1, 8] :=
    ((in_context torus6 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8, 1] [0]).trans (in_context torus1 [7, 8, 5, 0, 8, 7, 4, 5, 1, 8] []))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18568 : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1, 8] = V [0, 3, 1, 8, 1, 6, 0] := by
  have h0 : V [8, 1, 1, 0, 0, 8, 0, 3, 1, 8, 1, 6, 0] = V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 7, 8, 5, 0, 8, 7, 4, 5, 1, 8] :=
    overlap torus5248 focused18567 [1, 5, 0, 2, 1, 1, 4, 0, 7, 1] [0, 0, 8, 0, 3, 1, 8, 1, 6, 0] (by decide)
  have hl : V [8, 1, 1, 0, 0, 8, 0, 3, 1, 8, 1, 6, 0] = V [0, 3, 1, 8, 1, 6, 0] :=
    ((in_context torus1 [8, 1] [0, 8, 0, 3, 1, 8, 1, 6, 0]).trans ((in_context torus1 [8] [8, 0, 3, 1, 8, 1, 6, 0]).trans (in_context torus8 [] [0, 3, 1, 8, 1, 6, 0])))
  have hr : V [1, 5, 0, 2, 1, 1, 4, 0, 7, 1, 7, 8, 5, 0, 8, 7, 4, 5, 1, 8] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1, 8] :=
    (in_context torus5349 [] [7, 8, 5, 0, 8, 7, 4, 5, 1, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18571 : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5] = V [0, 3, 1, 8, 1, 6, 0, 8, 0] := by
  have h0 : V [0, 3, 1, 8, 1, 6, 0, 7, 8, 2, 8] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1, 3, 2, 3, 4, 3] :=
    overlap focused18568 torus135 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1] [7, 8, 2, 8] (by decide)
  have hl : V [0, 3, 1, 8, 1, 6, 0, 7, 8, 2, 8] = V [0, 3, 1, 8, 1, 6, 0, 8, 0] :=
    ((in_context torus1574 [0, 3, 1, 8, 1] [2, 8]).trans ((in_context torus2061 [0, 3, 1, 8, 1, 1] []).trans (in_context torus1 [0, 3, 1, 8, 1] [6, 0, 8, 0])))
  have hr : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1, 3, 2, 3, 4, 3] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5] :=
    ((in_context torus143 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1] []).trans ((in_context torus1428 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 1] [3, 2]).trans ((in_context torus1 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5] [2, 3, 3, 2]).trans ((in_context torus3 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5, 2] [2]).trans (in_context torus2 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4, 5] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18573 : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4] = V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5] := by
  have h0 : V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4] :=
    overlap focused18571 torus5 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4] [5] (by decide)
  have hl : V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5] = V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5] :=
    rfl
  have hr : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18589 : V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7] := by
  have h0 : V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7] :=
    overlap focused18573 torus4 [8, 1, 1, 3, 7, 8, 5, 0, 8, 7] [4] (by decide)
  have hl : V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] = V [0, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] :=
    rfl
  have hr : V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7] = V [8, 1, 1, 3, 7, 8, 5, 0, 8, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18590 : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8, 7] = V [1, 6, 0, 8, 0, 5, 4] := by
  have h0 : V [8, 0, 3, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] = V [5, 7, 1, 4, 0, 6, 2, 7, 8, 1, 1, 3, 7, 8, 5, 0, 8, 7] :=
    overlap torus2200 focused18589 [5, 7, 1, 4, 0, 6, 2, 7] [3, 1, 8, 1, 6, 0, 8, 0, 5, 4] (by decide)
  have hl : V [8, 0, 3, 3, 1, 8, 1, 6, 0, 8, 0, 5, 4] = V [1, 6, 0, 8, 0, 5, 4] :=
    ((in_context torus3 [8, 0] [1, 8, 1, 6, 0, 8, 0, 5, 4]).trans ((in_context torus0 [8] [8, 1, 6, 0, 8, 0, 5, 4]).trans (in_context torus8 [] [1, 6, 0, 8, 0, 5, 4])))
  have hr : V [5, 7, 1, 4, 0, 6, 2, 7, 8, 1, 1, 3, 7, 8, 5, 0, 8, 7] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8, 7] :=
    (in_context torus2318 [] [8, 1, 1, 3, 7, 8, 5, 0, 8, 7])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18591 : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8] = V [1, 6, 0, 8, 0, 5, 4, 7] := by
  have h0 : V [1, 6, 0, 8, 0, 5, 4, 7] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8] :=
    overlap focused18590 torus7 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8] [7] (by decide)
  have hl : V [1, 6, 0, 8, 0, 5, 4, 7] = V [1, 6, 0, 8, 0, 5, 4, 7] :=
    rfl
  have hr : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18594 : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5] = V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1] := by
  have h0 : V [1, 6, 0, 8, 0, 5, 4, 7, 2, 8, 7, 8] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 3, 4, 3, 2, 3] :=
    overlap focused18591 torus138 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0] [2, 8, 7, 8] (by decide)
  have hl : V [1, 6, 0, 8, 0, 5, 4, 7, 2, 8, 7, 8] = V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1] :=
    ((in_context torus1484 [1, 6, 0, 8, 0, 5, 4, 7, 2] []).trans (in_context torus1491 [1, 6, 0, 8, 0, 5, 4, 7] []))
  have hr : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 0, 3, 4, 3, 2, 3] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5] :=
    ((in_context torus1562 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] [3, 2, 3]).trans ((in_context torus1555 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] [2, 3]).trans ((in_context torus2 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5, 3] [3]).trans (in_context torus3 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8, 5] []))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18617 : V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] := by
  have h0 : V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] :=
    overlap focused18594 torus5 [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] [5] (by decide)
  have hl : V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] = V [1, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] :=
    rfl
  have hr : V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] = V [8, 0, 3, 1, 8, 1, 1, 3, 7, 8] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18714 : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 11] = V [0, 2, 8, 4, 5, 1, 2, 11] := by
  have h0 : V [5, 1, 3, 11, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] = V [7, 6, 8, 1, 5, 0, 2, 8, 0, 3, 1, 8, 1, 1, 3, 7, 8] :=
    overlap torus3348 focused18617 [7, 6, 8, 1, 5, 0, 2] [6, 0, 8, 0, 5, 4, 7, 8, 1, 5] (by decide)
  have hl : V [5, 1, 3, 11, 6, 0, 8, 0, 5, 4, 7, 8, 1, 5] = V [0, 2, 8, 4, 5, 1, 2, 11] :=
    ((in_context torus71 [5, 1, 3] [0, 8, 0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus3 [5, 1] [11, 0, 8, 0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus91 [5, 1] [8, 0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus1 [5] [11, 8, 0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus83 [5] [0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus5 [] [11, 0, 5, 4, 7, 8, 1, 5]).trans ((in_context torus91 [] [5, 4, 7, 8, 1, 5]).trans ((in_context torus65 [0] [4, 7, 8, 1, 5]).trans ((in_context torus59 [0, 2] [7, 8, 1, 5]).trans ((in_context torus77 [0, 2, 8] [8, 1, 5]).trans ((in_context torus83 [0, 2, 8, 4] [1, 5]).trans ((in_context torus92 [0, 2, 8, 4, 5] [5]).trans (in_context torus65 [0, 2, 8, 4, 5, 1] [])))))))))))))
  have hr : V [7, 6, 8, 1, 5, 0, 2, 8, 0, 3, 1, 8, 1, 1, 3, 7, 8] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 11] :=
    ((in_context torus3349 [] [8, 0, 3, 1, 8, 1, 1, 3, 7, 8]).trans ((in_context torus83 [5, 1, 3, 0] [0, 3, 1, 8, 1, 1, 3, 7, 8]).trans ((in_context torus91 [5, 1, 3, 0, 5] [3, 1, 8, 1, 1, 3, 7, 8]).trans ((in_context torus53 [5, 1, 3, 0, 5, 0] [1, 8, 1, 1, 3, 7, 8]).trans ((in_context torus92 [5, 1, 3, 0, 5, 0, 7] [8, 1, 1, 3, 7, 8]).trans ((in_context torus83 [5, 1, 3, 0, 5, 0, 7, 1] [1, 1, 3, 7, 8]).trans ((in_context torus92 [5, 1, 3, 0, 5, 0, 7, 1, 5] [1, 3, 7, 8]).trans ((in_context torus92 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1] [3, 7, 8]).trans ((in_context torus53 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1] [7, 8]).trans ((in_context torus77 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7] [8]).trans (in_context torus83 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] [])))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18715 : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5] = V [0, 2, 8, 4, 5, 1, 2] := by
  have h0 : V [0, 2, 8, 4, 5, 1, 2, 11, 12] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5] :=
    overlap focused18714 torus24 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5] [12] (by decide)
  have hl : V [0, 2, 8, 4, 5, 1, 2, 11, 12] = V [0, 2, 8, 4, 5, 1, 2] :=
    (in_context torus24 [0, 2, 8, 4, 5, 1, 2] [])
  have hr : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18716 : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [0, 2, 8, 4, 5, 1, 2, 5] := by
  have h0 : V [0, 2, 8, 4, 5, 1, 2, 5] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] :=
    overlap focused18715 torus5 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] [5] (by decide)
  have hl : V [0, 2, 8, 4, 5, 1, 2, 5] = V [0, 2, 8, 4, 5, 1, 2, 5] :=
    rfl
  have hr : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18722 : V [0, 2, 8, 4, 5, 1, 2, 5, 4, 7, 0] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1] := by
  have h0 : V [0, 2, 8, 4, 5, 1, 2, 5, 1, 2, 0, 5, 1, 3, 7, 1, 7, 4, 11] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 7, 0] :=
    overlap focused18716 torus5219 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7] [1, 2, 0, 5, 1, 3, 7, 1, 7, 4, 11] (by decide)
  have hl : V [0, 2, 8, 4, 5, 1, 2, 5, 1, 2, 0, 5, 1, 3, 7, 1, 7, 4, 11] = V [0, 2, 8, 4, 5, 1, 2, 5, 4, 7, 0] :=
    ((in_context torus5345 [0, 2, 8, 4, 5, 1, 2, 5] [11]).trans (in_context torus29 [0, 2, 8, 4, 5, 1, 2, 5, 4, 7, 0] []))
  have hr : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 7, 0] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 1] :=
    ((in_context torus7 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1] [0]).trans (in_context torus1 [5, 1, 3, 0, 5, 0, 7, 1, 5, 1] []))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18723 : V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5, 1] = V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0] := by
  have h0 : V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0] = V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5, 1] :=
    overlap torus1 focused18722 [1] [2, 8, 4, 5, 1, 2, 5, 4, 7, 0] (by decide)
  have hl : V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0] = V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0] :=
    rfl
  have hr : V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5, 1] = V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18724 : V [3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [0, 5, 0, 2, 8, 4, 5, 1, 2, 5] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [5, 4, 5, 6, 0, 2, 8, 4, 5, 1, 2, 5] :=
    overlap torus108 focused18716 [5, 4, 5, 6] [1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] :=
    ((in_context torus143 [] [1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans ((in_context torus2 [0] [1, 3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans (in_context torus0 [] [3, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4])))))
  have hr : V [5, 4, 5, 6, 0, 2, 8, 4, 5, 1, 2, 5] = V [0, 5, 0, 2, 8, 4, 5, 1, 2, 5] :=
    ((in_context torus1457 [] [6, 0, 2, 8, 4, 5, 1, 2, 5]).trans (in_context torus6 [0, 5] [0, 2, 8, 4, 5, 1, 2, 5]))
  exact hl.symm.trans (h0.trans hr)

private theorem focused18725 : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5] = V [0, 7, 1, 5, 1, 1, 7, 4] := by
  have h0 : V [6, 5, 4, 5, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [5, 3, 4, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5] :=
    overlap torus113 focused18724 [5, 3, 4, 3, 2] [0, 5, 0, 7, 1, 5, 1, 1, 7, 4] (by decide)
  have hl : V [6, 5, 4, 5, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4] = V [0, 7, 1, 5, 1, 1, 7, 4] :=
    ((in_context torus1462 [] [5, 0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans ((in_context torus5 [5, 1] [0, 5, 0, 7, 1, 5, 1, 1, 7, 4]).trans ((in_context torus1 [5] [5, 0, 7, 1, 5, 1, 1, 7, 4]).trans (in_context torus5 [] [0, 7, 1, 5, 1, 1, 7, 4]))))
  have hr : V [5, 3, 4, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5] :=
    ((in_context torus1442 [5] [2, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5]).trans ((in_context torus1446 [5] [2, 0, 5, 0, 2, 8, 4, 5, 1, 2, 5]).trans (in_context torus2 [5, 1, 3] [0, 5, 0, 2, 8, 4, 5, 1, 2, 5])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18727 : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2] = V [0, 7, 1, 5, 1, 1, 7, 4, 5] := by
  have h0 : V [0, 7, 1, 5, 1, 1, 7, 4, 5] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2] :=
    overlap focused18725 torus5 [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2] [5] (by decide)
  have hl : V [0, 7, 1, 5, 1, 1, 7, 4, 5] = V [0, 7, 1, 5, 1, 1, 7, 4, 5] :=
    rfl
  have hr : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18730 : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] = V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2] := by
  have h0 : V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] :=
    overlap focused18727 torus2 [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] [2] (by decide)
  have hl : V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2] :=
    rfl
  have hr : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18731 : V [0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [3, 0, 5, 0, 2, 8, 4, 5, 1] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] = V [5, 4, 5, 6, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] :=
    overlap torus108 focused18730 [5, 4, 5, 6] [1, 3, 0, 5, 0, 2, 8, 4, 5, 1] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1] = V [3, 0, 5, 0, 2, 8, 4, 5, 1] :=
    ((in_context torus143 [] [1, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus2 [0] [1, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans (in_context torus0 [] [3, 0, 5, 0, 2, 8, 4, 5, 1])))))
  have hr : V [5, 4, 5, 6, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [0, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] :=
    ((in_context torus1457 [] [6, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2]).trans (in_context torus6 [0, 5] [0, 7, 1, 5, 1, 1, 7, 4, 5, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18734 : V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0, 0] = V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5] := by
  have h0 : V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0, 0] = V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5] :=
    overlap focused18723 torus1 [1, 5, 1, 3, 0, 5, 0, 7, 1, 5] [0] (by decide)
  have hl : V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0, 0] = V [2, 8, 4, 5, 1, 2, 5, 4, 7, 0, 0] :=
    rfl
  have hr : V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5] = V [1, 5, 1, 3, 0, 5, 0, 7, 1, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18735 : V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1, 5] = V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0] := by
  have h0 : V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0] = V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1, 5] :=
    overlap torus2 focused18734 [2] [8, 4, 5, 1, 2, 5, 4, 7, 0, 0] (by decide)
  have hl : V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0] = V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0] :=
    rfl
  have hr : V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1, 5] = V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18737 : V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5] := by
  have h0 : V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5] :=
    overlap focused18730 torus1 [5, 1, 3, 0, 5, 0, 2, 8, 4, 5] [0] (by decide)
  have hl : V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] = V [0, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] :=
    rfl
  have hr : V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5] = V [5, 1, 3, 0, 5, 0, 2, 8, 4, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18738 : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4, 5] = V [1, 1, 7, 4, 5, 2, 0] := by
  have h0 : V [5, 0, 7, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] = V [2, 4, 1, 8, 0, 3, 6, 4, 5, 1, 3, 0, 5, 0, 2, 8, 4, 5] :=
    overlap torus2204 focused18737 [2, 4, 1, 8, 0, 3, 6, 4] [7, 1, 5, 1, 1, 7, 4, 5, 2, 0] (by decide)
  have hl : V [5, 0, 7, 7, 1, 5, 1, 1, 7, 4, 5, 2, 0] = V [1, 1, 7, 4, 5, 2, 0] :=
    ((in_context torus7 [5, 0] [1, 5, 1, 1, 7, 4, 5, 2, 0]).trans ((in_context torus0 [5] [5, 1, 1, 7, 4, 5, 2, 0]).trans (in_context torus5 [] [1, 1, 7, 4, 5, 2, 0])))
  have hr : V [2, 4, 1, 8, 0, 3, 6, 4, 5, 1, 3, 0, 5, 0, 2, 8, 4, 5] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4, 5] :=
    ((in_context torus2952 [2] [5, 1, 3, 0, 5, 0, 2, 8, 4, 5]).trans (in_context torus2 [] [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4, 5]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18739 : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4] = V [1, 1, 7, 4, 5, 2, 0, 5] := by
  have h0 : V [1, 1, 7, 4, 5, 2, 0, 5] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4] :=
    overlap focused18738 torus5 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4] [5] (by decide)
  have hl : V [1, 1, 7, 4, 5, 2, 0, 5] = V [1, 1, 7, 4, 5, 2, 0, 5] :=
    rfl
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 4] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18741 : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] = V [1, 1, 7, 4, 5, 2, 0, 5, 4] := by
  have h0 : V [1, 1, 7, 4, 5, 2, 0, 5, 4] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] :=
    overlap focused18739 torus4 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] [4] (by decide)
  have hl : V [1, 1, 7, 4, 5, 2, 0, 5, 4] = V [1, 1, 7, 4, 5, 2, 0, 5, 4] :=
    rfl
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18743 : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8] := by
  have h0 : V [1, 1, 7, 4, 5, 2, 0, 5, 2, 0, 5, 3, 5, 6, 8, 0] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 8] :=
    overlap focused18739 torus1952 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8] [2, 0, 5, 3, 5, 6, 8, 0] (by decide)
  have hl : V [1, 1, 7, 4, 5, 2, 0, 5, 2, 0, 5, 3, 5, 6, 8, 0] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8] :=
    ((in_context torus2146 [1, 1, 7, 4, 5, 2, 0, 5] [8, 0]).trans ((in_context torus1484 [1, 1, 7, 4, 5, 2, 0, 5, 4, 2] [0]).trans ((in_context torus1491 [1, 1, 7, 4, 5, 2, 0, 5, 4] [0]).trans (in_context torus1 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8] []))))
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 8, 8] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2] :=
    (in_context torus8 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18747 : V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1] := by
  have h0 : V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    overlap focused18735 torus5 [2, 1, 5, 1, 3, 0, 5, 0, 7, 1] [5] (by decide)
  have hl : V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [8, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] :=
    rfl
  have hr : V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18748 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [5] := by
  have h0 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    overlap focused18741 focused18747 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2] [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] (by decide)
  have hl : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [5] :=
    ((in_context torus4 [1, 1, 7, 4, 5, 2, 0, 5] [5, 1, 2, 5, 4, 7, 0, 0, 5]).trans ((in_context torus5 [1, 1, 7, 4, 5, 2, 0] [1, 2, 5, 4, 7, 0, 0, 5]).trans ((in_context torus0 [1, 1, 7, 4, 5, 2] [2, 5, 4, 7, 0, 0, 5]).trans ((in_context torus2 [1, 1, 7, 4, 5] [5, 4, 7, 0, 0, 5]).trans ((in_context torus5 [1, 1, 7, 4] [4, 7, 0, 0, 5]).trans ((in_context torus4 [1, 1, 7] [7, 0, 0, 5]).trans ((in_context torus7 [1, 1] [0, 0, 5]).trans ((in_context torus1 [1] [0, 5]).trans (in_context torus1 [] [5])))))))))
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 2, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    (in_context focused18743 [] [2, 1, 5, 1, 3, 0, 5, 0, 7, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18749 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [5, 0] := by
  have h0 : V [5, 0] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    overlap focused18748 torus1 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] [0] (by decide)
  have hl : V [5, 0] = V [5, 0] :=
    rfl
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18751 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5] = V [5, 0, 7, 1] := by
  have h0 : V [5, 4, 0, 6, 8, 7, 2, 1, 6, 12] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 1] :=
    overlap focused18748 torus3012 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0] [4, 0, 6, 8, 7, 2, 1, 6, 12] (by decide)
  have hl : V [5, 4, 0, 6, 8, 7, 2, 1, 6, 12] = V [5, 0, 7, 1] :=
    ((in_context torus4428 [5] [1, 6, 12]).trans ((in_context torus92 [5, 0, 7, 1, 3, 0] [6, 12]).trans ((in_context torus0 [5, 0, 7, 1, 3] [11, 6, 12]).trans ((in_context torus71 [5, 0, 7, 1, 3] [12]).trans ((in_context torus3 [5, 0, 7, 1] [11, 12]).trans (in_context torus24 [5, 0, 7, 1] []))))))
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 1] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5] :=
    (in_context torus0 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18752 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0] = V [5, 0, 7, 1, 5] := by
  have h0 : V [5, 0, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 1, 5] :=
    overlap focused18749 torus2968 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0] [2, 8, 3, 1, 7, 0, 4, 1, 12] (by decide)
  have hl : V [5, 0, 2, 8, 3, 1, 7, 0, 4, 1, 12] = V [5, 0, 7, 1, 5] :=
    ((in_context torus3422 [5, 0, 2] [12]).trans ((in_context torus2 [5, 0] [7, 1, 5, 11, 12]).trans (in_context torus24 [5, 0, 7, 1, 5] [])))
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 1, 5] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0] :=
    ((in_context torus0 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5] [5]).trans (in_context torus5 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18753 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3] = V [5, 0, 7, 1, 5, 1] := by
  have h0 : V [5, 0, 7, 1, 6, 5, 4, 5] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 3, 4, 3, 2, 3] :=
    overlap focused18751 torus111 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0] [6, 5, 4, 5] (by decide)
  have hl : V [5, 0, 7, 1, 6, 5, 4, 5] = V [5, 0, 7, 1, 5, 1] :=
    ((in_context torus1577 [5, 0] [4, 5]).trans ((in_context torus2017 [5, 0, 0] []).trans (in_context torus0 [5, 0] [7, 1, 5, 1])))
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 3, 4, 3, 2, 3] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3] :=
    ((in_context torus1440 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1] [4, 3, 2, 3]).trans ((in_context torus4 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 2, 3] [3, 2, 3]).trans ((in_context torus3 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 2] [2, 3]).trans (in_context torus2 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1] [3]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18755 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] = V [5, 0, 7, 1, 5, 1, 3, 0, 5] := by
  have h0 : V [5, 0, 7, 1, 5, 1, 2, 3, 4, 3, 5] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 5, 4, 5, 6] :=
    overlap focused18753 torus115 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1] [2, 3, 4, 3, 5] (by decide)
  have hl : V [5, 0, 7, 1, 5, 1, 2, 3, 4, 3, 5] = V [5, 0, 7, 1, 5, 1, 3, 0, 5] :=
    (in_context torus1441 [5, 0, 7, 1, 5, 1] [5])
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 5, 4, 5, 6] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] :=
    ((in_context torus1463 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] [5, 6]).trans ((in_context torus5 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 6] [6]).trans (in_context torus6 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18756 : V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] := by
  have h0 : V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    overlap torus8 focused18747 [8] [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] (by decide)
  have hl : V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] = V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5] :=
    rfl
  have hr : V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused18760 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0] := by
  have h0 : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0] :=
    overlap focused18743 torus2 [5, 0, 7, 1, 5, 1, 3, 0, 5, 0] [2] (by decide)
  have hl : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2] :=
    rfl
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0] = V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18762 : V [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] = V [0, 5, 0, 7, 1, 5, 1, 3, 0, 5] := by
  have h0 : V [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] = V [0, 5, 0, 7, 1, 5, 1, 3, 0, 5] :=
    overlap torus0 focused18755 [0] [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] (by decide)
  have hl : V [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] = V [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1] :=
    rfl
  have hr : V [0, 5, 0, 7, 1, 5, 1, 3, 0, 5] = V [0, 5, 0, 7, 1, 5, 1, 3, 0, 5] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused18764 : V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5, 0] = V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7] := by
  have h0 : V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5, 0] = V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    overlap focused18756 torus1 [8, 2, 1, 5, 1, 3, 0, 5, 0, 7] [0] (by decide)
  have hl : V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5, 0] = V [4, 5, 1, 2, 5, 4, 7, 0, 0, 5, 0] :=
    rfl
  have hr : V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused21454 : V [4, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] := by
  have h0 : V [0, 5, 7, 8, 2, 4, 5, 4, 7, 0, 0, 5, 0] = V [4, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    overlap torus4378 focused18764 [4, 1] [5, 4, 7, 0, 0, 5, 0] (by decide)
  have hl : V [0, 5, 7, 8, 2, 4, 5, 4, 7, 0, 0, 5, 0] = V [0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] :=
    ((in_context torus1451 [0, 5, 7, 8, 2] [7, 0, 0, 5, 0]).trans ((in_context torus1429 [0, 5, 7] [4, 0, 7, 0, 0, 5, 0]).trans ((in_context torus1863 [0, 5] [0, 7, 0, 0, 5, 0]).trans ((in_context torus5 [0] [7, 1, 4, 6, 0, 7, 0, 0, 5, 0]).trans (in_context torus1581 [0, 7, 1, 4] [0, 5, 0])))))
  have hr : V [4, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [4, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused21455 : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] = V [5, 1, 3, 0, 5, 0, 7] := by
  have h0 : V [0, 2, 8, 0, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [2, 1, 8, 5, 1, 5, 2, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] :=
    overlap torus2324 focused21454 [2, 1, 8, 5, 1, 5, 2] [1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] (by decide)
  have hl : V [0, 2, 8, 0, 1, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7] = V [5, 1, 3, 0, 5, 0, 7] :=
    ((in_context torus0 [0, 2, 8] [8, 2, 1, 5, 1, 3, 0, 5, 0, 7]).trans ((in_context torus8 [0, 2] [2, 1, 5, 1, 3, 0, 5, 0, 7]).trans ((in_context torus2 [0] [1, 5, 1, 3, 0, 5, 0, 7]).trans (in_context torus0 [] [5, 1, 3, 0, 5, 0, 7]))))
  have hr : V [2, 1, 8, 5, 1, 5, 2, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0] :=
    ((in_context torus3910 [] [2, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0]).trans (in_context torus2 [0, 2, 8, 0, 4] [0, 7, 1, 4, 5, 6, 8, 7, 0, 5, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused21456 : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5] = V [5, 1, 3, 0, 5, 0, 7, 1] := by
  have h0 : V [5, 1, 3, 0, 5, 0, 7, 1] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5] :=
    overlap focused21455 torus0 [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5] [1] (by decide)
  have hl : V [5, 1, 3, 0, 5, 0, 7, 1] = V [5, 1, 3, 0, 5, 0, 7, 1] :=
    rfl
  have hr : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused21457 : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] = V [5, 1, 3, 0, 5, 0, 7, 1, 5] := by
  have h0 : V [5, 1, 3, 0, 5, 0, 7, 1, 5] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] :=
    overlap focused21456 torus5 [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] [5] (by decide)
  have hl : V [5, 1, 3, 0, 5, 0, 7, 1, 5] = V [5, 1, 3, 0, 5, 0, 7, 1, 5] :=
    rfl
  have hr : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused22990 : V [4, 6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [1, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1] := by
  have h0 : V [1, 4, 3, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [3, 4, 3, 0, 5, 0, 2, 8, 4, 5, 1] :=
    overlap torus1455 focused18731 [3, 4] [5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] (by decide)
  have hl : V [1, 4, 3, 5, 0, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [4, 6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2] :=
    ((in_context torus1564 [1] [7, 1, 5, 1, 1, 7, 4, 5, 2]).trans (in_context torus1 [] [4, 6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2]))
  have hr : V [3, 4, 3, 0, 5, 0, 2, 8, 4, 5, 1] = V [1, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1] :=
    ((in_context torus1442 [] [0, 5, 0, 2, 8, 4, 5, 1]).trans (in_context torus1446 [] [0, 5, 0, 2, 8, 4, 5, 1]))
  exact hl.symm.trans (h0.trans hr)

private theorem focused23490 : V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3, 14] = V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1, 14] := by
  have h0 : V [3, 4, 1, 8, 0, 3, 6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [0, 3, 0, 6, 1, 3, 5, 1, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1] :=
    overlap torus8731 focused22990 [0, 3, 0, 6, 1, 3, 5] [6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2] (by decide)
  have hl : V [3, 4, 1, 8, 0, 3, 6, 5, 7, 1, 5, 1, 1, 7, 4, 5, 2] = V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3, 14] :=
    ((in_context torus4343 [3] [5, 7, 1, 5, 1, 1, 7, 4, 5, 2]).trans ((in_context torus13902 [] [5, 7, 1, 5, 1, 1, 7, 4, 5, 2]).trans ((in_context torus65 [0, 3, 2, 0, 5, 1] [7, 1, 5, 1, 1, 7, 4, 5, 2]).trans ((in_context torus77 [0, 3, 2, 0, 5, 1, 2] [1, 5, 1, 1, 7, 4, 5, 2]).trans ((in_context torus92 [0, 3, 2, 0, 5, 1, 2, 4] [5, 1, 1, 7, 4, 5, 2]).trans ((in_context torus65 [0, 3, 2, 0, 5, 1, 2, 4, 1] [1, 1, 7, 4, 5, 2]).trans ((in_context torus92 [0, 3, 2, 0, 5, 1, 2, 4, 1, 2] [1, 7, 4, 5, 2]).trans ((in_context torus14021 [0, 3, 2, 0] [11, 1, 7, 4, 5, 2]).trans ((in_context torus1544 [0, 3] [2, 4, 1, 7, 8, 11, 1, 7, 4, 5, 2]).trans ((in_context torus1541 [0] [3, 2, 4, 1, 7, 8, 11, 1, 7, 4, 5, 2]).trans ((in_context torus1436 [0, 0, 3, 4] [4, 1, 7, 8, 11, 1, 7, 4, 5, 2]).trans ((in_context torus4614 [] [4, 1, 7, 8, 11, 1, 7, 4, 5, 2]).trans ((in_context torus4 [2, 8, 0, 3] [1, 7, 8, 11, 1, 7, 4, 5, 2]).trans ((in_context torus92 [2, 8, 0, 3, 1, 7, 8] [7, 4, 5, 2]).trans ((in_context torus11232 [2] [11, 7, 4, 5, 2]).trans ((in_context torus23 [2, 5, 1, 3, 0, 6, 5] [7, 4, 5, 2]).trans ((in_context torus80 [2, 5, 1, 3, 0, 6, 5] [4, 5, 2]).trans ((in_context torus62 [2, 5, 1, 3, 0, 6, 5, 8] [5, 2]).trans ((in_context torus68 [2, 5, 1, 3, 0, 6, 5, 8, 5] [2]).trans (in_context torus50 [2, 5, 1, 3, 0, 6, 5, 8, 5, 6] []))))))))))))))))))))
  have hr : V [0, 3, 0, 6, 1, 3, 5, 1, 3, 2, 0, 5, 0, 2, 8, 4, 5, 1] = V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1, 14] :=
    ((in_context torus10246 [0, 3, 0] [0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus1550 [0] [3, 5, 1, 2, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus0 [] [3, 2, 4, 3, 5, 1, 2, 3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus4274 [3] [3, 0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus53 [3, 1, 7, 0, 3, 1] [0, 5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus91 [3, 1, 7, 0, 3, 1, 7] [5, 0, 2, 8, 4, 5, 1]).trans ((in_context torus65 [3, 1, 7, 0, 3, 1, 7, 0] [0, 2, 8, 4, 5, 1]).trans ((in_context torus4739 [3, 1, 7] [0, 2, 8, 4, 5, 1]).trans ((in_context torus97 [3, 1, 7, 6, 0, 2, 7, 8] [2, 8, 4, 5, 1]).trans ((in_context torus1490 [3, 1, 7, 6, 0, 2] [14, 2, 8, 4, 5, 1]).trans ((in_context torus1590 [3, 1, 7, 6, 0] [14, 2, 8, 4, 5, 1]).trans ((in_context torus50 [3, 1, 7, 6, 0, 0, 2, 3, 8] [8, 4, 5, 1]).trans ((in_context torus86 [3, 1, 7, 6, 0, 0, 2, 3, 8, 3] [4, 5, 1]).trans ((in_context torus4611 [3, 1, 7, 6] [14, 4, 5, 1]).trans ((in_context torus4140 [3] [8, 0, 14, 4, 5, 1]).trans ((in_context torus1543 [] [7, 0, 8, 8, 0, 14, 4, 5, 1]).trans ((in_context torus8 [2, 1, 2, 1, 7, 0] [0, 14, 4, 5, 1]).trans ((in_context torus62 [2, 1, 2, 1, 7, 0, 0] [5, 1]).trans ((in_context torus68 [2, 1, 2, 1, 7, 0, 0, 5] [1]).trans ((in_context torus1905 [2, 1, 2, 1] [14, 1]).trans (in_context torus98 [2, 1, 2, 1, 6, 1, 7, 5, 1] [])))))))))))))))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem focused23491 : V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1] := by
  have h0 : V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1, 14, 9] = V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3] :=
    overlap focused23490 torus39 [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3] [9] (by decide)
  have hl : V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1, 14, 9] = V [2, 1, 2, 1, 6, 1, 7, 5, 1, 1] :=
    (in_context torus39 [2, 1, 2, 1, 6, 1, 7, 5, 1, 1] [])
  have hr : V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [2, 5, 1, 3, 0, 6, 5, 8, 5, 6, 3] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23492 : V [5, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [1, 2, 1, 6, 1, 7, 5, 1, 1] := by
  have h0 : V [5, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [2, 2, 1, 2, 1, 6, 1, 7, 5, 1, 1] :=
    overlap torus2 focused23491 [2] [5, 1, 3, 0, 6, 5, 8, 5, 6, 3] (by decide)
  have hl : V [5, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [5, 1, 3, 0, 6, 5, 8, 5, 6, 3] :=
    rfl
  have hr : V [2, 2, 1, 2, 1, 6, 1, 7, 5, 1, 1] = V [1, 2, 1, 6, 1, 7, 5, 1, 1] :=
    (in_context torus2 [] [1, 2, 1, 6, 1, 7, 5, 1, 1])
  exact hl.symm.trans (h0.trans hr)

private theorem focused23493 : V [0, 5, 1, 2, 1, 6, 1, 7, 5, 1, 1] = V [3, 0, 6, 5, 8, 5, 6, 3] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [5, 4, 5, 6, 1, 2, 1, 6, 1, 7, 5, 1, 1] :=
    overlap torus108 focused23492 [5, 4, 5, 6] [1, 3, 0, 6, 5, 8, 5, 6, 3] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 6, 5, 8, 5, 6, 3] = V [3, 0, 6, 5, 8, 5, 6, 3] :=
    ((in_context torus143 [] [1, 3, 0, 6, 5, 8, 5, 6, 3]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 6, 5, 8, 5, 6, 3]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 6, 5, 8, 5, 6, 3]).trans ((in_context torus2 [0] [1, 3, 0, 6, 5, 8, 5, 6, 3]).trans (in_context torus0 [] [3, 0, 6, 5, 8, 5, 6, 3])))))
  have hr : V [5, 4, 5, 6, 1, 2, 1, 6, 1, 7, 5, 1, 1] = V [0, 5, 1, 2, 1, 6, 1, 7, 5, 1, 1] :=
    ((in_context torus1457 [] [6, 1, 2, 1, 6, 1, 7, 5, 1, 1]).trans (in_context torus6 [0, 5] [1, 2, 1, 6, 1, 7, 5, 1, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23496 : V [1, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [5, 1, 3, 0, 6, 5, 8, 5, 6] := by
  have h0 : V [1, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [5, 1, 3, 0, 6, 5, 8, 5, 6] :=
    overlap focused23492 torus3 [5, 1, 3, 0, 6, 5, 8, 5, 6] [3] (by decide)
  have hl : V [1, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [1, 2, 1, 6, 1, 7, 5, 1, 1, 3] :=
    rfl
  have hr : V [5, 1, 3, 0, 6, 5, 8, 5, 6] = V [5, 1, 3, 0, 6, 5, 8, 5, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused23497 : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5, 6] = V [1, 7, 5, 1, 1, 3] := by
  have h0 : V [6, 0, 2, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2, 5, 1, 3, 0, 6, 5, 8, 5, 6] :=
    overlap torus5232 focused23496 [0, 2, 7, 1, 2, 8, 4, 1, 8, 2] [2, 1, 6, 1, 7, 5, 1, 1, 3] (by decide)
  have hl : V [6, 0, 2, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [1, 7, 5, 1, 1, 3] :=
    ((in_context torus2 [6, 0] [1, 6, 1, 7, 5, 1, 1, 3]).trans ((in_context torus0 [6] [6, 1, 7, 5, 1, 1, 3]).trans (in_context torus6 [] [1, 7, 5, 1, 1, 3])))
  have hr : V [0, 2, 7, 1, 2, 8, 4, 1, 8, 2, 5, 1, 3, 0, 6, 5, 8, 5, 6] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5, 6] :=
    (in_context torus5404 [] [5, 1, 3, 0, 6, 5, 8, 5, 6])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23498 : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5] = V [1, 7, 5, 1, 1, 3, 6] := by
  have h0 : V [1, 7, 5, 1, 1, 3, 6] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5] :=
    overlap focused23497 torus6 [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5] [6] (by decide)
  have hl : V [1, 7, 5, 1, 1, 3, 6] = V [1, 7, 5, 1, 1, 3, 6] :=
    rfl
  have hr : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23499 : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8] = V [1, 7, 5, 1, 1, 3, 6, 5] := by
  have h0 : V [1, 7, 5, 1, 1, 3, 6, 5] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8] :=
    overlap focused23498 torus5 [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8] [5] (by decide)
  have hl : V [1, 7, 5, 1, 1, 3, 6, 5] = V [1, 7, 5, 1, 1, 3, 6, 5] :=
    rfl
  have hr : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5, 8] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23501 : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5] = V [1, 7, 5, 1, 1, 3, 6, 5, 8] := by
  have h0 : V [1, 7, 5, 1, 1, 3, 6, 5, 8] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5] :=
    overlap focused23499 torus8 [6, 0, 2, 0, 5, 1, 3, 0, 6, 5] [8] (by decide)
  have hl : V [1, 7, 5, 1, 1, 3, 6, 5, 8] = V [1, 7, 5, 1, 1, 3, 6, 5, 8] :=
    rfl
  have hr : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5] = V [6, 0, 2, 0, 5, 1, 3, 0, 6, 5] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23506 : V [3, 0, 6, 5, 8, 5, 6, 3, 0, 5] = V [0, 5, 1, 2, 1, 7, 0, 5, 4] := by
  have h0 : V [3, 0, 6, 5, 8, 5, 6, 3, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [0, 5, 1, 2, 1, 6, 1, 7, 5, 1, 5] :=
    overlap focused23493 focused18748 [0, 5, 1, 2, 1, 6, 1, 7, 5, 1] [1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] (by decide)
  have hl : V [3, 0, 6, 5, 8, 5, 6, 3, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 0, 5, 0, 7, 1] = V [3, 0, 6, 5, 8, 5, 6, 3, 0, 5] :=
    ((in_context focused18762 [3, 0, 6, 5, 8, 5, 6, 3] [5, 1, 3, 0, 5, 0, 7, 1]).trans ((in_context torus5 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7, 1, 5, 1, 3, 0] [1, 3, 0, 5, 0, 7, 1]).trans ((in_context torus0 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7, 1, 5, 1, 3] [3, 0, 5, 0, 7, 1]).trans ((in_context torus3 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7, 1, 5, 1] [0, 5, 0, 7, 1]).trans ((in_context torus1 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7, 1, 5] [5, 0, 7, 1]).trans ((in_context torus5 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7, 1] [0, 7, 1]).trans ((in_context torus1 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0, 7] [7, 1]).trans ((in_context torus7 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5, 0] [1]).trans (in_context torus0 [3, 0, 6, 5, 8, 5, 6, 3, 0, 5] [])))))))))
  have hr : V [0, 5, 1, 2, 1, 6, 1, 7, 5, 1, 5] = V [0, 5, 1, 2, 1, 7, 0, 5, 4] :=
    ((in_context torus1576 [0, 5, 1, 2, 1, 6, 1] []).trans (in_context torus1538 [0, 5, 1, 2, 1] [4]))
  exact hl.symm.trans (h0.trans hr)

private theorem focused23507 : V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 6] = V [0, 5, 1, 2, 1, 7, 0] := by
  have h0 : V [0, 5, 1, 2, 1, 7, 0, 5, 4, 4, 5] = V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 6] :=
    overlap focused23506 torus1457 [3, 0, 6, 5, 8, 5, 6, 3, 0] [4, 5] (by decide)
  have hl : V [0, 5, 1, 2, 1, 7, 0, 5, 4, 4, 5] = V [0, 5, 1, 2, 1, 7, 0] :=
    ((in_context torus4 [0, 5, 1, 2, 1, 7, 0, 5] [5]).trans (in_context torus5 [0, 5, 1, 2, 1, 7, 0] []))
  have hr : V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 6] = V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23508 : V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] = V [0, 5, 1, 2, 1, 6] := by
  have h0 : V [0, 5, 1, 2, 1, 7, 0, 7, 8, 7] = V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] :=
    overlap focused23507 torus1477 [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5] [7, 8, 7] (by decide)
  have hl : V [0, 5, 1, 2, 1, 7, 0, 7, 8, 7] = V [0, 5, 1, 2, 1, 6] :=
    ((in_context torus1476 [0, 5, 1, 2, 1] [8, 7]).trans ((in_context torus8 [0, 5, 1, 2, 1, 6, 7] [7]).trans (in_context torus7 [0, 5, 1, 2, 1, 6] [])))
  have hr : V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] = V [3, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23531 : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 5] = V [6, 0, 2, 0, 5, 1, 3, 0, 6] := by
  have h0 : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 5] = V [6, 0, 2, 0, 5, 1, 3, 0, 6] :=
    overlap focused23501 torus5 [6, 0, 2, 0, 5, 1, 3, 0, 6] [5] (by decide)
  have hl : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 5] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 5] :=
    rfl
  have hr : V [6, 0, 2, 0, 5, 1, 3, 0, 6] = V [6, 0, 2, 0, 5, 1, 3, 0, 6] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused23535 : V [5, 8, 5, 6, 3, 0, 0, 5, 7, 0] = V [6, 1, 3, 0, 5, 1, 2, 1, 6] := by
  have h0 : V [7, 6, 5, 6, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] = V [6, 3, 4, 3, 2, 0, 5, 1, 2, 1, 6] :=
    overlap torus122 focused23508 [6, 3, 4, 3, 2] [0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] (by decide)
  have hl : V [7, 6, 5, 6, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0] = V [5, 8, 5, 6, 3, 0, 0, 5, 7, 0] :=
    ((in_context torus1471 [] [6, 0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0]).trans ((in_context torus6 [6, 1] [0, 6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0]).trans ((in_context torus1 [6] [6, 5, 8, 5, 6, 3, 0, 0, 5, 7, 0]).trans (in_context torus6 [] [5, 8, 5, 6, 3, 0, 0, 5, 7, 0]))))
  have hr : V [6, 3, 4, 3, 2, 0, 5, 1, 2, 1, 6] = V [6, 1, 3, 0, 5, 1, 2, 1, 6] :=
    ((in_context torus1442 [6] [2, 0, 5, 1, 2, 1, 6]).trans ((in_context torus1446 [6] [2, 0, 5, 1, 2, 1, 6]).trans (in_context torus2 [6, 1, 3] [0, 5, 1, 2, 1, 6])))
  exact hl.symm.trans (h0.trans hr)

private theorem focused23536 : V [5, 6, 1, 3, 0, 5, 1, 2, 1, 6] = V [8, 5, 6, 3, 0, 0, 5, 7, 0] := by
  have h0 : V [8, 5, 6, 3, 0, 0, 5, 7, 0] = V [5, 6, 1, 3, 0, 5, 1, 2, 1, 6] :=
    overlap torus5 focused23535 [5] [8, 5, 6, 3, 0, 0, 5, 7, 0] (by decide)
  have hl : V [8, 5, 6, 3, 0, 0, 5, 7, 0] = V [8, 5, 6, 3, 0, 0, 5, 7, 0] :=
    rfl
  have hr : V [5, 6, 1, 3, 0, 5, 1, 2, 1, 6] = V [5, 6, 1, 3, 0, 5, 1, 2, 1, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23548 : V [8, 5, 6, 3, 0, 0, 5, 6, 1, 7] = V [5, 6, 1, 3, 0, 5, 1, 2, 1] := by
  have h0 : V [8, 5, 6, 3, 0, 0, 5, 7, 0, 6] = V [5, 6, 1, 3, 0, 5, 1, 2, 1] :=
    overlap focused23536 torus6 [5, 6, 1, 3, 0, 5, 1, 2, 1] [6] (by decide)
  have hl : V [8, 5, 6, 3, 0, 0, 5, 7, 0, 6] = V [8, 5, 6, 3, 0, 0, 5, 6, 1, 7] :=
    (in_context torus1505 [8, 5, 6, 3, 0, 0, 5] [])
  have hr : V [5, 6, 1, 3, 0, 5, 1, 2, 1] = V [5, 6, 1, 3, 0, 5, 1, 2, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused23549 : V [8, 5, 6, 1, 3, 0, 5, 1, 2, 1] = V [5, 6, 3, 0, 0, 5, 6, 1, 7] := by
  have h0 : V [5, 6, 3, 0, 0, 5, 6, 1, 7] = V [8, 5, 6, 1, 3, 0, 5, 1, 2, 1] :=
    overlap torus8 focused23548 [8] [5, 6, 3, 0, 0, 5, 6, 1, 7] (by decide)
  have hl : V [5, 6, 3, 0, 0, 5, 6, 1, 7] = V [5, 6, 3, 0, 0, 5, 6, 1, 7] :=
    rfl
  have hr : V [8, 5, 6, 1, 3, 0, 5, 1, 2, 1] = V [8, 5, 6, 1, 3, 0, 5, 1, 2, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23560 : V [5, 6, 3, 0, 0, 5, 6, 1, 7, 0] = V [8, 5, 6, 1, 3, 0, 5, 1, 2] := by
  have h0 : V [5, 6, 3, 0, 0, 5, 6, 1, 7, 0] = V [8, 5, 6, 1, 3, 0, 5, 1, 2] :=
    overlap focused23549 torus1 [8, 5, 6, 1, 3, 0, 5, 1, 2] [0] (by decide)
  have hl : V [5, 6, 3, 0, 0, 5, 6, 1, 7, 0] = V [5, 6, 3, 0, 0, 5, 6, 1, 7, 0] :=
    rfl
  have hr : V [8, 5, 6, 1, 3, 0, 5, 1, 2] = V [8, 5, 6, 1, 3, 0, 5, 1, 2] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused23561 : V [5, 8, 5, 6, 1, 3, 0, 5, 1, 2] = V [6, 3, 0, 0, 5, 6, 1, 7, 0] := by
  have h0 : V [6, 3, 0, 0, 5, 6, 1, 7, 0] = V [5, 8, 5, 6, 1, 3, 0, 5, 1, 2] :=
    overlap torus5 focused23560 [5] [6, 3, 0, 0, 5, 6, 1, 7, 0] (by decide)
  have hl : V [6, 3, 0, 0, 5, 6, 1, 7, 0] = V [6, 3, 0, 0, 5, 6, 1, 7, 0] :=
    rfl
  have hr : V [5, 8, 5, 6, 1, 3, 0, 5, 1, 2] = V [5, 8, 5, 6, 1, 3, 0, 5, 1, 2] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23567 : V [6, 3, 0, 0, 5, 6, 1, 7, 0, 2] = V [5, 8, 5, 6, 1, 3, 0, 5, 1] := by
  have h0 : V [6, 3, 0, 0, 5, 6, 1, 7, 0, 2] = V [5, 8, 5, 6, 1, 3, 0, 5, 1] :=
    overlap focused23561 torus2 [5, 8, 5, 6, 1, 3, 0, 5, 1] [2] (by decide)
  have hl : V [6, 3, 0, 0, 5, 6, 1, 7, 0, 2] = V [6, 3, 0, 0, 5, 6, 1, 7, 0, 2] :=
    rfl
  have hr : V [5, 8, 5, 6, 1, 3, 0, 5, 1] = V [5, 8, 5, 6, 1, 3, 0, 5, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem focused23572 : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 6] = V [6, 0, 2, 6, 5] := by
  have h0 : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 6, 1, 3, 0, 6, 0] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 6] :=
    overlap focused23531 torus14147 [1, 7, 5, 1, 1, 3, 6, 5, 8] [6, 1, 3, 0, 6, 0] (by decide)
  have hl : V [6, 0, 2, 0, 5, 1, 3, 0, 6, 6, 1, 3, 0, 6, 0] = V [6, 0, 2, 6, 5] :=
    ((in_context torus6 [6, 0, 2, 0, 5, 1, 3, 0] [1, 3, 0, 6, 0]).trans ((in_context torus0 [6, 0, 2, 0, 5, 1, 3] [3, 0, 6, 0]).trans ((in_context torus3 [6, 0, 2, 0, 5, 1] [0, 6, 0]).trans ((in_context torus1 [6, 0, 2, 0, 5] [6, 0]).trans (in_context torus1465 [6, 0, 2] [])))))
  have hr : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 6] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 6] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23573 : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 1, 5, 4, 6] = V [6, 0, 2] := by
  have h0 : V [6, 0, 2, 6, 5, 5, 6] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 0, 6, 7] :=
    overlap focused23572 torus1466 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5] [5, 6] (by decide)
  have hl : V [6, 0, 2, 6, 5, 5, 6] = V [6, 0, 2] :=
    ((in_context torus5 [6, 0, 2, 6] [6]).trans (in_context torus6 [6, 0, 2] []))
  have hr : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 5, 0, 6, 7] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 1, 5, 4, 6] :=
    (in_context torus1566 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem focused23583 : V [1, 7, 5, 1, 1, 3, 6, 5, 7, 1, 8, 5, 6, 4, 0, 6] = V [6, 0, 2, 5, 0] := by
  have h0 : V [6, 0, 2, 5, 0] = V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 0, 6, 7, 5, 7, 6] :=
    overlap focused23573 torus3485 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1] [5, 0] (by decide)
  have hl : V [6, 0, 2, 5, 0] = V [6, 0, 2, 5, 0] :=
    rfl
  have hr : V [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8, 1, 0, 6, 7, 5, 7, 6] = V [1, 7, 5, 1, 1, 3, 6, 5, 7, 1, 8, 5, 6, 4, 0, 6] :=
    ((in_context torus1 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 5, 0, 8] [6, 7, 5, 7, 6]).trans ((in_context torus4420 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0] [7, 6]).trans ((in_context torus78 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 0, 2, 1, 6, 0] [6]).trans ((in_context torus4492 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0, 0] [6]).trans ((in_context torus0 [1, 7, 5, 1, 1, 3, 6, 5, 8, 0] [7, 5, 6, 4, 0, 6]).trans (in_context torus1506 [1, 7, 5, 1, 1, 3, 6, 5] [5, 6, 4, 0, 6]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic25074 : V [0, 6, 1, 4, 6, 5, 7, 1, 8, 5, 6] = V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3] := by
  have hloop : V [0, 0, 5, 7, 0, 6, 0, 2, 5, 0, 6, 1, 4, 6, 5, 8, 0, 7, 5, 6, 3] = 1 :=
    relation_split _ (equation_loop focused23583) true 16 _ [] (by decide)
  have h0 : V [0, 6, 1, 4, 6, 5, 8, 0, 7, 5, 6] = V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3] :=
    relation_split _ hloop false 9 _ _ (by decide)
  have hl : V [0, 6, 1, 4, 6, 5, 8, 0, 7, 5, 6] = V [0, 6, 1, 4, 6, 5, 7, 1, 8, 5, 6] :=
    (in_context torus1506 [0, 6, 1, 4, 6, 5] [5, 6])
  have hr : V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3] = V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

private theorem cyclic27563 : V [0, 6, 1, 4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1] = V [5] := by
  have h0 : V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3, 3, 0, 0, 5, 6, 1, 7, 0, 2] = V [0, 6, 1, 4, 6, 5, 7, 1, 8, 5, 5, 8, 5, 6, 1, 3, 0, 5, 1] :=
    overlap cyclic25074 focused23567 [0, 6, 1, 4, 6, 5, 7, 1, 8, 5] [3, 0, 0, 5, 6, 1, 7, 0, 2] (by decide)
  have hl : V [5, 2, 1, 6, 1, 7, 5, 1, 1, 3, 3, 0, 0, 5, 6, 1, 7, 0, 2] = V [5] :=
    ((in_context torus3 [5, 2, 1, 6, 1, 7, 5, 1, 1] [0, 0, 5, 6, 1, 7, 0, 2]).trans ((in_context torus1 [5, 2, 1, 6, 1, 7, 5, 1] [0, 5, 6, 1, 7, 0, 2]).trans ((in_context torus1 [5, 2, 1, 6, 1, 7, 5] [5, 6, 1, 7, 0, 2]).trans ((in_context torus5 [5, 2, 1, 6, 1, 7] [6, 1, 7, 0, 2]).trans ((in_context torus1510 [5, 2, 1] [1, 7, 0, 2]).trans ((in_context torus0 [5, 2, 1, 7] [7, 0, 2]).trans ((in_context torus7 [5, 2, 1] [0, 2]).trans ((in_context torus1 [5, 2] [2]).trans (in_context torus2 [5] [])))))))))
  have hr : V [0, 6, 1, 4, 6, 5, 7, 1, 8, 5, 5, 8, 5, 6, 1, 3, 0, 5, 1] = V [0, 6, 1, 4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1] :=
    ((in_context torus5 [0, 6, 1, 4, 6, 5, 7, 1, 8] [8, 5, 6, 1, 3, 0, 5, 1]).trans (in_context torus8 [0, 6, 1, 4, 6, 5, 7, 1] [5, 6, 1, 3, 0, 5, 1]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27564 : V [7, 8, 1, 6, 1, 3, 0, 5, 1] = V [5, 6, 3, 0, 6] := by
  have h0 : V [1, 7, 5, 0, 8, 1, 5, 6, 1, 4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1] = V [5, 6, 3, 0, 6, 5, 5] :=
    overlap torus11227 cyclic27563 [5, 6, 3, 0, 6, 5] [6, 1, 4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1] (by decide)
  have hl : V [1, 7, 5, 0, 8, 1, 5, 6, 1, 4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1] = V [7, 8, 1, 6, 1, 3, 0, 5, 1] :=
    ((in_context torus12584 [1, 7] [4, 6, 5, 7, 1, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus13511 [1, 7, 1, 5] [5, 7, 1, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus2338 [1, 7, 1, 5, 0, 6] [5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus1566 [1, 7, 1] [5, 6, 4, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus10979 [1] [6, 4, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus1 [] [7, 8, 1, 5, 4, 6, 6, 4, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus6 [7, 8, 1, 5, 4] [4, 5, 6, 1, 3, 0, 5, 1]).trans ((in_context torus4 [7, 8, 1, 5] [5, 6, 1, 3, 0, 5, 1]).trans (in_context torus5 [7, 8, 1] [6, 1, 3, 0, 5, 1])))))))))
  have hr : V [5, 6, 3, 0, 6, 5, 5] = V [5, 6, 3, 0, 6] :=
    (in_context torus5 [5, 6, 3, 0, 6] [])
  exact hl.symm.trans (h0.trans hr)

private theorem cyclic27565 : V [5, 1, 3, 0, 5, 1] = V [0, 7, 1, 5, 0, 12] := by
  have h0 : V [1, 6, 5, 8, 8, 1, 6, 1, 3, 0, 5, 1] = V [0, 7, 8, 1, 6, 5, 0, 5, 6, 3, 0, 6] :=
    overlap torus2429 cyclic27564 [0, 7, 8, 1, 6, 5, 0] [8, 1, 6, 1, 3, 0, 5, 1] (by decide)
  have hl : V [1, 6, 5, 8, 8, 1, 6, 1, 3, 0, 5, 1] = V [5, 1, 3, 0, 5, 1] :=
    ((in_context torus8 [1, 6, 5] [1, 6, 1, 3, 0, 5, 1]).trans ((in_context torus1461 [1] [6, 1, 3, 0, 5, 1]).trans ((in_context torus1 [] [5, 6, 6, 1, 3, 0, 5, 1]).trans (in_context torus6 [5] [1, 3, 0, 5, 1]))))
  have hr : V [0, 7, 8, 1, 6, 5, 0, 5, 6, 3, 0, 6] = V [0, 7, 1, 5, 0, 12] :=
    ((in_context torus4244 [0] [5, 6, 3, 0, 6]).trans ((in_context torus0 [] [1, 6, 5, 8, 7, 5, 6, 3, 0, 6]).trans ((in_context torus1610 [1, 6, 5] [3, 0, 6]).trans ((in_context torus4135 [] [1, 3, 0, 6]).trans ((in_context torus1596 [0, 7, 8] [3, 0, 6]).trans ((in_context torus4421 [0, 7] [0, 6]).trans ((in_context torus93 [0, 7, 1, 5, 0, 2, 1] [6]).trans ((in_context torus1 [0, 7, 1, 5, 0, 2] [12, 6]).trans ((in_context torus72 [0, 7, 1, 5, 0, 2] []).trans (in_context torus2 [0, 7, 1, 5, 0] [12]))))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem cyclic27566 : V [0, 5, 0, 7, 1, 5, 0, 12] = V [3, 0, 5, 1] := by
  have h0 : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 1] = V [5, 4, 5, 6, 0, 7, 1, 5, 0, 12] :=
    overlap torus108 cyclic27565 [5, 4, 5, 6] [1, 3, 0, 5, 1] (by decide)
  have hl : V [3, 2, 3, 4, 3, 1, 3, 0, 5, 1] = V [3, 0, 5, 1] :=
    ((in_context torus143 [] [1, 3, 0, 5, 1]).trans ((in_context torus1428 [] [3, 2, 1, 3, 0, 5, 1]).trans ((in_context torus3 [0, 2] [2, 1, 3, 0, 5, 1]).trans ((in_context torus2 [0] [1, 3, 0, 5, 1]).trans (in_context torus0 [] [3, 0, 5, 1])))))
  have hr : V [5, 4, 5, 6, 0, 7, 1, 5, 0, 12] = V [0, 5, 0, 7, 1, 5, 0, 12] :=
    ((in_context torus1457 [] [6, 0, 7, 1, 5, 0, 12]).trans (in_context torus6 [0, 5] [0, 7, 1, 5, 0, 12]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27567 : V [0, 5, 0, 7, 1, 5, 0, 0, 12] = V [3, 0, 5] := by
  have h0 : V [3, 0, 5, 1, 0] = V [0, 5, 0, 7, 1, 5, 0, 0, 12] :=
    overlap cyclic27566 torus93 [0, 5, 0, 7, 1, 5, 0] [0] (by decide)
  have hl : V [3, 0, 5, 1, 0] = V [3, 0, 5] :=
    (in_context torus1 [3, 0, 5] [])
  have hr : V [0, 5, 0, 7, 1, 5, 0, 0, 12] = V [0, 5, 0, 7, 1, 5, 0, 0, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27568 : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 12] = V [3, 0] := by
  have h0 : V [3, 0, 5, 5] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 12] :=
    overlap cyclic27567 torus66 [0, 5, 0, 7, 1, 5, 0, 0] [5] (by decide)
  have hl : V [3, 0, 5, 5] = V [3, 0] :=
    (in_context torus5 [3, 0] [])
  have hr : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 12] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27569 : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1, 12] = V [3] := by
  have h0 : V [3, 0, 1] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1, 12] :=
    overlap cyclic27568 torus94 [0, 5, 0, 7, 1, 5, 0, 0, 8] [1] (by decide)
  have hl : V [3, 0, 1] = V [3] :=
    (in_context torus0 [3] [])
  have hr : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1, 12] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1, 12] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27572 : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1] = V [3, 11] := by
  have h0 : V [3, 11] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1] :=
    overlap cyclic27569 torus29 [0, 5, 0, 7, 1, 5, 0, 0, 8, 1] [11] (by decide)
  have hl : V [3, 11] = V [3, 11] :=
    rfl
  have hr : V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1] = V [0, 5, 0, 7, 1, 5, 0, 0, 8, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27573 : V [5, 0, 7, 1, 5, 1, 3, 0, 5] = V [0, 0, 12] := by
  have h0 : V [5, 0, 7, 1, 5, 5, 0, 7, 1, 5, 0, 0, 12] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 3, 0, 5] :=
    overlap focused18752 cyclic27567 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3] [5, 0, 7, 1, 5, 0, 0, 12] (by decide)
  have hl : V [5, 0, 7, 1, 5, 5, 0, 7, 1, 5, 0, 0, 12] = V [0, 0, 12] :=
    ((in_context torus5 [5, 0, 7, 1] [0, 7, 1, 5, 0, 0, 12]).trans ((in_context torus1 [5, 0, 7] [7, 1, 5, 0, 0, 12]).trans ((in_context torus7 [5, 0] [1, 5, 0, 0, 12]).trans ((in_context torus0 [5] [5, 0, 0, 12]).trans (in_context torus5 [] [0, 0, 12])))))
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 3, 0, 5] = V [5, 0, 7, 1, 5, 1, 3, 0, 5] :=
    (in_context focused18753 [] [3, 0, 5])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27575 : V [5, 0, 0, 8, 2, 1, 5, 0, 2] = V [0, 0, 8] := by
  have h0 : V [0, 0, 12, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [5, 0, 7, 1, 5, 1, 3, 0, 11] :=
    overlap cyclic27573 torus2351 [5, 0, 7, 1, 5, 1, 3, 0] [1, 2, 0, 6, 1, 3, 0, 5, 7, 6] (by decide)
  have hl : V [0, 0, 12, 1, 2, 0, 6, 1, 3, 0, 5, 7, 6] = V [0, 0, 8] :=
    ((in_context torus94 [0, 0] [2, 0, 6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus0 [0] [12, 2, 0, 6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus48 [0] [0, 6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus93 [0, 5] [6, 1, 3, 0, 5, 7, 6]).trans ((in_context torus72 [0, 5, 0] [1, 3, 0, 5, 7, 6]).trans ((in_context torus94 [0, 5, 0, 2] [3, 0, 5, 7, 6]).trans ((in_context torus54 [0, 5, 0, 2, 1] [0, 5, 7, 6]).trans ((in_context torus4435 [0] [0, 5, 7, 6]).trans ((in_context torus1464 [0, 0, 8, 1, 6] [5, 7, 6]).trans ((in_context torus1569 [0, 0, 8, 1] [5, 7, 6]).trans ((in_context torus1 [0, 0, 8] [6, 7, 5, 5, 7, 6]).trans ((in_context torus5 [0, 0, 8, 6, 7] [7, 6]).trans ((in_context torus7 [0, 0, 8, 6] [6]).trans (in_context torus6 [0, 0, 8] []))))))))))))))
  have hr : V [5, 0, 7, 1, 5, 1, 3, 0, 11] = V [5, 0, 0, 8, 2, 1, 5, 0, 2] :=
    (in_context torus12178 [5, 0] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27576 : V [5, 0, 0, 8, 1, 6, 0, 8, 0, 3, 12] = V [0] := by
  have h0 : V [0, 0, 8, 8, 1] = V [5, 0, 0, 8, 2, 1, 5, 0, 0, 8, 2] :=
    overlap cyclic27575 torus1488 [5, 0, 0, 8, 2, 1, 5, 0] [8, 1] (by decide)
  have hl : V [0, 0, 8, 8, 1] = V [0] :=
    ((in_context torus8 [0, 0] [1]).trans (in_context torus0 [0] []))
  have hr : V [5, 0, 0, 8, 2, 1, 5, 0, 0, 8, 2] = V [5, 0, 0, 8, 1, 6, 0, 8, 0, 3, 12] :=
    (in_context torus13922 [5, 0, 0, 8] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27584 : V [5, 1, 3, 0, 5, 0, 7, 1, 5, 0] = V [1, 11] := by
  have h0 : V [5, 1, 3, 0, 5, 0, 7, 1, 0, 0, 8, 1, 6, 0, 8, 0, 3, 12] = V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 0] :=
    overlap focused21456 cyclic27576 [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0] [0, 0, 8, 1, 6, 0, 8, 0, 3, 12] (by decide)
  have hl : V [5, 1, 3, 0, 5, 0, 7, 1, 0, 0, 8, 1, 6, 0, 8, 0, 3, 12] = V [1, 11] :=
    ((in_context torus1 [5, 1, 3, 0, 5, 0, 7] [0, 8, 1, 6, 0, 8, 0, 3, 12]).trans ((in_context torus13083 [5, 1] [1, 6, 0, 8, 0, 3, 12]).trans ((in_context torus1 [5] [6, 1, 2, 0, 6, 11, 1, 6, 0, 8, 0, 3, 12]).trans ((in_context torus92 [5, 6, 1, 2, 0, 6] [6, 0, 8, 0, 3, 12]).trans ((in_context torus14302 [] [11, 6, 0, 8, 0, 3, 12]).trans ((in_context torus23 [1, 4, 1, 2, 1, 7] [6, 0, 8, 0, 3, 12]).trans ((in_context torus74 [1, 4, 1, 2, 1, 7] [0, 8, 0, 3, 12]).trans ((in_context torus7 [1, 4, 1, 2, 1] [14, 0, 8, 0, 3, 12]).trans ((in_context torus97 [1, 4, 1, 2, 1] [8, 0, 3, 12]).trans ((in_context torus1 [1, 4, 1, 2] [14, 8, 0, 3, 12]).trans ((in_context torus86 [1, 4, 1, 2] [0, 3, 12]).trans ((in_context torus2 [1, 4, 1] [14, 0, 3, 12]).trans ((in_context torus97 [1, 4, 1] [3, 12]).trans ((in_context torus1 [1, 4] [14, 3, 12]).trans ((in_context torus56 [1, 4] [12]).trans ((in_context torus4 [1] [14, 12]).trans (in_context torus42 [1] [])))))))))))))))))
  have hr : V [0, 2, 8, 0, 4, 0, 7, 1, 4, 5, 6, 8, 7, 0, 0] = V [5, 1, 3, 0, 5, 0, 7, 1, 5, 0] :=
    (in_context focused21457 [] [0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27593 : V [5, 1, 1, 2, 8, 0, 5, 1, 8] = V [1, 1, 2] := by
  have h0 : V [1, 11, 8, 1, 4, 0, 7, 1, 5, 3, 4] = V [5, 1, 3, 0, 5, 0, 7, 1, 12] :=
    overlap cyclic27584 torus2189 [5, 1, 3, 0, 5, 0, 7, 1] [8, 1, 4, 0, 7, 1, 5, 3, 4] (by decide)
  have hl : V [1, 11, 8, 1, 4, 0, 7, 1, 5, 3, 4] = V [1, 1, 2] :=
    ((in_context torus83 [1] [1, 4, 0, 7, 1, 5, 3, 4]).trans ((in_context torus92 [1, 5] [4, 0, 7, 1, 5, 3, 4]).trans ((in_context torus59 [1, 5, 1] [0, 7, 1, 5, 3, 4]).trans ((in_context torus91 [1, 5, 1, 8] [7, 1, 5, 3, 4]).trans ((in_context torus77 [1, 5, 1, 8, 0] [1, 5, 3, 4]).trans ((in_context torus4352 [1] [1, 5, 3, 4]).trans ((in_context torus1461 [1, 1, 2, 0, 4] [5, 3, 4]).trans ((in_context torus1561 [1, 1, 2, 0] [5, 3, 4]).trans ((in_context torus0 [1, 1, 2] [4, 3, 5, 5, 3, 4]).trans ((in_context torus5 [1, 1, 2, 4, 3] [3, 4]).trans ((in_context torus3 [1, 1, 2, 4] [4]).trans (in_context torus4 [1, 1, 2] []))))))))))))
  have hr : V [5, 1, 3, 0, 5, 0, 7, 1, 12] = V [5, 1, 1, 2, 8, 0, 5, 1, 8] :=
    (in_context torus13581 [5, 1] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27594 : V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 11] = V [1] := by
  have h0 : V [1, 1, 2, 2, 0] = V [5, 1, 1, 2, 8, 0, 5, 1, 2, 3, 2] :=
    overlap cyclic27593 torus1430 [5, 1, 1, 2, 8, 0, 5, 1] [2, 0] (by decide)
  have hl : V [1, 1, 2, 2, 0] = V [1] :=
    ((in_context torus2 [1, 1] [0]).trans (in_context torus1 [1] []))
  have hr : V [5, 1, 1, 2, 8, 0, 5, 1, 2, 3, 2] = V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 11] :=
    ((in_context torus1436 [5, 1, 1, 2, 8, 0, 5, 1] []).trans (in_context torus13024 [5, 1, 1, 2] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27595 : V [5, 1, 1, 2, 0, 0, 5, 6, 1, 2, 0, 6] = V [] := by
  have h0 : V [1, 0] = V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 0, 11] :=
    overlap cyclic27594 torus91 [5, 1, 1, 2, 0, 4, 1, 2, 1, 7] [0] (by decide)
  have hl : V [1, 0] = V [] :=
    (in_context torus1 [] [])
  have hr : V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 0, 11] = V [5, 1, 1, 2, 0, 0, 5, 6, 1, 2, 0, 6] :=
    (in_context torus14207 [5, 1, 1, 2, 0] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27597 : V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 0] = V [12] := by
  have h0 : V [12] = V [5, 1, 1, 2, 0, 0, 1, 4, 1, 2, 1, 7, 0] :=
    overlap cyclic27595 torus14156 [5, 1, 1, 2, 0, 0] [12] (by decide)
  have hl : V [12] = V [12] :=
    rfl
  have hr : V [5, 1, 1, 2, 0, 0, 1, 4, 1, 2, 1, 7, 0] = V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 0] :=
    (in_context torus0 [5, 1, 1, 2, 0] [4, 1, 2, 1, 7, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27609 : V [5, 0, 7, 1, 5, 1, 3, 11] = V [0, 0, 8, 1] := by
  have h0 : V [5, 0, 7, 1, 5, 5, 0, 7, 1, 5, 0, 0, 8, 1] = V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 3, 11] :=
    overlap focused18752 cyclic27572 [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3] [5, 0, 7, 1, 5, 0, 0, 8, 1] (by decide)
  have hl : V [5, 0, 7, 1, 5, 5, 0, 7, 1, 5, 0, 0, 8, 1] = V [0, 0, 8, 1] :=
    ((in_context torus5 [5, 0, 7, 1] [0, 7, 1, 5, 0, 0, 8, 1]).trans ((in_context torus1 [5, 0, 7] [7, 1, 5, 0, 0, 8, 1]).trans ((in_context torus7 [5, 0] [1, 5, 0, 0, 8, 1]).trans ((in_context torus0 [5] [5, 0, 0, 8, 1]).trans (in_context torus5 [] [0, 0, 8, 1])))))
  have hr : V [1, 1, 7, 4, 5, 2, 0, 5, 4, 8, 2, 1, 5, 1, 3, 3, 11] = V [5, 0, 7, 1, 5, 1, 3, 11] :=
    (in_context focused18753 [] [3, 11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27618 : V [5, 1, 1, 2, 0, 4, 1, 2] = V [1, 3, 0, 12] := by
  have h0 : V [12, 8, 2, 1, 7, 6, 8, 7, 2, 8] = V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 7, 0] :=
    overlap cyclic27597 torus2172 [5, 1, 1, 2, 0, 4, 1, 2, 1, 7] [8, 2, 1, 7, 6, 8, 7, 2, 8] (by decide)
  have hl : V [12, 8, 2, 1, 7, 6, 8, 7, 2, 8] = V [1, 3, 0, 12] :=
    ((in_context torus84 [] [2, 1, 7, 6, 8, 7, 2, 8]).trans ((in_context torus48 [4] [1, 7, 6, 8, 7, 2, 8]).trans ((in_context torus94 [4, 5] [7, 6, 8, 7, 2, 8]).trans ((in_context torus78 [4, 5, 1] [6, 8, 7, 2, 8]).trans ((in_context torus72 [4, 5, 1, 3] [8, 7, 2, 8]).trans ((in_context torus84 [4, 5, 1, 3, 2] [7, 2, 8]).trans ((in_context torus4160 [] [12, 7, 2, 8]).trans ((in_context torus78 [1, 1, 3, 2, 4, 3] [2, 8]).trans ((in_context torus3 [1, 1, 3, 2, 4] [12, 2, 8]).trans ((in_context torus48 [1, 1, 3, 2, 4] [8]).trans ((in_context torus1518 [1] [12, 8]).trans ((in_context torus84 [1, 3, 0, 4] []).trans (in_context torus4 [1, 3, 0] [12])))))))))))))
  have hr : V [5, 1, 1, 2, 0, 4, 1, 2, 1, 7, 7, 0] = V [5, 1, 1, 2, 0, 4, 1, 2] :=
    ((in_context torus7 [5, 1, 1, 2, 0, 4, 1, 2, 1] [0]).trans (in_context torus1 [5, 1, 1, 2, 0, 4, 1, 2] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27620 : V [3, 1, 8, 1, 6, 0, 8, 1] = V [1, 8, 0, 12] := by
  have h0 : V [1, 7, 0, 4, 1, 7, 12, 0, 7, 1, 5, 1, 3, 11] = V [3, 1, 8, 1, 6, 1, 0, 0, 8, 1] :=
    overlap torus12984 cyclic27609 [3, 1, 8, 1, 6, 1] [0, 7, 1, 5, 1, 3, 11] (by decide)
  have hl : V [1, 7, 0, 4, 1, 7, 12, 0, 7, 1, 5, 1, 3, 11] = V [1, 8, 0, 12] :=
    ((in_context torus93 [1, 7, 0, 4, 1, 7] [7, 1, 5, 1, 3, 11]).trans ((in_context torus78 [1, 7, 0, 4, 1, 7, 0] [1, 5, 1, 3, 11]).trans ((in_context torus13352 [1] [12, 1, 5, 1, 3, 11]).trans ((in_context torus30 [1, 1, 8, 7, 3, 5, 4] [1, 5, 1, 3, 11]).trans ((in_context torus88 [1, 1, 8, 7, 3, 5, 4] [5, 1, 3, 11]).trans ((in_context torus1452 [1, 1, 8, 7, 3] [9, 5, 1, 3, 11]).trans ((in_context torus1550 [1, 1, 8, 7] [9, 5, 1, 3, 11]).trans ((in_context torus1479 [1, 1] [3, 2, 4, 9, 5, 1, 3, 11]).trans ((in_context torus1 [1] [7, 8, 3, 2, 4, 9, 5, 1, 3, 11]).trans ((in_context torus63 [1, 7, 8, 3, 2, 4] [1, 3, 11]).trans ((in_context torus4 [1, 7, 8, 3, 2] [9, 1, 3, 11]).trans ((in_context torus88 [1, 7, 8, 3, 2] [3, 11]).trans ((in_context torus1432 [1, 7, 8] [9, 3, 11]).trans ((in_context torus1490 [1] [2, 3, 9, 3, 11]).trans ((in_context torus1617 [1, 1] [9, 3, 11]).trans ((in_context torus1 [1] [8, 0, 2, 9, 3, 11]).trans ((in_context torus51 [1, 8, 0, 2] [11]).trans ((in_context torus2 [1, 8, 0] [9, 11]).trans (in_context torus11 [1, 8, 0] [])))))))))))))))))))
  have hr : V [3, 1, 8, 1, 6, 1, 0, 0, 8, 1] = V [3, 1, 8, 1, 6, 0, 8, 1] :=
    (in_context torus1 [3, 1, 8, 1, 6] [0, 8, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27621 : V [1, 1, 8, 0, 3, 1, 8, 1, 6] = V [4, 1, 12] := by
  have h0 : V [1, 2, 0, 4, 0, 12, 1, 8, 1, 6, 0, 8, 1] = V [5, 1, 8, 0, 0, 4, 5, 1, 8, 0, 12] :=
    overlap torus7291 cyclic27620 [5, 1, 8, 0, 0, 4, 5] [1, 8, 1, 6, 0, 8, 1] (by decide)
  have hl : V [1, 2, 0, 4, 0, 12, 1, 8, 1, 6, 0, 8, 1] = V [4, 1, 12] :=
    ((in_context torus94 [1, 2, 0, 4, 0] [8, 1, 6, 0, 8, 1]).trans ((in_context torus0 [1, 2, 0, 4] [12, 8, 1, 6, 0, 8, 1]).trans ((in_context torus84 [1, 2, 0, 4] [1, 6, 0, 8, 1]).trans ((in_context torus4 [1, 2, 0] [12, 1, 6, 0, 8, 1]).trans ((in_context torus94 [1, 2, 0] [6, 0, 8, 1]).trans ((in_context torus0 [1, 2] [12, 6, 0, 8, 1]).trans ((in_context torus72 [1, 2] [0, 8, 1]).trans ((in_context torus2 [1] [12, 0, 8, 1]).trans ((in_context torus93 [1] [8, 1]).trans ((in_context torus1 [] [12, 8, 1]).trans ((in_context torus84 [] [1]).trans (in_context torus94 [4] []))))))))))))
  have hr : V [5, 1, 8, 0, 0, 4, 5, 1, 8, 0, 12] = V [1, 1, 8, 0, 3, 1, 8, 1, 6] :=
    ((in_context torus11454 [] [1, 8, 0, 12]).trans ((in_context torus94 [1, 2, 0, 4, 0, 6] [8, 0, 12]).trans ((in_context torus13532 [1] [8, 0, 12]).trans ((in_context torus1490 [1, 1, 8, 7, 0, 4, 1] [12]).trans (in_context torus8761 [1, 1, 8] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27626 : V [1, 1, 8, 7, 0, 4, 1, 7, 8] = V [4, 1, 1] := by
  have h0 : V [4, 1, 12, 1, 11] = V [1, 1, 8, 0, 1, 7, 0, 4, 1, 7, 8] :=
    overlap cyclic27621 torus13986 [1, 1, 8, 0] [1, 11] (by decide)
  have hl : V [4, 1, 12, 1, 11] = V [4, 1, 1] :=
    ((in_context torus94 [4, 1] [11]).trans (in_context torus29 [4, 1, 1] []))
  have hr : V [1, 1, 8, 0, 1, 7, 0, 4, 1, 7, 8] = V [1, 1, 8, 7, 0, 4, 1, 7, 8] :=
    (in_context torus0 [1, 1, 8] [7, 0, 4, 1, 7, 8])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27627 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1, 1] = V [12] := by
  have h0 : V [4, 0, 6, 1, 4, 1, 2, 1, 8, 7, 0, 4, 1, 7, 8] = V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 4, 1, 1] :=
    overlap focused18519 cyclic27626 [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4] [1, 8, 7, 0, 4, 1, 7, 8] (by decide)
  have hl : V [4, 0, 6, 1, 4, 1, 2, 1, 8, 7, 0, 4, 1, 7, 8] = V [12] :=
    ((in_context torus7592 [4] [7, 0, 4, 1, 7, 8]).trans ((in_context torus78 [4, 3, 0, 7, 1, 3] [0, 4, 1, 7, 8]).trans ((in_context torus3 [4, 3, 0, 7, 1] [12, 0, 4, 1, 7, 8]).trans ((in_context torus93 [4, 3, 0, 7, 1] [4, 1, 7, 8]).trans ((in_context torus1 [4, 3, 0, 7] [12, 4, 1, 7, 8]).trans ((in_context torus60 [4, 3, 0, 7] [1, 7, 8]).trans ((in_context torus7 [4, 3, 0] [12, 1, 7, 8]).trans ((in_context torus94 [4, 3, 0] [7, 8]).trans ((in_context torus0 [4, 3] [12, 7, 8]).trans ((in_context torus78 [4, 3] [8]).trans ((in_context torus3 [4] [12, 8]).trans ((in_context torus84 [4] []).trans (in_context torus4 [] [12])))))))))))))
  have hr : V [1, 1, 6, 3, 4, 8, 0, 4, 3, 7, 8, 1, 4, 4, 1, 1] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1, 1] :=
    (in_context focused18520 [] [4, 1, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27628 : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1] = V [0, 12] := by
  have h0 : V [12, 0] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1] :=
    overlap cyclic27627 torus1 [4, 0, 6, 1, 4, 1, 2, 0, 4, 1] [0] (by decide)
  have hl : V [12, 0] = V [0, 12] :=
    (in_context torus93 [] [])
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1] = V [4, 0, 6, 1, 4, 1, 2, 0, 4, 1] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27675 : V [1, 6, 0, 0, 2, 1, 7, 0] = V [8, 1, 6, 11] := by
  have h0 : V [1, 6, 0, 0, 11, 1, 1, 2, 0, 4, 1, 2] = V [3, 1, 7, 0, 2, 0, 4, 6, 1, 3, 0, 12] :=
    overlap torus5603 cyclic27618 [3, 1, 7, 0, 2, 0, 4, 6] [1, 1, 2, 0, 4, 1, 2] (by decide)
  have hl : V [1, 6, 0, 0, 11, 1, 1, 2, 0, 4, 1, 2] = V [8, 1, 6, 11] :=
    ((in_context torus92 [1, 6, 0, 0] [1, 2, 0, 4, 1, 2]).trans ((in_context torus0 [1, 6, 0] [11, 1, 2, 0, 4, 1, 2]).trans ((in_context torus92 [1, 6, 0] [2, 0, 4, 1, 2]).trans ((in_context torus0 [1, 6] [11, 2, 0, 4, 1, 2]).trans ((in_context torus47 [1, 6] [0, 4, 1, 2]).trans ((in_context torus6 [1] [11, 0, 4, 1, 2]).trans ((in_context torus91 [1] [4, 1, 2]).trans ((in_context torus1 [] [11, 4, 1, 2]).trans ((in_context torus59 [] [1, 2]).trans ((in_context torus92 [8] [2]).trans (in_context torus47 [8, 1] [])))))))))))
  have hr : V [3, 1, 7, 0, 2, 0, 4, 6, 1, 3, 0, 12] = V [1, 6, 0, 0, 2, 1, 7, 0] :=
    ((in_context torus7073 [] [1, 3, 0, 12]).trans ((in_context torus92 [1, 6, 0, 0, 2] [3, 0, 12]).trans ((in_context torus53 [1, 6, 0, 0, 2, 1] [0, 12]).trans ((in_context torus91 [1, 6, 0, 0, 2, 1, 7] [12]).trans (in_context torus24 [1, 6, 0, 0, 2, 1, 7, 0] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27676 : V [1, 6, 0, 0, 2, 3, 1, 6, 0] = V [0, 2, 3] := by
  have h0 : V [8, 1, 6, 11, 2, 4, 3, 5, 12] = V [1, 6, 0, 0, 2, 1, 0, 3, 1, 6, 0] :=
    overlap cyclic27675 torus3278 [1, 6, 0, 0, 2, 1] [2, 4, 3, 5, 12] (by decide)
  have hl : V [8, 1, 6, 11, 2, 4, 3, 5, 12] = V [0, 2, 3] :=
    ((in_context torus47 [8, 1, 6] [4, 3, 5, 12]).trans ((in_context torus6 [8, 1] [11, 4, 3, 5, 12]).trans ((in_context torus59 [8, 1] [3, 5, 12]).trans ((in_context torus1489 [] [11, 3, 5, 12]).trans ((in_context torus53 [2, 8, 7] [5, 12]).trans ((in_context torus7 [2, 8] [11, 5, 12]).trans ((in_context torus65 [2, 8] [12]).trans ((in_context torus1428 [] [11, 12]).trans (in_context torus24 [0, 2, 3] [])))))))))
  have hr : V [1, 6, 0, 0, 2, 1, 0, 3, 1, 6, 0] = V [1, 6, 0, 0, 2, 3, 1, 6, 0] :=
    (in_context torus1 [1, 6, 0, 0, 2] [3, 1, 6, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27678 : V [1, 6, 0, 8, 1, 6, 1, 4, 0] = V [0, 2, 12] := by
  have h0 : V [0, 2, 3, 3, 12] = V [1, 6, 0, 0, 1, 8, 1, 6, 1, 4, 0] :=
    overlap cyclic27676 torus14155 [1, 6, 0, 0] [3, 12] (by decide)
  have hl : V [0, 2, 3, 3, 12] = V [0, 2, 12] :=
    (in_context torus3 [0, 2] [12])
  have hr : V [1, 6, 0, 0, 1, 8, 1, 6, 1, 4, 0] = V [1, 6, 0, 8, 1, 6, 1, 4, 0] :=
    (in_context torus0 [1, 6, 0] [8, 1, 6, 1, 4, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27704 : V [4, 0, 6, 1, 4, 1, 2, 11] = V [0, 0, 7, 1] := by
  have h0 : V [0, 12, 8, 0, 5, 1, 2, 4, 3, 5] = V [4, 0, 6, 1, 4, 1, 2, 0, 1, 11] :=
    overlap cyclic27628 torus2214 [4, 0, 6, 1, 4, 1, 2, 0] [8, 0, 5, 1, 2, 4, 3, 5] (by decide)
  have hl : V [0, 12, 8, 0, 5, 1, 2, 4, 3, 5] = V [0, 0, 7, 1] :=
    ((in_context torus84 [0] [0, 5, 1, 2, 4, 3, 5]).trans ((in_context torus93 [0, 4] [5, 1, 2, 4, 3, 5]).trans ((in_context torus66 [0, 4, 0] [1, 2, 4, 3, 5]).trans ((in_context torus94 [0, 4, 0, 8] [2, 4, 3, 5]).trans ((in_context torus48 [0, 4, 0, 8, 1] [4, 3, 5]).trans ((in_context torus4309 [0] [4, 3, 5]).trans ((in_context torus4 [0, 0, 7, 1, 5, 3] [3, 5]).trans ((in_context torus3 [0, 0, 7, 1, 5] [5]).trans (in_context torus5 [0, 0, 7, 1] [])))))))))
  have hr : V [4, 0, 6, 1, 4, 1, 2, 0, 1, 11] = V [4, 0, 6, 1, 4, 1, 2, 11] :=
    (in_context torus0 [4, 0, 6, 1, 4, 1, 2] [11])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27705 : V [1, 6, 0, 8, 1, 6, 0, 7, 1] = V [7, 1, 5] := by
  have h0 : V [0, 2, 12, 6, 1, 4, 1, 2, 11] = V [1, 6, 0, 8, 1, 6, 1, 0, 0, 7, 1] :=
    overlap cyclic27678 cyclic27704 [1, 6, 0, 8, 1, 6, 1] [6, 1, 4, 1, 2, 11] (by decide)
  have hl : V [0, 2, 12, 6, 1, 4, 1, 2, 11] = V [7, 1, 5] :=
    ((in_context torus72 [0, 2] [1, 4, 1, 2, 11]).trans ((in_context torus2 [0] [12, 1, 4, 1, 2, 11]).trans ((in_context torus94 [0] [4, 1, 2, 11]).trans ((in_context torus0 [] [12, 4, 1, 2, 11]).trans ((in_context torus60 [] [1, 2, 11]).trans ((in_context torus94 [7] [2, 11]).trans ((in_context torus48 [7, 1] [11]).trans (in_context torus29 [7, 1, 5] []))))))))
  have hr : V [1, 6, 0, 8, 1, 6, 1, 0, 0, 7, 1] = V [1, 6, 0, 8, 1, 6, 0, 7, 1] :=
    (in_context torus1 [1, 6, 0, 8, 1, 6] [0, 7, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27805 : V [4, 5, 2, 0, 5, 4, 8, 11] = V [7, 1, 1, 5] := by
  have h0 : V [7, 1, 5, 5, 1, 5] = V [1, 6, 0, 8, 1, 6, 0, 0, 7, 8, 6, 4] :=
    overlap cyclic27705 torus1935 [1, 6, 0, 8, 1, 6, 0] [5, 1, 5] (by decide)
  have hl : V [7, 1, 5, 5, 1, 5] = V [7, 1, 1, 5] :=
    (in_context torus5 [7, 1] [1, 5])
  have hr : V [1, 6, 0, 8, 1, 6, 0, 0, 7, 8, 6, 4] = V [4, 5, 2, 0, 5, 4, 8, 11] :=
    ((in_context torus3480 [1, 6, 0, 8, 1] [4]).trans ((in_context torus4477 [1] [7, 8, 6, 7, 4]).trans ((in_context torus77 [1, 4, 5, 3, 0, 6] [8, 6, 7, 4]).trans ((in_context torus2009 [1, 4] [11, 8, 6, 7, 4]).trans ((in_context torus1553 [1] [7, 6, 11, 8, 6, 7, 4]).trans ((in_context torus1480 [1, 3, 1, 3] [11, 8, 6, 7, 4]).trans ((in_context torus83 [1, 3, 1, 3, 7, 1, 7] [6, 7, 4]).trans ((in_context torus10351 [1] [11, 6, 7, 4]).trans ((in_context torus1 [] [4, 5, 2, 0, 5, 3, 11, 6, 7, 4]).trans ((in_context torus71 [4, 5, 2, 0, 5, 3] [7, 4]).trans ((in_context torus3 [4, 5, 2, 0, 5] [11, 7, 4]).trans ((in_context torus77 [4, 5, 2, 0, 5] [4]).trans (in_context torus59 [4, 5, 2, 0, 5, 4] [])))))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27806 : V [4, 5, 2, 0, 5, 4, 8, 2, 11] = V [7, 1, 1] := by
  have h0 : V [7, 1, 1, 5, 5] = V [4, 5, 2, 0, 5, 4, 8, 2, 11] :=
    overlap cyclic27805 torus65 [4, 5, 2, 0, 5, 4, 8] [5] (by decide)
  have hl : V [7, 1, 1, 5, 5] = V [7, 1, 1] :=
    (in_context torus5 [7, 1, 1] [])
  have hr : V [4, 5, 2, 0, 5, 4, 8, 2, 11] = V [4, 5, 2, 0, 5, 4, 8, 2, 11] :=
    rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27807 : V [1, 1, 1, 1] = V [0, 0, 0] := by
  have h0 : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 11] = V [1, 1, 7, 7, 1, 1] :=
    overlap focused18760 cyclic27806 [1, 1, 7] [11] (by decide)
  have hl : V [5, 0, 7, 1, 5, 1, 3, 0, 5, 0, 11] = V [0, 0, 0] :=
    ((in_context cyclic27573 [] [0, 11]).trans ((in_context torus93 [0, 0] [11]).trans (in_context torus29 [0, 0, 0] [])))
  have hr : V [1, 1, 7, 7, 1, 1] = V [1, 1, 1, 1] :=
    (in_context torus7 [1, 1] [1, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem cyclic27808 : V [0, 0, 0, 0] = V [1, 1, 1] := by
  have h0 : V [0, 0, 0, 0] = V [1, 1, 1] :=
    overlap cyclic27807 torus1 [1, 1, 1] [0] (by decide)
  have hl : V [0, 0, 0, 0] = V [0, 0, 0, 0] :=
    rfl
  have hr : V [1, 1, 1] = V [1, 1, 1] :=
    rfl
  exact hl.symm.trans (h0.trans hr)

/-- The source equations alone imply that the five-letter word has seventh power one. -/
theorem u_pow_seven : u ^ 7 = 1 := by
  have hf : V [0, 0, 0, 0, 0, 0, 0] = V [] :=
    ((in_context cyclic27808 [] [0, 0, 0]).trans ((in_context torus1 [1, 1] [0, 0]).trans ((in_context torus1 [1] [0]).trans (in_context torus1 [] []))))
  simpa only [V, symbol, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hf

/-- The auxiliary word also commutes with the source order-17 product `y⁻³`. -/
theorem u_commute_inverse_third : Commute u ((y ^ 3)⁻¹) :=
  (u_commute_y.pow_right 3).inv_right

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.OddTorus
