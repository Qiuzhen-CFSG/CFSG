module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup

/-!
# The six-generator quotient of the presentation interval

The four core generators are normalized by every presentation generator.
Their quotient images therefore define a genuine group quotient. The six
slice generators commute and have square one in this quotient. A single
binary-product induction proves the xor multiplication law, and its range
is a subgroup containing the image of every envelope generator.

All generator comparisons use the literal presentation relations through
`Profiles.collect_sound`. No order or matrix-identification premise is used.
Source context: Aschbacher–Smith A.3.12, pp.47–48; the presentation provenance
in `SylowNormalEights/source/README.md`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles
open Theory.GroupTheory.BinaryCollection

abbrev coreIndices : List (Fin 21) := [16, 18, 19, 20]
abbrev sliceIndices : List (Fin 21) := [9, 11, 13, 14, 15, 17]

theorem word_mem (K : Subgroup Carrier) (w : List (Fin 21))
    (h : ∀ i ∈ w, generator i ∈ K) : wordValue w ∈ K := by
  apply K.list_prod_mem
  rintro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi

theorem generator_mem_core (i : Fin 21) (hi : i ∈ coreIndices) : generator i ∈ core := by
  have hh : [i] ∈ coreWords := by simpa [coreIndices, coreWords] using hi
  exact (wordSubgroup_le_iff generator coreWords core).mp le_rfl [i] hh

theorem collected_core (w : List (Fin 21)) (fuel : ℕ)
    (h : ∀ i ∈ collect fuel w, i ∈ coreIndices) : wordValue w ∈ core := by
  rw [← collect_sound fuel w]
  exact word_mem core _ (fun i hi => generator_mem_core i (h i hi))

private theorem conjugate_support : ∀ i b : Fin 21, b ∈ coreIndices →
    ∀ k ∈ collect 16 (inverseGeneratorWord i ++ [b, i]), k ∈ coreIndices := by
  decide +kernel

instance core_normal : core.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Set.range relator)]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change generator i ∈ Subgroup.normalizer (core : Set Carrier)
  apply (Subgroup.inv_mem_iff _).mp
  apply Subgroup.mem_normalizer_fintype
  have hh : core ≤ core.comap (MulAut.conj (generator i)⁻¹).toMonoidHom := by
    apply (wordSubgroup_le_iff generator coreWords _).mpr
    intro w hw
    have hw' : ∃ b ∈ coreIndices, w = [b] := by
      simpa [coreWords, coreIndices] using hw
    obtain ⟨b, hb, rfl⟩ := hw'
    change (generator i)⁻¹ * (generator b * 1) * ((generator i)⁻¹)⁻¹ ∈ core
    have h := collected_core (inverseGeneratorWord i ++ [b, i]) 16
      (conjugate_support i b hb)
    simpa only [wordValue_append, wordValue_inverseGeneratorWord, wordValue_cons,
      wordValue_nil, mul_one, inv_inv, mul_assoc] using h
  intro x hx
  exact hh hx

abbrev Q := Carrier ⧸ core
noncomputable def q : Carrier →* Q := QuotientGroup.mk' core

theorem q_eq_one {x : Carrier} : q x = 1 ↔ x ∈ core := QuotientGroup.eq_one_iff x

theorem q_generator_core (i : Fin 21) (hi : i ∈ coreIndices) : q (generator i) = 1 :=
  q_eq_one.mpr (generator_mem_core i hi)

noncomputable def v (n : Code) : Q := q (sliceValue n)

private theorem slice_square_support : ∀ i : Fin 21, i ∈ sliceIndices → squareWord i = [] := by
  decide +kernel

theorem q_square (i : Fin 21) (hi : i ∈ sliceIndices) :
    q (generator i) * q (generator i) = 1 := by
  rw [← map_mul, generator_relations.square, slice_square_support i hi]
  exact map_one q

private theorem slice_commute_support : ∀ i j : Fin 21,
    i ∈ sliceIndices → j ∈ sliceIndices →
    ∀ k ∈ collect 16 ([i, j] ++ inverseWord [j, i]), k ∈ coreIndices := by
  decide +kernel

theorem q_commute (i j : Fin 21) (hi : i ∈ sliceIndices) (hj : j ∈ sliceIndices) :
    Commute (q (generator i)) (q (generator j)) := by
  have h := collected_core ([i, j] ++ inverseWord [j, i]) 16
    (slice_commute_support i j hi hj)
  have he := q_eq_one.mpr h
  change q (generator i) * q (generator j) = q (generator j) * q (generator i)
  simpa only [wordValue_append, wordValue_inverseWord, wordValue_cons, wordValue_nil,
    mul_one, map_mul, map_inv, mul_inv_eq_one] using he

private theorem product_commute {G : Type*} [Group G] (x : G) (l : List G)
    (h : ∀ y ∈ l, Commute x y) (n : ℕ) : Commute x (product l n) := by
  induction l generalizing n with
  | nil => exact Commute.one_right x
  | cons a l ih =>
    exact ((h a List.mem_cons_self).pow_right _).mul_right
      (ih (fun y hy => h y (List.mem_cons_of_mem a hy)) _)

private theorem product_xor {G : Type*} [Group G] (l : List G)
    (hs : ∀ x ∈ l, x * x = 1)
    (hc : ∀ x ∈ l, ∀ y ∈ l, Commute x y) (a b : ℕ) :
    product l (a ^^^ b) = product l a * product l b := by
  induction l generalizing a b with
  | nil => simp [product]
  | cons x l ih =>
    have hh : x ^ ((a ^^^ b) % 2) = x ^ (a % 2) * x ^ (b % 2) := by
      rw [show (a ^^^ b) % 2 = a % 2 ^^^ b % 2 from Nat.xor_mod_two_pow (n := 1)]
      have ha := Nat.mod_lt a (by decide : 0 < 2)
      have hb := Nat.mod_lt b (by decide : 0 < 2)
      interval_cases ha' : a % 2 <;> interval_cases hb' : b % 2 <;>
        simp [hs x List.mem_cons_self]
    rw [product, Nat.xor_div_two, ih
      (fun y hy => hs y (List.mem_cons_of_mem x hy))
      (fun y hy z hz => hc y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz)), hh]
    exact (product_commute x l (fun y hy => hc x List.mem_cons_self y
      (List.mem_cons_of_mem x hy)) (a / 2)).symm.pow_right (b % 2) |>.mul_mul_mul_comm _ _ |>.symm

theorem v_product (n : Code) :
    v n = product (sliceIndices.map (fun i => q (generator i))) n.val := by
  unfold v sliceValue sliceWord
  rw [map_list_prod, List.map_map]
  have h := congrArg q (wordValue_selectWord sliceIndices n.val)
  -- The recursive product commutes with every homomorphism.
  have hm (l : List Carrier) (m : ℕ) : q (product l m) = product (l.map q) m := by
    induction l generalizing m with
    | nil => exact map_one q
    | cons x l ih => simp only [product, List.map_cons, map_mul, map_pow, ih]
  simpa only [wordValue, map_list_prod, List.map_map, hm, Function.comp_def] using h

theorem v_mul (a b : Code) : v a * v b = v (codeXor a b) := by
  rw [v_product, v_product, v_product]
  have hb : Nat.xor a.val b.val < 64 := Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt
  simp only [codeXor, Nat.mod_eq_of_lt hb]
  symm
  apply product_xor
  · rintro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact q_square i hi
  · rintro x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact q_commute i j hi hj

@[simp] theorem v_zero : v 0 = 1 := map_one q

theorem v_inv (a : Code) : (v a)⁻¹ = v a := by
  apply inv_eq_of_mul_eq_one_right
  rw [v_mul]
  have he : codeXor a a = 0 := by simp [codeXor]
  rw [he, v_zero]

noncomputable def imageSubgroup : Subgroup Q where
  carrier := Set.range v
  one_mem' := ⟨0, v_zero⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨codeXor a b, (v_mul a b).symm⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a, (v_inv a).symm⟩

theorem envelope_cover (x : Carrier) (hx : x ∈ envelope) :
    ∃ n : Code, x * (sliceValue n)⁻¹ ∈ core := by
  have hh : envelope ≤ imageSubgroup.comap q := by
    apply (wordSubgroup_le_iff generator envelopeWords _).mpr
    intro w hw
    simp only [envelopeWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change q (wordValue _) ∈ imageSubgroup
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨16, rfl⟩
    · exact ⟨0, by simpa only [v_zero, wordValue_cons, wordValue_nil, mul_one] using
        (q_generator_core 16 (by decide)).symm⟩
    · exact ⟨32, rfl⟩
    · exact ⟨0, by simpa only [v_zero, wordValue_cons, wordValue_nil, mul_one] using
        (q_generator_core 18 (by decide)).symm⟩
    · exact ⟨0, by simpa only [v_zero, wordValue_cons, wordValue_nil, mul_one] using
        (q_generator_core 19 (by decide)).symm⟩
    · exact ⟨0, by simpa only [v_zero, wordValue_cons, wordValue_nil, mul_one] using
        (q_generator_core 20 (by decide)).symm⟩
  obtain ⟨n, hn⟩ := hh hx
  refine ⟨n, q_eq_one.mp ?_⟩
  rw [map_mul, map_inv, ← hn]
  exact mul_inv_cancel _

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
