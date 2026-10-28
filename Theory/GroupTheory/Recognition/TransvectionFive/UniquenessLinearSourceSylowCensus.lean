module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangles
public import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases

/-!
# The maximum elementary subgroups of the marked Sylow model

Ten matrix entries encode the actual positive-root Sylow. Squaring and
commutation give six Boolean equations each. A kernel-checked list covers
all 192 elements whose square is one. For an involution outside the two
rectangles, at most 56 such elements commute with it; an elementary subgroup
of order at least 64 consequently lies in their union. A subgroup contained
in a union of two subgroups lies in one of them. The proved rectangle orders
then identify it with that rectangle.

This proves the maximum-elementary assertion in Aschbacher, *Sporadic Groups*
(1994), 39.1(3), printed p.213, needed for 39.6. It enumerates elements of a
1024-element Sylow, not subgroups or ambient groups. The numerical checks
are Boolean reductions checked by Lean's kernel, with no native-decision axiom.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
namespace SylowCoordinates

private def bit (a : ZMod 2) : Bool := decide (a = 1)
private def val (b : Bool) : ZMod 2 := if b then 1 else 0
private theorem val_bit (a : ZMod 2) : val (bit a) = a := by
  fin_cases a <;> rfl
private theorem val_xor (a b : Bool) : val (a ^^ b) = val a + val b := by
  cases a <;> cases b <;> decide
private theorem val_and (a b : Bool) : val (a && b) = val a * val b := by
  cases a <;> cases b <;> decide
private theorem val_injective : Function.Injective val := by decide

private def encode (g : SL) : BitVec 10 :=
  BitVec.cons (bit (g 3 4)) (BitVec.cons (bit (g 2 4))
  (BitVec.cons (bit (g 2 3)) (BitVec.cons (bit (g 1 4))
  (BitVec.cons (bit (g 1 3)) (BitVec.cons (bit (g 1 2))
  (BitVec.cons (bit (g 0 4)) (BitVec.cons (bit (g 0 3))
  (BitVec.cons (bit (g 0 2)) (BitVec.cons (bit (g 0 1)) 0)))))))))

private def position : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

private theorem encode_entry (g : SL) (i : Fin 10) :
    val ((encode g).getLsbD i) = g (position i).1 (position i).2 := by
  fin_cases i <;> simp [encode, position, BitVec.getElem_cons, val_bit]

private theorem upper_entry (g : upper) (i j : Fin 5) (h : j ≤ i) :
    (g : SL) i j = if i = j then 1 else 0 := by
  have hg : (g : SL) ∈ Theory.SpecificGroups.LinearSylowNormalizers.unipotent 5 (ZMod 2) :=
    model_upper_eq_unipotent ▸ g.property
  obtain ⟨hu, hd⟩ := (Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent 5 (ZMod 2) _).mp hg
  by_cases he : i = j
  · simpa [he] using hd j
  · rw [if_neg he]
    exact (Theory.SpecificGroups.LinearSylowNormalizers.mem_borel 5 (ZMod 2) _).mp hu
      (lt_of_le_of_ne h (Ne.symm he))

/-- Ten strict upper entries faithfully encode the literal root Sylow. -/
private theorem encode_injective : Function.Injective (fun g : upper => encode g) := by
  intro g h he
  change encode (g : SL) = encode (h : SL) at he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  by_cases hij : j ≤ i
  · rw [upper_entry g i j hij, upper_entry h i j hij]
  · have he' (k : Fin 10) : (g : SL) (position k).1 (position k).2 =
        (h : SL) (position k).1 (position k).2 := by
      rw [← encode_entry, ← encode_entry, he]
    fin_cases i <;> fin_cases j <;> try (exfalso; exact hij (by decide))
    all_goals first | exact he' 0 | exact he' 1 | exact he' 2 | exact he' 3 | exact he' 4 | exact he' 5 | exact he' 6 | exact he' 7 | exact he' 8 | exact he' 9

/-- Boolean equations for squaring a unitriangular element to the identity. -/
private def square (a : BitVec 10) : Bool :=
  !(a[0]! && a[4]!) &&
  !((a[0]! && a[5]!) ^^ (a[1]! && a[7]!)) &&
  !((a[0]! && a[6]!) ^^ (a[1]! && a[8]!) ^^ (a[2]! && a[9]!)) &&
  !(a[4]! && a[7]!) &&
  !((a[4]! && a[8]!) ^^ (a[5]! && a[9]!)) &&
  !(a[7]! && a[9]!)

/-- Boolean equations for the commutation of two unitriangular elements. -/
private def commute (a b : BitVec 10) : Bool :=
  ((a[0]! && b[4]!) == (b[0]! && a[4]!)) &&
  (((a[0]! && b[5]!) ^^ (a[1]! && b[7]!)) ==
    ((b[0]! && a[5]!) ^^ (b[1]! && a[7]!))) &&
  (((a[0]! && b[6]!) ^^ (a[1]! && b[8]!) ^^ (a[2]! && b[9]!)) ==
    ((b[0]! && a[6]!) ^^ (b[1]! && a[8]!) ^^ (b[2]! && a[9]!))) &&
  ((a[4]! && b[7]!) == (b[4]! && a[7]!)) &&
  (((a[4]! && b[8]!) ^^ (a[5]! && b[9]!)) ==
    ((b[4]! && a[8]!) ^^ (b[5]! && a[9]!))) &&
  ((a[7]! && b[9]!) == (b[7]! && a[9]!))

/-- Matrix squaring implies the six binary equations. -/
private theorem square_encode (g : upper) (h : (g : SL) * g = 1) : square (encode g) = true := by
  simp only [square, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 2) h
    change ((g : SL).val * (g : SL).val) 0 2 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 3) h
    change ((g : SL).val * (g : SL).val) 0 3 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 4) h
    change ((g : SL).val * (g : SL).val) 0 4 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he
  · apply val_injective
    have he := congrArg (fun a : SL => a 1 3) h
    change ((g : SL).val * (g : SL).val) 1 3 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he
  · apply val_injective
    have he := congrArg (fun a : SL => a 1 4) h
    change ((g : SL).val * (g : SL).val) 1 4 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he
  · apply val_injective
    have he := congrArg (fun a : SL => a 2 4) h
    change ((g : SL).val * (g : SL).val) 2 4 = 0 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit, show val false = 0 from rfl]
    try rw [← mul_eq_zero]
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])) he

/-- Matrix commutation implies the six binary equations. -/
private theorem commute_encode (g h : upper) (heq : (g : SL) * h = h * g) :
    commute (encode g) (encode h) = true := by
  simp only [commute, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 2) heq
    change ((g : SL).val * (h : SL).val) 0 2 = ((h : SL).val * (g : SL).val) 0 2 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 3) heq
    change ((g : SL).val * (h : SL).val) 0 3 = ((h : SL).val * (g : SL).val) 0 3 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he
  · apply val_injective
    have he := congrArg (fun a : SL => a 0 4) heq
    change ((g : SL).val * (h : SL).val) 0 4 = ((h : SL).val * (g : SL).val) 0 4 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he
  · apply val_injective
    have he := congrArg (fun a : SL => a 1 3) heq
    change ((g : SL).val * (h : SL).val) 1 3 = ((h : SL).val * (g : SL).val) 1 3 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he
  · apply val_injective
    have he := congrArg (fun a : SL => a 1 4) heq
    change ((g : SL).val * (h : SL).val) 1 4 = ((h : SL).val * (g : SL).val) 1 4 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_xor, val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he
  · apply val_injective
    have he := congrArg (fun a : SL => a 2 4) heq
    change ((g : SL).val * (h : SL).val) 2 4 = ((h : SL).val * (g : SL).val) 2 4 at he
    simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry] at he
    simp [val_and, encode, BitVec.getElem_cons, val_bit]
    linear_combination he

private def rect2 (a : BitVec 10) : Bool := !a[0]! && !a[7]! && !a[8]! && !a[9]!
private def rect3 (a : BitVec 10) : Bool := !a[0]! && !a[1]! && !a[4]! && !a[9]!

private def involutionList : List (BitVec 10) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
   48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78,
   80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110,
   112, 114, 116, 118, 120, 122, 124, 126, 128, 129, 132, 133, 136, 137, 140, 141,
   160, 163, 164, 167, 168, 171, 172, 175, 192, 196, 200, 204, 224, 228, 232, 236,
   256, 257, 260, 261, 264, 265, 268, 269, 288, 292, 296, 300, 320, 323, 324, 327,
   328, 331, 332, 335, 352, 356, 360, 364, 384, 385, 388, 389, 392, 393, 396, 397,
   416, 420, 424, 428, 448, 452, 456, 460, 480, 483, 484, 487, 488, 491, 492, 495,
   512, 513, 514, 515, 520, 521, 522, 523, 528, 530, 536, 538, 576, 578, 581, 583,
   584, 586, 589, 591, 592, 594, 600, 602, 768, 769, 774, 775, 776, 777, 782, 783,
   816, 822, 824, 830, 832, 835, 837, 838, 840, 843, 845, 846, 880, 886, 888, 894]

set_option maxRecDepth 4096 in
private theorem square_check : ((List.range 1024).all fun n => !square (BitVec.ofNat 10 n) ||
    involutionList.contains (BitVec.ofNat 10 n)) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem bound_check : (involutionList.all fun a => rect2 a || rect3 a ||
    decide ((involutionList.filter (commute a)).length ≤ 56)) = true := by decide +kernel


private theorem square_mem (a : BitVec 10) (ha : square a = true) : a ∈ involutionList := by
  have hh := List.all_eq_true.mp square_check a.toNat (List.mem_range.mpr a.isLt)
  simpa [ha] using hh

private def candidates (a : BitVec 10) : Finset (BitVec 10) := (involutionList.filter (commute a)).toFinset

private theorem candidate_mem (a b : BitVec 10) (hb : square b = true) (hc : commute a b = true) :
    b ∈ candidates a := by
  exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨square_mem b hb, hc⟩)

private theorem candidate_bound (a : BitVec 10) (ha : square a = true)
    (h2 : rect2 a ≠ true) (h3 : rect3 a ≠ true) : (candidates a).card ≤ 56 := by
  have hh := List.all_eq_true.mp bound_check a (square_mem a ha)
  have hh' : (involutionList.filter (commute a)).length ≤ 56 := by
    simpa [h2, h3] using hh
  exact (List.toFinset_card_le _).trans hh'


private theorem ne_one_iff (a : ZMod 2) : a ≠ 1 ↔ a = 0 := by
  exact (by decide : ∀ a : ZMod 2, a ≠ 1 ↔ a = 0) a

/-- The bit test describes the actual plane rectangle, not an abstract tag. -/
private theorem rect2_encode (g : upper) : rect2 (encode g) = true ↔ (g : SL) ∈ rectangle 2 := by
  have hb : rect2 (encode g) = true ↔
      (g : SL) 0 1 = 0 ∧ (g : SL) 2 3 = 0 ∧ (g : SL) 2 4 = 0 ∧ (g : SL) 3 4 = 0 := by
    simp [rect2, encode, BitVec.getElem_cons, bit, ne_one_iff, and_assoc]
  rw [hb, RectangleCoordinates.mem2_iff]
  constructor
  · intro hg i j hij
    by_cases hji : j ≤ i
    · exact upper_entry g i j hji
    · fin_cases i <;> fin_cases j <;> simp_all
  · intro hg
    exact ⟨hg 0 1 (by decide), hg 2 3 (by decide), hg 2 4 (by decide), hg 3 4 (by decide)⟩

/-- The second bit test retains the literal three-space rectangle. -/
private theorem rect3_encode (g : upper) : rect3 (encode g) = true ↔ (g : SL) ∈ rectangle 3 := by
  have hb : rect3 (encode g) = true ↔
      (g : SL) 0 1 = 0 ∧ (g : SL) 0 2 = 0 ∧ (g : SL) 1 2 = 0 ∧ (g : SL) 3 4 = 0 := by
    simp [rect3, encode, BitVec.getElem_cons, bit, ne_one_iff, and_assoc]
  rw [hb, RectangleCoordinates.mem3_iff]
  constructor
  · intro hg i j hij
    by_cases hji : j ≤ i
    · exact upper_entry g i j hji
    · fin_cases i <;> fin_cases j <;> simp_all
  · intro hg
    exact ⟨hg 0 1 (by decide), hg 0 2 (by decide), hg 1 2 (by decide), hg 3 4 (by decide)⟩

end SylowCoordinates
open SylowCoordinates

/-- The only elementary subgroups of order at least 64 in the actual root Sylow
lie in one of its two rectangles. The bound counts involutions centralizing an
outside element, rather than enumerating subgroups. -/
theorem model_large_elementary_le_rectangle (E : Subgroup SL) [IsElementaryAbelian 2 E]
    (hET : E ≤ upper) (hcard : 64 ≤ Nat.card E) : E ≤ rectangle 2 ∨ E ≤ rectangle 3 := by
  apply SubgroupClass.subset_union.mp
  intro a ha
  by_contra hn
  have h2 : a ∉ rectangle 2 := fun h => hn (Or.inl h)
  have h3 : a ∉ rectangle 3 := fun h => hn (Or.inr h)
  let a' : upper := ⟨a, hET ha⟩
  have hsq : square (encode a) = true := square_encode a' (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
  have hbound : (candidates (encode a)).card ≤ 56 := candidate_bound (encode a) hsq
    (fun h => h2 ((rect2_encode a').mp h)) (fun h => h3 ((rect3_encode a').mp h))
  let f : E → ↥(candidates (encode a)) := fun b => ⟨encode b, candidate_mem _ _
    (square_encode ⟨b, hET b.property⟩ (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (b : SL) b.property))
    (commute_encode a' ⟨b, hET b.property⟩ (setLike_mul_comm ha b.property))⟩
  have hf : Function.Injective f := by
    intro b c he
    have hh : encode (b : SL) = encode (c : SL) := congrArg Subtype.val he
    have he' := encode_injective (a₁ := (⟨b, hET b.property⟩ : upper))
      (a₂ := (⟨c, hET c.property⟩ : upper)) hh
    exact Subtype.ext (congrArg (fun x : upper => (x : SL)) he')
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥(candidates (encode a))), Fintype.card_coe] at hc
  omega

/-- Source 39.1(3): the two rectangles are the only elementary subgroups
of maximum order in the actual Sylow model. -/
theorem model_large_elementary_eq_rectangle (E : Subgroup SL) [IsElementaryAbelian 2 E]
    (hET : E ≤ upper) (hcard : 64 ≤ Nat.card E) : E = rectangle 2 ∨ E = rectangle 3 := by
  rcases model_large_elementary_le_rectangle E hET hcard with h2 | h3
  · exact Or.inl (eq_of_le_of_card_ge h2 (RectangleCoordinates.card2 ▸ hcard))
  · exact Or.inr (eq_of_le_of_card_ge h3 (RectangleCoordinates.card3 ▸ hcard))

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
