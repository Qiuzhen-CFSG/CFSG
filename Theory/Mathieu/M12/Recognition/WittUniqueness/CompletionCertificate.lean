module

public import Theory.Mathieu.M12.Recognition.WittUniqueness.Coordinates
public import Theory.Mathieu.M11.Basic
public import Theory.Mathieu.M12.Block
public import Mathlib.Data.Fintype.Card
public import Theory.GroupTheory.SteinerSystem.Completion

/-!
# Completing the normalized twelve-point Witt design

A block of an `S(5,6,12)` must meet every distinct block in at most four points.
For the 66 augmented concrete eleven-point blocks, the only six-subsets with
this compatibility property are concrete twelve-point hexads. We check the
required implication over all 4096 point masks, then prove that every finite
point set has a mask. Thus compatibility gives block inclusion, and the
Steiner axioms turn inclusion into equality.

The seed masks below are checked against the explicit point embedding;
the conclusion uses the literal `m12BlockMaskArray`. All finite checks use
kernel reduction. The sixteen small certificates bound the memory needed by
an individual kernel check, and are checked sequentially.

This supplies the geometric extension step for Aschbacher, *Sporadic Groups*,
Exercise 6.6(6–7), printed p. 95, cited in *A 2-local characterization of M12*,
Lemma 4.11. The proof of unconditional design uniqueness does not assume an
invariant group action.
-/

namespace Sporadic.Mathieu.M12WittUniqueness

set_option maxRecDepth 100000
private abbrev Mask := Fin 4096
private def decode (m : Mask) : Finset (Fin 12) :=
  Finset.univ.filter (fun x => m.val.testBit x.val)
private def weight (m : Mask) : Nat := Nat.count (fun k => m.val.testBit k = true) 12
private def meet (a b : Mask) : Mask :=
  ⟨a.val &&& b.val, lt_of_le_of_lt Nat.and_le_left a.isLt⟩
private def compatible (a b : Mask) : Bool := a == b || decide (weight (meet a b) < 5)
private def seedArray : Array Mask := #[
  467, 1415, 907, 2467, 207, 2755, 1251, 2199,
  187, 1683, 679, 3211, 359, 2379, 1859, 287,
  3347, 819, 2823, 1323, 599, 1115, 2163, 3143,
  619, 1079, 2587, 2095, 1551, 3619, 965, 489,
  3521, 437, 1433, 2961, 2445, 1953, 1237, 2265,
  753, 2277, 1737, 669, 3249, 1197, 3717, 2729,
  2389, 857, 1393, 1357, 2913, 1813, 2361, 813,
  3365, 3849, 125, 3665, 2637, 1637, 3177, 3101,
  2613, 1593,
]
private def seed (i : Fin 66) : Mask := seedArray[i.val]'(by change i.val < 66; exact i.isLt)
private noncomputable def check (m : Mask) : Bool :=
  weight m != 6 || m12BlockMaskArray.contains m.val ||
    (!(List.finRange 66).all (fun i => compatible m (seed i)))
-- Keep each reduction at most 256 masks, rather than retaining all intermediate
-- reductions for the entire powerset in a single kernel invocation.
private def chunkMask (k : Fin 16) (m : Fin 256) : Mask :=
  ⟨m.val + 256 * k.val, by omega⟩
set_option Elab.async false in
private theorem check_0 : ∀ m, check (chunkMask 0 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_1 : ∀ m, check (chunkMask 1 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_2 : ∀ m, check (chunkMask 2 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_3 : ∀ m, check (chunkMask 3 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_4 : ∀ m, check (chunkMask 4 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_5 : ∀ m, check (chunkMask 5 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_6 : ∀ m, check (chunkMask 6 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_7 : ∀ m, check (chunkMask 7 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_8 : ∀ m, check (chunkMask 8 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_9 : ∀ m, check (chunkMask 9 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_10 : ∀ m, check (chunkMask 10 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_11 : ∀ m, check (chunkMask 11 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_12 : ∀ m, check (chunkMask 12 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_13 : ∀ m, check (chunkMask 13 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_14 : ∀ m, check (chunkMask 14 m) = true := by decide +kernel
set_option Elab.async false in
private theorem check_15 : ∀ m, check (chunkMask 15 m) = true := by decide +kernel
private theorem check_chunk (k : Fin 16) (m : Fin 256) : check (chunkMask k m) = true := by
  fin_cases k
  · exact check_0 m
  · exact check_1 m
  · exact check_2 m
  · exact check_3 m
  · exact check_4 m
  · exact check_5 m
  · exact check_6 m
  · exact check_7 m
  · exact check_8 m
  · exact check_9 m
  · exact check_10 m
  · exact check_11 m
  · exact check_12 m
  · exact check_13 m
  · exact check_14 m
  · exact check_15 m
private theorem check_true (m : Mask) : check m = true := by
  let k : Fin 16 := ⟨m.val / 256, by omega⟩
  let r : Fin 256 := ⟨m.val % 256, by omega⟩
  have heq : chunkMask k r = m := by
    apply Fin.ext
    simp only [chunkMask, k, r]
    omega
  rw [← heq]
  exact check_chunk k r

private theorem decode_card (m : Mask) : (decode m).card = weight m := by
  rw [weight, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt,
      (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro n hn
    obtain ⟨hn, hbit⟩ := Finset.mem_filter.mp hn
    exact ⟨⟨n, Finset.mem_range.mp hn⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩, rfl⟩
private theorem seed_decode : ∀ i : Fin 66, decode (seed i) =
    insert 0 ((m11BlockAt i).map pointEmbedding) := by decide +kernel

private theorem decode_meet (a b : Mask) : decode (meet a b) = decode a ∩ decode b := by
  ext x
  simp [decode, meet, Nat.testBit_and]

private theorem decode_injective : Function.Injective decode := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have hm := Finset.ext_iff.mp h ⟨i, hi⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [decode, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · have hab : 4096 ≤ 2 ^ i := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hab),
      Nat.testBit_lt_two_pow (b.isLt.trans_le hab)]

private theorem decode_surjective : Function.Surjective decode :=
  ((Fintype.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective, by simp [Mask, Fintype.card_finset]⟩).2

private theorem compatible_iff (a b : Mask) : compatible a b = true ↔
    decode a = decode b ∨ (decode a ∩ decode b).card < 5 := by
  simp only [compatible, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ← decode_meet, decode_card, decode_injective.eq_iff]

/-- The augmented concrete eleven-point blocks determine every block of an
`S(5,6,12)`, and hence determine the entire concrete twelve-point design. -/
public theorem blocks_eq_of_augmented (D : Theory.GroupTheory.SteinerSystem (Fin 12) 5 6)
    (hseed : ∀ B ∈ m11Blocks,
      insert 0 (B.map pointEmbedding) ∈ D.blocks) :
    D.blocks = m12WittDesign.blocks := by
  apply D.blocks_eq_of_subset m12WittDesign (by decide)
  intro B hB
  obtain ⟨m, rfl⟩ := decode_surjective B
  have hw : weight m = 6 := (decode_card m).symm.trans (D.block_card _ hB)
  have hc : (List.finRange 66).all (fun i => compatible m (seed i)) = true := by
    apply List.all_eq_true.mpr
    intro i _
    apply (compatible_iff m (seed i)).mpr
    have hmem : decode (seed i) ∈ D.blocks := by
      rw [seed_decode]
      exact hseed _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    by_cases heq : decode m = decode (seed i)
    · exact Or.inl heq
    · exact Or.inr (D.inter_card_lt hB hmem heq)
  have hm : m12BlockMaskArray.contains m.val = true := by
    simpa only [check, hw, bne_self_eq_false, hc, Bool.not_true,
      Bool.false_or, Bool.or_false] using check_true m
  obtain ⟨i, hi, him⟩ := Array.mem_iff_getElem.mp (Array.contains_iff_mem.mp hm)
  let j : Fin 132 := ⟨i, by simpa only [m12BlockMaskArray_size] using hi⟩
  have hmask : m12BlockMask j = m.val := him
  have hd : decode m = m12BlockAt j := by
    simp only [decode, m12BlockAt, m12MaskBlock, hmask]
  rw [hd]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

end Sporadic.Mathieu.M12WittUniqueness
