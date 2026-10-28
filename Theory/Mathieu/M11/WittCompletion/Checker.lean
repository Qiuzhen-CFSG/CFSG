module

public import Theory.Mathieu.M11.WittCompletionSeed
public import Theory.Mathieu.M11.Basic
public import Theory.GroupTheory.SteinerSystem.Transport

/-!
# Sound checker for the normalized Witt completion certificate

Candidate masks encode subsets of eleven points. A forced unique extension or
an exhaustive branch preserves the bound on the blocks of an unknown design.
The generated certificate uses these rules and identifies every terminal family
with a relabeling of the explicit Witt model. Reference: Hall, *The Theory of
Groups*, Theorem 5.8.1; see also `WittCompletionSeed`.
-/

namespace Sporadic.Mathieu.WittCompletion
open Theory.GroupTheory
open scoped Pointwise

public section
set_option maxRecDepth 100000

abbrev Mask := Fin 2048

@[expose]
def decode (m : Mask) : Finset (Fin 11) :=
  Finset.univ.filter (fun x => m.val.testBit x.val)

@[expose]
def meet (a b : Mask) : Mask :=
  ⟨a.val &&& b.val, lt_of_le_of_lt Nat.and_le_left a.isLt⟩

@[expose]
def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => m % 2 + countBits n (m / 2)

@[expose]
def weight (m : Mask) : Nat := countBits 11 m.val

theorem decode_card : ∀ m : Mask, (decode m).card = weight m := by decide +kernel

theorem decode_meet (a b : Mask) : decode (meet a b) = decode a ∩ decode b := by
  ext x
  simp [decode, meet, Nat.testBit_and]

theorem decode_injective : Function.Injective decode := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · have hm := Finset.ext_iff.mp h ⟨i, hi⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [decode, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · have hab : 2048 ≤ 2 ^ i := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hab),
      Nat.testBit_lt_two_pow (b.isLt.trans_le hab)]

theorem contains_iff (s b : Mask) : s.val &&& b.val = s.val ↔ decode s ⊆ decode b := by
  rw [← Finset.inter_eq_left]
  rw [← decode_meet, decode_injective.eq_iff]
  exact (@Fin.ext_iff 2048 (meet s b) s).symm

@[expose]
def compatible (a b : Mask) : Bool := a == b || decide (weight (meet a b) < 4)

theorem compatible_iff (a b : Mask) : compatible a b = true ↔
    decode a = decode b ∨ (decode a ∩ decode b).card < 4 := by
  simp only [compatible, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ← decode_meet, decode_card, decode_injective.eq_iff]

@[expose]
def options (cs : List Mask) (s : Mask) : List Mask :=
  cs.filter (fun b => s.val &&& b.val == s.val)

@[expose]
def restrict (cs : List Mask) (b : Mask) : List Mask := cs.filter (compatible · b)

@[expose]
def Bounds (D : SteinerSystem (Fin 11) 4 5) (cs : List Mask) : Prop :=
  ∀ B ∈ D.blocks, ∃ b ∈ cs, decode b = B

theorem choose (D : SteinerSystem (Fin 11) 4 5) {cs : List Mask}
    (h : Bounds D cs) {s : Mask} (hs : weight s = 4) :
    ∃ b ∈ options cs s, decode b ∈ D.blocks := by
  obtain ⟨B, ⟨hB, hSB⟩, _⟩ := D.existsUnique_block (decode s) ((decode_card s).trans hs)
  obtain ⟨b, hb, rfl⟩ := h B hB
  exact ⟨b, List.mem_filter.mpr ⟨hb, by simpa using (contains_iff s b).mpr hSB⟩, hB⟩

theorem restrict_sound (D : SteinerSystem (Fin 11) 4 5) {cs : List Mask}
    (h : Bounds D cs) {b : Mask} (hb : decode b ∈ D.blocks) : Bounds D (restrict cs b) := by
  intro C hC
  obtain ⟨c, hc, rfl⟩ := h C hC
  refine ⟨c, List.mem_filter.mpr ⟨hc, (compatible_iff c b).mpr ?_⟩, rfl⟩
  by_cases heq : decode c = decode b
  · exact Or.inl heq
  · exact Or.inr (D.inter_card_lt hC hb heq)

@[expose]
def advance (cs : List Mask) (s : Mask) : List Mask :=
  if weight s = 4 then
    match options cs s with
    | [b] => restrict cs b
    | _ => cs
  else cs

theorem advance_sound (D : SteinerSystem (Fin 11) 4 5) {cs : List Mask}
    (h : Bounds D cs) (s : Mask) : Bounds D (advance cs s) := by
  unfold advance
  split
  · rename_i hs
    split
    · rename_i b hb
      obtain ⟨c, hc, hC⟩ := choose D h hs
      rw [hb] at hc
      simp only [List.mem_singleton] at hc
      subst c
      exact restrict_sound D h hC
    · exact h
  · exact h

@[expose]
def propagate : List Mask → List Mask → List Mask
  | cs, [] => cs
  | cs, s :: ss => propagate (advance cs s) ss

theorem propagate_sound (D : SteinerSystem (Fin 11) 4 5) (ss : List Mask)
    {cs : List Mask} (h : Bounds D cs) : Bounds D (propagate cs ss) := by
  induction ss generalizing cs with
  | nil => exact h
  | cons s ss ih => exact ih (advance_sound D h s)

theorem branch (D : SteinerSystem (Fin 11) 4 5) {cs : List Mask}
    (h : Bounds D cs) {s : Mask} (hs : weight s = 4) {P : Prop}
    (hb : ∀ b ∈ options cs s, Bounds D (restrict cs b) → P) : P := by
  obtain ⟨b, hmem, hB⟩ := choose D h hs
  exact hb b hmem (restrict_sound D h hB)


theorem decode_surjective : Function.Surjective decode :=
  ((Fintype.bijective_iff_injective_and_card decode).mpr
    ⟨decode_injective, by simp [Mask, Fintype.card_finset]⟩).2

@[expose]
def initial : List Mask := (List.finRange 2048).filter (fun m =>
  weight m == 5 && compatible m 31 && compatible m 103 &&
    compatible m 391 && compatible m 1543)

theorem initial_bounds (D : SteinerSystem (Fin 11) 4 5)
    (hseed : m11CompletionSeed ⊆ D.blocks) : Bounds D initial := by
  intro B hB
  obtain ⟨b, rfl⟩ := decode_surjective B
  refine ⟨b, ?_, rfl⟩
  have hc (s : Mask) (hs : s ∈ ([31, 103, 391, 1543] : List Mask)) :
      compatible b s = true := by
    apply (compatible_iff b s).mpr
    have hmem : decode s ∈ m11CompletionSeed := by
      have hh : ([31, 103, 391, 1543] : List Mask).all
          (fun m => decide (decode m ∈ m11CompletionSeed)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hh s hs)
    by_cases heq : decode b = decode s
    · exact Or.inl heq
    · exact Or.inr (D.inter_card_lt hB (hseed hmem) heq)
  simp only [initial, List.mem_filter, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
    true_and]
  exact ⟨⟨⟨⟨(decode_card b).symm.trans (D.block_card _ hB), hc 31 (by simp)⟩,
    hc 103 (by simp)⟩, hc 391 (by simp)⟩, hc 1543 (by simp)⟩

@[expose]
noncomputable def leafCheck (e : Equiv.Perm (Fin 11)) (bs : List (Mask × Fin 66)) : Bool :=
  bs.all (fun bi => decide (e • decode bi.1 = m11BlockAt bi.2))

theorem finish (D : SteinerSystem (Fin 11) 4 5) (e : Equiv.Perm (Fin 11))
    (bs : List (Mask × Fin 66)) (h : Bounds D (bs.map Prod.fst))
    (hc : leafCheck e bs = true) :
    ∃ e : Equiv.Perm (Fin 11),
      e • (D.blocks : Set (Finset (Fin 11))) =
        (m11WittDesign.blocks : Set (Finset (Fin 11))) := by
  have hsub : (D.relabel e).blocks ⊆ m11WittDesign.blocks := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hB
    obtain ⟨m, hm, rfl⟩ := h C hC
    obtain ⟨⟨m, i⟩, hmi, rfl⟩ := List.mem_map.mp hm
    have heq := of_decide_eq_true (List.all_eq_true.mp hc (m, i) hmi)
    rw [heq, m11WittDesign_blocks]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have heq := (D.relabel e).blocks_eq_of_subset m11WittDesign (by decide) hsub
  refine ⟨e, ?_⟩
  simpa only [SteinerSystem.relabel, Finset.coe_smul_finset] using
    congrArg (fun s : Finset (Finset (Fin 11)) => (s : Set (Finset (Fin 11)))) heq

end
end Sporadic.Mathieu.WittCompletion
