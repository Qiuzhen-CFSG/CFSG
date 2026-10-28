module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Checker

/-!
# Certifying a common fixed octad for large Mathieu fixed spaces

The branching check retains every actor of an elementary subgroup and every
common fixed mask. Each leaf has fewer than four actors, fewer than 64 fixed
masks, or places all actors in one explicitly marked octad kernel.
Binary spans certify mask bounds; no enumeration of the ambient J₄ is used.
Source: the local-radical strategy of An--O'Brien--Wilson (2003), §4, p.122.
-/
@[expose] public section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
open ElementaryNormalizerCover.ElementaryBound

inductive Tree where
  | small : Tree
  | octad : Fin 39 → Tree
  | bound : List ℕ → Tree
  | branch : Fin 192 → Tree → Tree → Tree

def check (keep : Fin 39 → Fin 192 → Bool) (neighbors masks : Fin 192 → ℕ) :
    Tree → List (Fin 192) → ℕ → Bool
  | .small, u, _ => decide (u.length < 4)
  | .octad i, u, _ => u.all (keep i)
  | .bound bs, _, w => decide (w = encode (sums bs) ∧ bs.length < 6)
  | .branch v l r, u, w =>
      check keep neighbors masks l (u.filter (fun a => a != v)) w &&
      check keep neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
        (w &&& masks v)

theorem check_sound (keep : Fin 39 → Fin 192 → Bool) (neighbors masks : Fin 192 → ℕ)
    (t : Tree) (u : List (Fin 192)) (w : ℕ)
    (ht : check keep neighbors masks t u w = true)
    (s : Finset (Fin 192)) (a : Finset (Fin 2048))
    (hs : ∀ v ∈ s, v ∈ u) (ha : ∀ m ∈ a, w.testBit m.val = true)
    (hc : ∀ v ∈ s, ∀ v' ∈ s, (neighbors v).testBit v'.val = true)
    (hf : ∀ v ∈ s, ∀ m ∈ a, (masks v).testBit m.val = true) :
    s.card < 4 ∨ a.card < 64 ∨ ∃ i, ∀ v ∈ s, keep i v = true := by
  induction t generalizing u w with
  | small =>
    have hlt : u.length < 4 := of_decide_eq_true ht
    exact Or.inl ((Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hs v hv))).trans_lt
      ((List.toFinset_card_le u).trans_lt hlt))
  | octad i =>
    exact Or.inr (Or.inr ⟨i, fun v hv => List.all_eq_true.mp ht v (hs v hv)⟩)
  | bound bs =>
    have hb : w = encode (sums bs) ∧ bs.length < 6 := of_decide_eq_true ht
    have hac : a.card ≤ 2 ^ bs.length := card_le_sums a bs (hb.1 ▸ ha)
    exact Or.inr (Or.inl (hac.trans_lt
      (show 2 ^ bs.length < 2 ^ 6 from Nat.pow_lt_pow_right (by decide) hb.2)))
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ : check keep neighbors masks l (u.filter (fun a => a != v)) w = true ∧
        check keep neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
          (w &&& masks v) = true := by
      simpa only [check, Bool.and_eq_true] using ht
    by_cases hv : v ∈ s
    · apply ihr _ _ hr
      · intro v' hv'
        exact List.mem_filter.mpr ⟨hs v' hv', hc v hv v' hv'⟩
      · intro m hm
        rw [Nat.testBit_land, ha m hm, hf v hv m hm]
        rfl
    · apply ihl _ _ hl
      · intro v' hv'
        exact List.mem_filter.mpr ⟨hs v' hv', by
          simpa only [bne_iff_ne] using (show v' ≠ v by rintro rfl; exact hv hv')⟩
      · exact ha
end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
