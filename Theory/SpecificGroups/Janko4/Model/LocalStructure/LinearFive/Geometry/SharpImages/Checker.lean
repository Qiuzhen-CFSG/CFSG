module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Checker

/-!
# Strict elementary product bounds with an octad exception

A branching certificate either bounds the product of clique size and common
fixed space strictly below 1024, or puts every actor in a specified set. The
native application identifies that exceptional set with an octad kernel.
This refines the elementary product bound for the occurrence argument in
Kleidman--Wilson (1988), Lemma 1.1.2(ii).
-/
@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages
open ElementaryNormalizerCover.ElementaryBound

inductive Tree where
  | small : Tree
  | octad : Tree
  | bound : ℕ → List ℕ → Tree
  | branch : Fin 192 → Tree → Tree → Tree

def check (keep : Fin 192 → Bool) (neighbors masks : Fin 192 → ℕ) : Tree → List (Fin 192) → ℕ → Bool
  | .small, u, _ => decide (u.length < 2)
  | .octad, u, _ => u.all keep
  | .bound k bs, u, w => decide
      (u.length < 2 ^ (k+1) ∧ w = encode (sums bs) ∧ 2 ^ k * 2 ^ bs.length < 1024)
  | .branch v l r, u, w =>
      check keep neighbors masks l (u.filter (fun a => a != v)) w &&
      check keep neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
        (w &&& masks v)

theorem check_sound (keep : Fin 192 → Bool) (neighbors masks : Fin 192 → ℕ)
    (t : Tree) (u : List (Fin 192)) (w : ℕ)
    (ht : check keep neighbors masks t u w = true)
    (s : Finset (Fin 192)) (a : Finset (Fin 2048))
    (hs : ∀ v ∈ s, v ∈ u) (ha : ∀ m ∈ a, w.testBit m.val = true)
    (hne : 2 ≤ s.card) (hpow : ∃ d, s.card = 2 ^ d)
    (hc : ∀ v ∈ s, ∀ v' ∈ s, (neighbors v).testBit v'.val = true)
    (hf : ∀ v ∈ s, ∀ m ∈ a, (masks v).testBit m.val = true) :
    s.card * a.card < 1024 ∨ ∀ v ∈ s, keep v = true := by
  have hslen (u : List (Fin 192)) (hs : ∀ v ∈ s, v ∈ u) : s.card ≤ u.length :=
    (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hs v hv))).trans
      (List.toFinset_card_le u)
  induction t generalizing u w with
  | small =>
    have hlt : u.length < 2 := of_decide_eq_true ht
    have := hslen u hs
    omega
  | octad =>
    exact Or.inr (fun v hv => List.all_eq_true.mp ht v (hs v hv))
  | bound k bs =>
    have hb : u.length < 2 ^ (k+1) ∧ w = encode (sums bs) ∧
        2 ^ k * 2 ^ bs.length < 1024 := of_decide_eq_true ht
    obtain ⟨d, hd⟩ := hpow
    have hdlt : 2 ^ d < 2 ^ (k+1) := hd ▸ (hslen u hs).trans_lt hb.1
    have hdle : d ≤ k := by
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hdlt
      omega
    have hsc : s.card ≤ 2 ^ k := hd ▸ Nat.pow_le_pow_right (by decide) hdle
    have hac : a.card ≤ 2 ^ bs.length := card_le_sums a bs (hb.2.1 ▸ ha)
    exact Or.inl ((Nat.mul_le_mul hsc hac).trans_lt hb.2.2)
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

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages
