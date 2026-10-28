module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Core
public import Mathlib.Data.Nat.Bitwise

/-!
# A checked product bound from commuting vertices and fixed masks

A branching certificate retains all possible group elements and intersects the
binary masks fixed by selected elements. At a leaf, a short list of binary
generators covers the remaining masks. Their binary sums give a cardinality
upper bound without requiring independence. Power-of-two order then bounds the
product of the subgroup order and its common fixed space.

This is the finite checker for the native Mathieu action used in
Kleidman--Wilson (1988), Lemma 1.1.2(i).
-/
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound

/-- All binary sums of a list of masks; independence is unnecessary for an upper bound. -/
def sums : List ℕ → List ℕ
  | [] => [0]
  | b :: bs => sums bs ++ (sums bs).map (fun m => b ^^^ m)

theorem length_sums (bs : List ℕ) : (sums bs).length = 2 ^ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [sums, List.length_append, List.length_map, ih,
      List.length_cons, pow_succ]; omega

def encode : List ℕ → ℕ
  | [] => 0
  | m :: ms => 2 ^ m ||| encode ms

theorem testBit_encode (ms : List ℕ) (m : ℕ) :
    (encode ms).testBit m = true ↔ m ∈ ms := by
  induction ms with
  | nil => simp [encode]
  | cons a ms ih =>
    simp only [encode, Nat.testBit_lor, Bool.or_eq_true,
      Nat.testBit_two_pow, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem card_le_sums (a : Finset (Fin 2048)) (bs : List ℕ)
    (h : ∀ m ∈ a, (encode (sums bs)).testBit m.val = true) :
    a.card ≤ 2 ^ bs.length := by
  calc
    a.card = (a.image Fin.val).card := (Finset.card_image_of_injective a Fin.val_injective).symm
    _ ≤ (sums bs).toFinset.card := Finset.card_le_card (by
      intro m hm
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
      exact List.mem_toFinset.mpr ((testBit_encode _ _).mp (h v hv)))
    _ ≤ (sums bs).length := List.toFinset_card_le _
    _ = _ := length_sums bs

inductive Tree where
  | small : Tree
  | bound : ℕ → List ℕ → Tree
  | branch : Fin 192 → Tree → Tree → Tree

def check (neighbors masks : Fin 192 → ℕ) : Tree → List (Fin 192) → ℕ → Bool
  | .small, u, _ => decide (u.length < 2)
  | .bound k bs, u, w => decide
      (u.length < 2 ^ (k+1) ∧ w = encode (sums bs) ∧ 2 ^ k * 2 ^ bs.length ≤ 1024)
  | .branch v l r, u, w =>
      check neighbors masks l (u.filter (fun a => a != v)) w &&
      check neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
        (w &&& masks v)

theorem check_sound (neighbors masks : Fin 192 → ℕ)
    (t : Tree) (u : List (Fin 192)) (w : ℕ)
    (ht : check neighbors masks t u w = true)
    (s : Finset (Fin 192)) (a : Finset (Fin 2048))
    (hs : ∀ v ∈ s, v ∈ u) (ha : ∀ m ∈ a, w.testBit m.val = true)
    (hne : 2 ≤ s.card) (hpow : ∃ d, s.card = 2 ^ d)
    (hc : ∀ v ∈ s, ∀ v' ∈ s, (neighbors v).testBit v'.val = true)
    (hf : ∀ v ∈ s, ∀ m ∈ a, (masks v).testBit m.val = true) :
    s.card * a.card ≤ 1024 := by
  have hslen (u : List (Fin 192)) (hs : ∀ v ∈ s, v ∈ u) : s.card ≤ u.length :=
    (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hs v hv))).trans
      (List.toFinset_card_le u)
  induction t generalizing u w with
  | small =>
    have hlt : u.length < 2 := of_decide_eq_true ht
    have := hslen u hs
    omega
  | bound k bs =>
    have hb : u.length < 2 ^ (k+1) ∧ w = encode (sums bs) ∧
        2 ^ k * 2 ^ bs.length ≤ 1024 := of_decide_eq_true ht
    obtain ⟨d, hd⟩ := hpow
    have hdlt : 2 ^ d < 2 ^ (k+1) := hd ▸ (hslen u hs).trans_lt hb.1
    have hdle : d ≤ k := by
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hdlt
      omega
    have hsc : s.card ≤ 2 ^ k := hd ▸ Nat.pow_le_pow_right (by decide) hdle
    have hac : a.card ≤ 2 ^ bs.length := card_le_sums a bs (hb.2.1 ▸ ha)
    exact (Nat.mul_le_mul hsc hac).trans hb.2.2
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ : check neighbors masks l (u.filter (fun a => a != v)) w = true ∧
        check neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
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

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
