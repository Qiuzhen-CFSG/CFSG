module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Finite certificates for binary elementary action bounds

A binary elementary group gives a commuting set of power-of-two cardinality.
Branching on membership of an actor restricts the possible actors to its
commuting set and the possible common fixed points to its fixed set. At a
leaf, the next power of two above the actor count sharpens that count.
The checker below proves a bound on the product of the two cardinalities.

This elementary counting argument is used for the literal J₄ max1 action,
in the two-rank estimate cited before Aschbacher–Smith G.7.1, printed p.347.
The finite relations are parameters; a consumer must prove their connection
to its actual group and action.
-/

@[expose] public section
namespace Theory.GroupAction.BinaryCliqueFixedBound

/-- A branching certificate, with a power-of-two actor bound at each leaf. -/
inductive Tree (α : Type) where
  | leaf : ℕ → Tree α
  | branch : α → Tree α → Tree α → Tree α

variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- The negative branch removes an actor; the positive branch restricts both sets. -/
def check (commute : α → α → Bool) (fixed : α → β → Bool) (bound : ℕ) :
    Tree α → List α → List β → Bool
  | .leaf n, u, f => decide (u.length < 2 ^ (n + 1) ∧ 2 ^ n * f.length ≤ bound)
  | .branch v l r, u, f =>
      check commute fixed bound l (u.filter (fun w => w != v)) f &&
      check commute fixed bound r (u.filter (commute v)) (f.filter (fixed v))

private theorem card_le_length (s : Finset α) (u : List α)
    (h : ∀ x ∈ s, x ∈ u) : s.card ≤ u.length :=
  (Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (h x hx))).trans
    (List.toFinset_card_le u)

/-- Soundness uses the actual commuting and fixed relations, and the binary order. -/
theorem check_sound (commute : α → α → Bool) (fixed : α → β → Bool) (bound : ℕ)
    (t : Tree α) (u : List α) (f : List β)
    (ht : check commute fixed bound t u f = true)
    (s : Finset α) (z : Finset β)
    (hs : ∀ v ∈ s, v ∈ u) (hz : ∀ m ∈ z, m ∈ f)
    (hp : ∃ k : ℕ, s.card = 2 ^ k)
    (hc : ∀ v ∈ s, ∀ w ∈ s, commute v w = true)
    (hf : ∀ v ∈ s, ∀ m ∈ z, fixed v m = true) :
    s.card * z.card ≤ bound := by
  induction t generalizing u f with
  | leaf n =>
    have ⟨hu, hbound⟩ : u.length < 2 ^ (n + 1) ∧ 2 ^ n * f.length ≤ bound :=
      of_decide_eq_true ht
    obtain ⟨k, hk⟩ := hp
    have hklt : k < n + 1 := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      exact lt_of_le_of_lt (hk ▸ card_le_length s u hs) hu
    have hle : s.card ≤ 2 ^ n := by
      rw [hk]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.mul_le_mul hle (card_le_length z f hz)).trans hbound
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ :
        check commute fixed bound l (u.filter (fun w => w != v)) f = true ∧
        check commute fixed bound r (u.filter (commute v)) (f.filter (fixed v)) = true := by
      simpa only [check, Bool.and_eq_true] using ht
    by_cases hv : v ∈ s
    · apply ihr _ _ hr
      · exact fun w hw => List.mem_filter.mpr ⟨hs w hw, hc v hv w hw⟩
      · exact fun m hm => List.mem_filter.mpr ⟨hz m hm, hf v hv m hm⟩
    · apply ihl _ _ hl
      · intro w hw
        apply List.mem_filter.mpr
        exact ⟨hs w hw, by simpa only [bne_iff_ne] using
          (show w ≠ v by rintro rfl; exact hv hw)⟩
      · exact hz

end Theory.GroupAction.BinaryCliqueFixedBound
