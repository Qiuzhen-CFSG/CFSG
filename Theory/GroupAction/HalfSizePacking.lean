module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
# Disjoint half-size subsets and fixed points

A family of pairwise disjoint subsets, each containing half of a nonempty
finite set, has at most two members. Consequently, a permutation of the family
fixing one member fixes every member. No finiteness assumption on the indexing
type is needed: the packing itself implies finiteness.

Two distinct members exhaust the ambient set by counting. A third member would
be nonempty and disjoint from their union, which is impossible. An injective
map to `Bool` records whether a member is a chosen one.

Source: the counting argument in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript of 1 March 2004, Lemma F.4.23(4),
printed p. 287, and the fixed-point argument immediately following F.4.23.
These are the abstract counting steps; the amalgam and fiber hypotheses must
be proved separately when applying them to completions.
-/

namespace Theory.GroupAction.HalfSizePacking

variable {α ι : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
/-- Two disjoint subsets of half the ambient size exhaust the ambient set. -/
public theorem union_eq_univ [DecidableEq α] (s t : Finset α)
    (hs : 2 * s.card = Fintype.card α)
    (ht : 2 * t.card = Fintype.card α)
    (hst : Disjoint s t) : s ∪ t = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_union_of_disjoint hst]
  omega

/-- Any two distinct members of a disjoint half-size family are all its members. -/
public theorem eq_or_eq (P : ι → Finset α)
    (hsize : ∀ i, 2 * (P i).card = Fintype.card α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    {a b : ι} (hab : a ≠ b) (i : ι) : i = a ∨ i = b := by
  classical
  by_contra h
  have hia : i ≠ a := fun hi => h (Or.inl hi)
  have hib : i ≠ b := fun hi => h (Or.inr hi)
  have hc := Fintype.card_pos (α := α)
  have hi := hsize i
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (P i).card by omega)
  have hcover := union_eq_univ (P a) (P b) (hsize a) (hsize b) (hdisj hab)
  have hxcover : x ∈ P a ∪ P b := by rw [hcover]; exact Finset.mem_univ x
  rcases Finset.mem_union.mp hxcover with hxa | hxb
  · exact Finset.disjoint_left.mp (hdisj hia) hx hxa
  · exact Finset.disjoint_left.mp (hdisj hib) hx hxb

/-- A disjoint family of half-size subsets is finite and has at most two members. -/
public theorem finite_and_card_le_two (P : ι → Finset α)
    (hsize : ∀ i, 2 * (P i).card = Fintype.card α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Finite ι ∧ Nat.card ι ≤ 2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨inferInstance, by simp⟩
  | inr h =>
    obtain ⟨a⟩ := h
    let f : ι → Bool := fun i => decide (i = a)
    have hf : Function.Injective f := by
      intro i j hij
      by_cases hia : i = a
      · have hja : j = a := by simpa [f, hia] using hij.symm
        exact hia.trans hja.symm
      · have hja : j ≠ a := by simpa [f, hia] using hij.symm
        exact ((eq_or_eq P hsize hdisj hia j).resolve_right hja).symm
    refine ⟨Finite.of_injective f hf, ?_⟩
    simpa using Nat.card_le_card_of_injective f hf

/-- A group element permuting a half-size family and fixing one index fixes all indices. -/
public theorem fixed_of_fixed {K : Type*} [Group K] [MulAction K ι]
    (P : ι → Finset α)
    (hsize : ∀ i, 2 * (P i).card = Fintype.card α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (a : ι) (g : K) (hfix : g • a = a) (i : ι) : g • i = i := by
  by_cases hia : i = a
  · simpa [hia] using hfix
  · have hne : g • i ≠ a := by
      intro hi
      exact hia (MulAction.injective g (hi.trans hfix.symm))
    exact (eq_or_eq P hsize hdisj hia (g • i)).resolve_right hne

end Theory.GroupAction.HalfSizePacking
