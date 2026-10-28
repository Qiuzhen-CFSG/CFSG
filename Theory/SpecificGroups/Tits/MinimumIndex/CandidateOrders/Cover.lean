module

public import Theory.SpecificGroups.Tits.MinimumIndex.Candidates
public import Theory.SpecificGroups.Tits.Atlas1600OrderData

/-!
# Finite map covers for the concrete candidate subgroups

A Schreier transition table bounds the number of words by the number of
representatives times the size of the next word subgroup. For an upper bound,
the representatives may be arbitrary point maps: their membership, invertibility
and distinctness are unnecessary. Word induction constructs the cover, and
faithfulness of permutation evaluation turns the cover into a cardinal bound.

This is the covering argument of `Theory.GroupTheory.WordSubgroup`, specialized
to point maps to keep the ATLAS certificates small. The concrete consumers
are the max2, max4 and max8 programs preserved in `../source/`.
-/

namespace Tits.MinimumIndexCandidates.OrderCertificate
open Theory.GroupTheory

-- An upper bound needs a cover by maps, not invertible representatives.
public theorem card_le_of_map_transitions {V : Type*} [Fintype V] [DecidableEq V]
    {n m p : Nat}
    (gen : Fin n → Equiv.Perm V) (invOf : Fin n → Fin n)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (nextGen : Fin p → Equiv.Perm V) (nextInv : Fin p → Fin p)
    (hNextInv : ∀ i, nextGen (nextInv i) = (nextGen i)⁻¹)
    (rep : Fin m → V → V) (act : Fin n → Fin m → Fin m)
    (factor : Fin n → Fin m → List (Fin p)) (initial : Fin m)
    (hInitial : ∀ x, rep initial x = x)
    (hStep : ∀ i r x, gen i (rep r x) = rep (act i r) (evalWord nextGen (factor i r) x)) :
    Nat.card (wordSubgroup gen invOf hInv) ≤
      m * Nat.card (wordSubgroup nextGen nextInv hNextInv) := by
  classical
  let H := wordSubgroup gen invOf hInv
  let K := wordSubgroup nextGen nextInv hNextInv
  have decompose (h : H) : ∃ t : Fin m × K, ∀ x, h.val x = rep t.1 (t.2.val x) := by
    obtain ⟨w, hw⟩ := h.property
    suffices ∃ t : Fin m × K, ∀ x, evalWord gen w x = rep t.1 (t.2.val x) by
      simpa only [hw] using this
    clear hw h
    induction w with
    | nil => exact ⟨(initial, 1), fun x => (hInitial x).symm⟩
    | cons i w ih =>
      obtain ⟨⟨r, k⟩, hk⟩ := ih
      refine ⟨(act i r, ⟨evalWord nextGen (factor i r) * k.val,
        K.mul_mem ⟨factor i r, rfl⟩ k.property⟩), ?_⟩
      intro x
      change gen i (evalWord gen w x) = _
      rw [hk x, hStep]
      rfl
  let f : H → Fin m × K := fun h => (decompose h).choose
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have ha := (decompose a).choose_spec x
    have hb := (decompose b).choose_spec x
    change a.val x = rep (f a).1 ((f a).2.val x) at ha
    change b.val x = rep (f b).1 ((f b).2.val x) at hb
    rw [hab] at ha
    exact ha.trans hb.symm
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

end Tits.MinimumIndexCandidates.OrderCertificate
