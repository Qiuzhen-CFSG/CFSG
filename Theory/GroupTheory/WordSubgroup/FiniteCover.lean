module

public import Theory.GroupTheory.WordSubgroup

/-!
# Upper bounds from word-subgroup transitions

A family of representatives containing the identity covers a word subgroup
when multiplying a representative by any generator reduces to another
representative times a word in a smaller subgroup. Induction on words gives
the cover and hence a cardinality bound. Unlike an exact Schreier index, this
bound needs neither an action nor a proof that the representatives are distinct.

This is the surjective part of `wordSubgroup_card_eq_mul_next`, separated so
matrix certificates can use it without first constructing a faithful permutation
representation. The certificate equalities hold in the actual ambient group.
-/

namespace Theory.GroupTheory

/-- A Schreier reduction table gives an upper bound even without a separating
action on its representatives. -/
public theorem wordSubgroup_card_le_mul_next {G : Type*} [Group G] [Finite G]
    {n m p : Nat}
    (gen : Fin n → G) (invOf : Fin n → Fin n)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (nextGen : Fin p → G) (nextInvOf : Fin p → Fin p)
    (hNextInv : ∀ i, nextGen (nextInvOf i) = (nextGen i)⁻¹)
    (rep : Fin m → G) (act : Fin n → Fin m → Fin m)
    (factor : Fin n → Fin m → List (Fin p)) (baseRep : Fin m)
    (hRepMem : ∀ r, rep r ∈ wordSubgroup gen invOf hInv)
    (hNextLe : wordSubgroup nextGen nextInvOf hNextInv ≤ wordSubgroup gen invOf hInv)
    (hRepBase : rep baseRep = 1)
    (hStep : ∀ i r,
      gen i * rep r = rep (act i r) * evalWord nextGen (factor i r)) :
    Nat.card (wordSubgroup gen invOf hInv) ≤
      m * Nat.card (wordSubgroup nextGen nextInvOf hNextInv) := by
  let H := wordSubgroup gen invOf hInv
  let K := wordSubgroup nextGen nextInvOf hNextInv
  have hDecomp : ∀ w : List (Fin n), ∃ r : Fin m, ∃ k : K,
      evalWord gen w = rep r * (k : G) := by
    intro w
    induction w with
    | nil =>
      exact ⟨baseRep, 1, by simp [evalWord, hRepBase]⟩
    | cons i w ih =>
      obtain ⟨r, k, hk⟩ := ih
      refine ⟨act i r, ⟨evalWord nextGen (factor i r) * (k : G),
        K.mul_mem ⟨factor i r, rfl⟩ k.property⟩, ?_⟩
      change gen i * evalWord gen w =
        rep (act i r) * (evalWord nextGen (factor i r) * (k : G))
      rw [hk, ← mul_assoc, hStep, mul_assoc]
  let coverMap : Fin m × K → H := fun x =>
    ⟨rep x.1 * (x.2 : G), H.mul_mem (hRepMem x.1) (hNextLe x.2.property)⟩
  have hsurj : Function.Surjective coverMap := by
    intro h
    obtain ⟨w, hw⟩ := h.property
    obtain ⟨r, k, hk⟩ := hDecomp w
    exact ⟨(r, k), Subtype.ext (hk.symm.trans hw)⟩
  simpa only [Nat.card_prod, Nat.card_fin] using
    Nat.card_le_card_of_surjective coverMap hsurj

end Theory.GroupTheory
