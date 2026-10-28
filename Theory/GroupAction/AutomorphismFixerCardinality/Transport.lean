module

public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Cardinal bounds for automorphism fixers under isomorphisms

Conjugating automorphisms by a group isomorphism identifies their action on
corresponding subgroups. Mapping an acting subgroup preserves its cardinality,
so any bound for the pointwise fixer transfers through the actual isomorphism.
This is the transport step for the small-model bounds in Aschbacher–Smith,
E.6.8(5), printed p.248.
-/

open Subgroup
namespace Theory.GroupAction
public theorem automorphism_fixer_card_le_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (P : Subgroup X) (Q : Subgroup Y) (hPQ : P.map e.toMonoidHom = Q)
    (n : ℕ) (hbound : ∀ B : Subgroup (MulAut Y),
      (∀ α ∈ B, ∀ x ∈ Q, α x = x) → Nat.card B ≤ n)
    (A : Subgroup (MulAut X)) (hfix : ∀ α ∈ A, ∀ x ∈ P, α x = x) : Nat.card A ≤ n := by
  let B := A.map (MulAut.congr e).toMonoidHom
  have hB : ∀ α ∈ B, ∀ x ∈ Q, α x = x := by
    rintro _ ⟨α, hα, rfl⟩ x hx
    rw [← hPQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hfix α hα y hy]
  calc
    Nat.card A = Nat.card B :=
      (card_map_of_injective (K := A) (MulAut.congr e).injective).symm
    _ ≤ n := hbound B hB
end Theory.GroupAction
