module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.Omega

/-!
# Normal subgroups and a unique central involution

In a finite two-group whose central omega subgroup has order two, every
nontrivial normal subgroup contains the central involution. A nontrivial
normal subgroup contains a central subgroup of order two; its inclusion
in the central omega subgroup is then an equality.

This is the normal-subgroup argument used in Janko–Thompson,
Math. Z. 113 (1970), Lemma 3.1, printed p.388.
-/

namespace IsPGroup
open Subgroup
variable {P : Type*} [Group P] [Finite P]

/-- A normal subgroup avoiding the unique central involution is trivial. -/
public theorem normal_eq_bot_of_avoiding_unique_central_involution (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (z : P) (hzC : z ∈ center P) (hz : orderOf z = 2)
    (N : Subgroup P) [N.Normal] (hzN : z ∉ N) : N = ⊥ := by
  by_contra hn
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hn
  obtain ⟨Z, _, hZN, hZcard, hZC⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  let O := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hO : Nat.card O = 2 := (card_map_of_injective (center P).subtype_injective).trans hZ
  have hZO : Z ≤ O := by
    intro x hx
    refine ⟨⟨x, hZC hx⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : Z))
    rw [hZcard] at h
    change x ^ 2 = 1
    exact congrArg Subtype.val h
  have heq : Z = O := eq_of_le_of_card_ge hZO (by omega)
  apply hzN
  apply hZN
  rw [heq]
  exact ⟨⟨z, hzC⟩, subset_closure (Subtype.ext (by simpa [hz] using pow_orderOf_eq_one z)), rfl⟩


end IsPGroup
