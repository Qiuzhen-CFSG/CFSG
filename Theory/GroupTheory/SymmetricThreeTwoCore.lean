module

public import Theory.PGroupCore
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-!
# Two-group kernels with symmetric-three quotient

A surjection onto S₃ with a two-group kernel has kernel equal to the
actual two-core: a normal two-subgroup of S₃ would be central of order two,
whereas S₃ has trivial center.

This elementary extension calculation is used for the local second
centralizer in Parrott (1972), §4, pp.682–683.
-/

open Subgroup

private theorem normal_two_perm_three_eq_bot
    (P : Subgroup (Equiv.Perm (Fin 3))) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdiv : Nat.card P ∣ 6 := hperm ▸ P.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hdiv2 : Nat.card P ∣ 2 := hcop.dvd_mul_right.mp hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · have hc := central_of_normal_card_two P h2
    have hh : ∀ x : Equiv.Perm (Fin 3), (∀ y, y * x = x * y) → x = 1 := by
      decide +kernel
    apply le_antisymm _ bot_le
    intro x hx
    exact hh x (mem_center_iff.mp (hc hx))

/-- A surjection onto S₃ with a two-group kernel identifies the actual two-core. -/
public theorem ker_eq_twoCore_of_surjective_perm_three
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : f.ker = pCore 2 G := by
  have hle : f.ker ≤ pCore 2 G := le_sSup ⟨inferInstance, hk⟩
  apply le_antisymm hle
  have : ((pCore 2 G).map f).Normal := (inferInstance : (pCore 2 G).Normal).map f hf
  exact (Subgroup.map_eq_bot_iff _).mp
    (normal_two_perm_three_eq_bot _ (pCore_isPGroup.map f))

