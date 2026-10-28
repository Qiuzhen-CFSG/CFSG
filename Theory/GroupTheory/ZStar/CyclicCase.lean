module

public import Mathlib.GroupTheory.Transfer

/-!
# The cyclic Sylow case of the Z-star theorem

If a finite group has a cyclic Sylow two-subgroup, there is an odd-order
normal subgroup containing every commutator with any specified element.
Thus the conclusion needed for the Z-star theorem holds in this case without
an involution or isolation assumption on that element.

If the Sylow subgroup has order one, the whole group has odd order. Otherwise
two is the smallest prime divisor of the group order, and cyclicity forces
the Sylow normalizer to centralize the Sylow subgroup. Burnside's transfer
theorem then supplies a normal odd-order kernel. The transfer takes values
in the cyclic Sylow subgroup, so it kills every commutator.

This is the cyclic reduction in the Z-star development, ported from
`Submission/CyclicCase.lean` at historical commit `c3503435`. The statement
is unchanged; the proof uses the current Mathlib transfer APIs directly.
-/

open Subgroup

namespace Glauberman.ZStar

/-- A finite group with cyclic Sylow two-subgroup has an odd normal subgroup
containing all commutators with any given element. -/
public theorem cyclic_case {G : Type*} [Group G] [Finite G] (t : G)
    (S : Sylow (2 : ℕ) G) (hS_cyclic : IsCyclic (S : Subgroup G)) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases S.isPGroup'.card_eq_or_dvd with hcardS_one | hcardS_even
  · have hindex : (S : Subgroup G).index = Nat.card G := by
      simpa [hcardS_one] using (S : Subgroup G).card_mul_index
    have hodd : Odd (Nat.card G) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd, ← hindex]
      exact S.not_dvd_index
    exact ⟨⊤, inferInstance, by simpa using hodd, fun _ => mem_top _⟩
  · have hcardG_even : 2 ∣ Nat.card G :=
      hcardS_even.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup G))
    have hp : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr hcardG_even
    let : IsCyclic S := hS_cyclic
    have hNleC : normalizer (S : Subgroup G) ≤ centralizer ((S : Subgroup G) : Set G) :=
      (inferInstance : IsCyclic S).normalizer_le_centralizer hp
    let τ := MonoidHom.transferSylow S hNleC
    have hodd : Odd (Nat.card τ.ker) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact MonoidHom.not_dvd_card_ker_transferSylow S hNleC
    refine ⟨τ.ker, inferInstance, hodd, ?_⟩
    intro g
    apply τ.mem_ker.mpr
    simp only [map_mul, map_inv]
    rw [mul_comm' (τ g) (τ t)]
    simp [mul_assoc]

end Glauberman.ZStar
