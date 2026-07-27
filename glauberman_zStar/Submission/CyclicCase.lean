import Mathlib
open Subgroup

namespace Submission.CyclicCase

/-- If a Sylow 2-subgroup S of G is cyclic, then the Z*-theorem holds. -/
theorem cyclic_case {G : Type*} [Group G] [Finite G] (t : G)
    (S : Sylow (2 : ℕ) G) (hS_cyclic : IsCyclic (S : Subgroup G)) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  rcases S.isPGroup'.card_eq_or_dvd with (hcardS_one | hcardS_even)
  · -- |S| = 1, so |G| is odd.  Take N = G.
    have hcardG_odd : ¬ 2 ∣ Nat.card G := by
      have hindex_eq : (S : Subgroup G).index = Nat.card G := by
        have := (S : Subgroup G).card_mul_index
        rw [hcardS_one, one_mul] at this
        exact this
      intro h2
      apply S.not_dvd_index
      rw [hindex_eq]
      exact h2
    have h_card_odd : Odd (Nat.card (⊤ : Subgroup G)) := by
      have hcard_top : Nat.card (⊤ : Subgroup G) = Nat.card G := by simp
      rw [hcard_top]
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact hcardG_odd
    refine ⟨⊤, Subgroup.normal_top, h_card_odd, ?_⟩
    intro g
    trivial

  · -- 2 ∣ |S|, so 2 ∣ |G|.  Use Burnside's normal p-complement theorem.
    have hcardG_even : 2 ∣ Nat.card G :=
      hcardS_even.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup G))
    have hp : (Nat.card G).minFac = (2 : ℕ) := (Nat.minFac_eq_two_iff _).mpr hcardG_even

    -- Lift the cyclic hypothesis to the Sylow type
    have hS_cyclic' : IsCyclic (S : Sylow (2 : ℕ) G) := by
      obtain ⟨g, hg⟩ := hS_cyclic
      refine ⟨⟨(g : G), g.2⟩, ?_⟩
      intro x
      have hx_mem : (x : G) ∈ (S : Subgroup G) := x.2
      obtain ⟨n, hn⟩ := hg ⟨(x : G), hx_mem⟩
      refine ⟨n, ?_⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val hn

    -- For a cyclic Sylow subgroup, N_G(S) = C_G(S).
    have hNleC : normalizer (S : Subgroup G) ≤ centralizer ((S : Subgroup G) : Set G) :=
      hS_cyclic'.normalizer_le_centralizer hp

    -- Elements of S commute (since S is cyclic, hence abelian).
    have hS_comm (a b : (S : Subgroup G)) : (a : G) * (b : G) = (b : G) * (a : G) := by
      have ha_norm : (a : G) ∈ normalizer (S : Subgroup G) := le_normalizer a.2
      have ha_cent : (a : G) ∈ centralizer ((S : Subgroup G) : Set G) := hNleC ha_norm
      exact (ha_cent (b : G) b.2).symm

    -- Burnside's normal p-complement theorem via the transfer homomorphism.
    let τ := MonoidHom.transferSylow S hNleC
    let K := τ.ker

    have h_comp : IsComplement' K (S : Subgroup G) :=
      MonoidHom.ker_transferSylow_isComplement' S hNleC

    -- |K| is not divisible by 2, hence is odd.
    have h_not_dvd : ¬ 2 ∣ Nat.card K :=
      MonoidHom.not_dvd_card_ker_transferSylow S hNleC
    have hK_odd : Odd (Nat.card K) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h_not_dvd

    -- All commutators [g,t] lie in K because τ([g,t]) = 1.
    have h_comm : ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ K := by
      intro g
      apply τ.mem_ker.mpr
      apply Subtype.ext
      calc
        ((τ (g * t * g⁻¹ * t⁻¹) : (S : Subgroup G)) : G) =
            ((τ g * τ t * τ (g⁻¹) * τ (t⁻¹) : (S : Subgroup G)) : G) := by
          simp [map_mul]
        _ = ((τ g : G) * (τ t : G) * ((τ g : G)⁻¹) * ((τ t : G)⁻¹)) := by
          simp
        _ = ((τ g : G) * ((τ g : G)⁻¹)) * ((τ t : G) * ((τ t : G)⁻¹)) := by
          have h_swap : (τ t : G) * ((τ g : G)⁻¹) = ((τ g : G)⁻¹) * (τ t : G) := by
            simpa using hS_comm (τ t) ((τ g)⁻¹)
          calc
            (τ g : G) * (τ t : G) * ((τ g : G)⁻¹) * ((τ t : G)⁻¹) =
                (τ g : G) * ((τ t : G) * ((τ g : G)⁻¹)) * ((τ t : G)⁻¹) := by group
            _ = (τ g : G) * (((τ g : G)⁻¹) * (τ t : G)) * ((τ t : G)⁻¹) := by
              rw [h_swap]
            _ = ((τ g : G) * ((τ g : G)⁻¹)) * ((τ t : G) * ((τ t : G)⁻¹)) := by group
        _ = (1 : G) * (1 : G) := by simp
        _ = (1 : G) := by simp
        _ = ((1 : (S : Subgroup G)) : G) := by simp

    refine ⟨K, inferInstance, hK_odd, h_comm⟩

end Submission.CyclicCase
