module

public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.PGroup.MaximalElementaryCentralizer

/-!
# Elements of prime order centralizing a subgroup of full rank two

A rank-two subgroup contains an elementary plane. When the ambient rank
is at most two, adjoining a commuting element of exponent p cannot enlarge
that plane. Thus every such element belongs to the original subgroup.

This supplies the centralizer step of Aschbacher–Smith, *The Classification
of Quasithin Groups*, A.1.32(2), printed p.29, without a p-group assumption
on the ambient group.
-/

open Subgroup
variable {G : Type*} [Group G]

/-- A rank-two subgroup in rank at most two contains each centralizing element of exponent p. -/
public theorem Subgroup.mem_of_prime_pow_eq_one_of_centralizes_rank_two [Finite G] {p : ℕ} [Fact p.Prime]
    (hrank : primeRank p G ≤ 2) (R : Subgroup G) (hrR : primeRank p R = 2)
    {x : G} (hx : x ^ p = 1) (hcent : x ∈ centralizer (R : Set G)) : x ∈ R := by
  obtain ⟨E, hEe, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := R) (p := p)
  let := hEe
  let F := E.map R.subtype
  let : IsElementaryAbelian p F := IsElementaryAbelian.map_subtype
  have hF : Nat.card F = p ^ 2 := by
    rw [card_map_of_injective R.subtype_injective, hEc, hrR]
  have hxF : x ∈ F := mem_of_pow_eq_one_of_elementary_card_le F
    (fun A hA => hF ▸ (primeRank_le_iff_elementary_card_le G).mp hrank A hA)
    hx (fun y hy => hcent y (map_subtype_le E hy))
  exact map_subtype_le E hxF

