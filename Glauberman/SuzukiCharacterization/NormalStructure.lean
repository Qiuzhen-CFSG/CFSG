module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Glauberman.SuzukiCharacterization.NormalizerBasics
public import Glauberman.SuzukiCharacterization.NormalCore
public import Glauberman.SuzukiCharacterization.NormalSupHypotheses
public import Glauberman.SuzukiCharacterization.NormalizerFrobenius

/-!
# Normal-subgroup reductions for the Suzuki characterization

The odd alternative for a normal subgroup is equivalent to triviality because
O_{2'}(G) = 1. Thus the normal-subgroup assertion of Proposition 2.1(ii)
reduces to showing that every nontrivial normal subgroup contains P. For such
a subgroup N, the product NP inherits the hypotheses by `NormalSupHypotheses`.
Since NP/N is a two-group, the Frobenius quotient consequence from
`NormalizerFrobenius`, applied inside NP, gives P ≤ N directly.

The public imports also retain part (i): the normalizer modulo its odd core
is Frobenius, with kernel the image of P, and its complementary index q is
odd and greater than one.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Proposition 2.1, pp. 79–81, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization
open Subgroup

/-- The odd-order formulation and the nontrivial-normal-subgroup formulation
of Proposition 2.1(ii) agree under the trivial odd core. -/
public theorem Hypotheses.normal_dichotomy_iff {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) :
    (∀ N : Subgroup G, N.Normal → Nat.Coprime 2 (Nat.card N) ∨ (P : Subgroup G) ≤ N) ↔
      (∀ N : Subgroup G, N.Normal → N ≠ ⊥ → (P : Subgroup G) ≤ N) := by
  constructor
  · intro hd N hN hne
    exact (hd N hN).resolve_left fun hc => hne (h.normal_eq_bot_of_coprime P N hN hc)
  · intro hd N hN
    by_cases hne : N = ⊥
    · left
      simp [hne]
    · exact Or.inr (hd N hN hne)

/-- Proposition 2.1(ii): every nontrivial normal subgroup contains P. -/
public theorem Hypotheses.sylow_le_of_normal_ne_bot {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) (N : Subgroup G) (hN : N.Normal)
    (hne : N ≠ ⊥) : (P : Subgroup G) ≤ N := by
  let := hN
  let H := N ⊔ (P : Subgroup G)
  let PH := P.subtype (show (P : Subgroup G) ≤ H from le_sup_right)
  have hquot : IsPGroup 2 (H ⧸ N.subgroupOf H) := by
    change IsPGroup 2 (↥(N ⊔ (P : Subgroup G)) ⧸ N.subgroupOf (N ⊔ (P : Subgroup G)))
    rw [sup_comm N (P : Subgroup G)]
    exact (P.isPGroup'.to_quotient (N.subgroupOf (P : Subgroup G))).of_equiv
      (QuotientGroup.quotientInfEquivProdNormalQuotient (P : Subgroup G) N)
  have hle := (h.normalSup P N hne).sylow_le_of_quotient_isPGroup PH
    (N.subgroupOf H) hquot
  intro x hx
  exact hle (show (⟨x, (show (P : Subgroup G) ≤ H from le_sup_right) hx⟩ : H) ∈
    (PH : Subgroup H) from hx)

/-- The normal-subgroup dichotomy in Proposition 2.1(ii): a normal subgroup
has odd order or contains the Sylow two-subgroup. -/
public theorem Hypotheses.normal_dichotomy {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) :
    ∀ N : Subgroup G, N.Normal → Nat.Coprime 2 (Nat.card N) ∨ (P : Subgroup G) ≤ N :=
  (h.normal_dichotomy_iff P).mpr (h.sylow_le_of_normal_ne_bot P)

end Glauberman.SuzukiCharacterization
