module

public import Theory.PPrimeCore

/-!
# Prime-complement cores under a prime-power quotient

If G/N is a p-group, every element of the p'-core of G maps trivially to
G/N: its order divides a number coprime to p. Thus the core lies in N.
If N has trivial p'-core, restricting the core to N proves it is trivial
in G as well.

This is the core argument in Glauberman, *A Characterization of the Suzuki
Groups* (1968), Proposition 2.1(ii), p. 80.
-/

open Subgroup

variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- A p-group quotient kills the p'-core. -/
public theorem pPrimeCore_le_of_isPGroup_quotient (N : Subgroup G) [N.Normal]
    (hQ : IsPGroup p (G ⧸ N)) : pPrimeCore p G ≤ N := by
  intro x hx
  apply (QuotientGroup.eq_one_iff (N := N) x).mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    (hQ.orderOf_coprime (pPrimeCore_coprime_card (p := p) (G := G))
      (QuotientGroup.mk' N x)) dvd_rfl
    ((orderOf_map_dvd (QuotientGroup.mk' N) x).trans
      ((pPrimeCore p G).orderOf_dvd_natCard hx))

/-- Triviality of the p'-core ascends across a p-group quotient. -/
public theorem pPrimeCore_eq_bot_of_isPGroup_quotient (N : Subgroup G) [N.Normal]
    (hN : pPrimeCore p N = ⊥) (hQ : IsPGroup p (G ⧸ N)) :
    pPrimeCore p G = ⊥ := by
  let O := pPrimeCore p G
  have hON : O ≤ N := pPrimeCore_le_of_isPGroup_quotient p N hQ
  have hO : O.subgroupOf N = ⊥ :=
    pPrimeCore_eq_bot_iff.mp hN _ inferInstance
      ((pPrimeCore_coprime_card (p := p) (G := G)).of_dvd_right
        (card_comap_dvd_of_injective O N.subtype N.subtype_injective))
  apply eq_bot_iff.mpr
  intro x hx
  have hxO : (⟨x, hON hx⟩ : N) ∈ O.subgroupOf N := hx
  rw [hO, mem_bot] at hxO
  exact mem_bot.mpr (congrArg Subtype.val hxO)
