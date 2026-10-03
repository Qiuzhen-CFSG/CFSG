module
public import Stellmacher.SectionOne.LemmaOneFive

/-!
# The odd-core commutator of an involution

In a finite solvable group with trivial 2-core, every involution acts
nontrivially on the odd core, and its commutator with that core has odd order.
These facts supply the nontrivial coprime subgroup in the reduction of
Stellmacher (1.3), before restricting the faithful module action.

The proof embeds the involution in a Sylow 2-subgroup and applies the
Fitting-centralizer argument exported by LemmaOneFive. A commutator subgroup
inside the normal odd core inherits its coprime cardinality.
Source: refs/latex/stellmacher-n-group.tex, proof of (1.3), journal pp.15–16.
-/

namespace Stellmacher.SectionOne

universe u v

public theorem oddCore_involution_commutator_ne_bot
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (x : G) (hx : IsInvolution x) :
    ⁅oddCore G, Subgroup.zpowers x⁆ ≠ ⊥ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
  have hXp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.iff_card.mpr
    exact ⟨1, by simpa using hcard⟩
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  intro hbot
  have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (oddCore G : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa [Subgroup.commutator_comm] using hbot
  have hxmem : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (oddCore G : Set G) :=
    ⟨hXS (Subgroup.mem_zpowers x), hcent (Subgroup.mem_zpowers x)⟩
  rw [lemma_one_five_sylow_oddCore_centralizer_bot h S] at hxmem
  exact hx.1 hxmem

public theorem oddCore_involution_commutator_coprime
    {G : Type u} [Group G] [Finite G] (x : G) :
    Nat.Coprime 2 (Nat.card (⁅oddCore G, Subgroup.zpowers x⁆ : Subgroup G)) := by
  let : (oddCore G).Normal := pPrimeCore_normal
  have hle : ⁅oddCore G, Subgroup.zpowers x⁆ ≤ oddCore G :=
    Subgroup.commutator_le_left _ _
  exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
    (Subgroup.card_dvd_of_le hle)

end Stellmacher.SectionOne

