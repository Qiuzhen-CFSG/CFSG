module

public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A self-centralizing prime core has trivial prime-complement core

Normal subgroups of coprime orders commute. Consequently, if the centralizer
of the prime core lies in that core, the prime-complement core lies in their
trivial intersection. This is the elementary characteristic-p implication
used in involution-centralizer recognition.
-/

namespace Theory.GroupTheory

/-- A finite group with self-centralizing p-core has trivial p'-core. -/
public theorem pPrimeCore_eq_bot_of_centralizer_pCore_le
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (h : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G) :
    pPrimeCore p G = ⊥ := by
  have hcop : Nat.Coprime (Nat.card (pCore p G)) (Nat.card (pPrimeCore p G)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := G)).pow_left n
  have hi : pCore p G ⊓ pPrimeCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hc : pPrimeCore p G ≤ Subgroup.centralizer (pCore p G : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro r hr
    have hm := Subgroup.commutator_le_inf
      (H₁ := pCore p G) (H₂ := pPrimeCore p G)
      (Subgroup.commutator_mem_commutator hr hx)
    simpa [hi] using hm
  exact le_bot_iff.mp ((le_inf (hc.trans h) le_rfl).trans_eq hi)

end Theory.GroupTheory
