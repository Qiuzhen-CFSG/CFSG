module

public import Theory.GroupTheory.CentralPChiefFactors

/-!
# Chief sections at a different prime

Every section of a q-group is a q-group. If it is also a p-group for a
distinct prime p, its two prime-group structures force it to be trivial.
Thus the central p-chief-factor condition holds vacuously. This supplies
A.4.11's chief-factor hypothesis above O₂(X) when X/O₂(X) is an odd p-group.
Source: Aschbacher--Smith, proof of Lemma 3.2.13, printed pp.584--585.
-/

public section
open Subgroup

namespace Subgroup
/-- A q-group has no nontrivial p-chief sections when the primes differ. -/
theorem HasCentralPChiefFactors.of_isPGroup_of_ne
    {G : Type*} [Group G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hne : p ≠ q) (hG : IsPGroup q G) : HasCentralPChiefFactors p G := by
  intro K L hK hL hlt _ hp
  let := hK
  let := hL
  let Q := L ⧸ K.subgroupOf L
  have hq : IsPGroup q Q := (hG.to_subgroup L).to_quotient _
  have ht : (⊤ : Subgroup Q) = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p q hne _ _ (hp.to_subgroup ⊤) (hq.to_subgroup ⊤))
  have hLK : L ≤ K := by
    intro l hl
    have he : QuotientGroup.mk' (K.subgroupOf L) (⟨l, hl⟩ : L) = 1 := by
      change QuotientGroup.mk' (K.subgroupOf L) (⟨l, hl⟩ : L) ∈ (⊥ : Subgroup Q)
      rw [← ht]
      exact mem_top _
    exact (show (⟨l, hl⟩ : L) ∈ K.subgroupOf L from
      (QuotientGroup.eq_one_iff _).mp he)
  exact (hlt.not_ge hLK).elim
end Subgroup
