module

public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Characteristic p descends through central kernels

A finite group with self-centralizing p-core retains that property under a
surjection with central kernel. In the preimage of the target core's
centralizer, an element of prime order different from p acts quadratically
on the source p-core. Coprime commutator idempotence makes that action
trivial, contradicting self-centralization. Cauchy's theorem therefore
makes the preimage a p-group, and its image lies in the target p-core.

This is the central-quotient step in the characteristic-two descent used
by Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138. No characteristic-p assumption on the target is used.
-/

public section
open Subgroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]
  {p : ℕ} [Fact p.Prime]

private theorem prime_order_preimage_centralizer
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (x : (centralizer (pCore p H : Set H)).comap f)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (ho : orderOf x = q) : False := by
  let Q := pCore p G
  let R := zpowers (x : G)
  have hmap : Q.map f ≤ pCore p H :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  have hR : R.map f ≤ centralizer (Q.map f : Set H) := by
    rw [map_zpowers]
    apply zpowers_le.mpr
    exact centralizer_le hmap x.property
  have hQR : ⁅Q, R⁆ ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hR
  have hquad : ⁅⁅Q, R⁆, R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((hQR.trans hk).trans (center_le_centralizer _))
  have hRcard : Nat.card R = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho]
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    rw [hRcard, hn]
    exact ((hq.coprime_iff_not_dvd).mpr
      (fun hd => hqp ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hq.ne_one))).pow_right n
  let : Group.IsNilpotent Q := (pCore_isPGroup (p := p) (G := G)).isNilpotent
  have hbot := commutator_eq_bot_of_coprime_quadratic Q R
    le_normalizer_of_normal (inferInstance : Group.IsSolvable Q) hcop hquad
  have hxQ : (x : G) ∈ Q := hc
    ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] : ⁅R, Q⁆ = ⊥))
      (mem_zpowers _))
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_orderOf_dvd_pow ⟨x, hxQ⟩
  have hd : q ∣ p ^ n := by
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe x, ho] using hn
  exact hqp ((Nat.dvd_prime Fact.out).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

/-- A central quotient of a finite group of characteristic p has characteristic p. -/
theorem centralizer_pCore_le_of_surjective_centralKernel
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G) :
    centralizer (pCore p H : Set H) ≤ pCore p H := by
  let C := (centralizer (pCore p H : Set H)).comap f
  have hCp : IsPGroup p C := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    by_cases he : q = p
    · subst q
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q (hp := ⟨hqprime⟩) hqdvd
      exact (prime_order_preimage_centralizer f hf hk hc x hqprime he hx).elim
  have hm : C.map f = centralizer (pCore p H : Set H) :=
    map_comap_eq_self_of_surjective hf _
  exact le_sSup ⟨inferInstance, hm ▸ hCp.map f⟩
end MonoidHom

end
