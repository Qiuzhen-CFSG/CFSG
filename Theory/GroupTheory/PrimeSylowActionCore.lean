module

public import Theory.GroupTheory.Fitting.Centralizer

/-!
# A Sylow five-action forces a self-centralizing two-core

In a finite solvable group of order `10240 = 2^11 * 5`, a Sylow
five-subgroup that does not centralize the two-core forces the centralizer
of the two-core to lie in the two-core.

The odd core has order dividing five. If its order were five, normality
would identify it with the supplied Sylow subgroup. The normal odd core
and two-core are disjoint, so they commute, contradicting the action
hypothesis. Thus the odd core is trivial. The Fitting subgroup is then
the two-core, and solvable Fitting self-centralization gives the result.

This is the intrinsic finite-group argument used in the Sylow paragraph
of Parrott, *A characterization of the Tits' simple group* (1972), Lemma 1,
p. 672. Its application obtains order `10240` from the order-512 two-core
and its order-20 quotient. No ambient recognition or model hypothesis is
part of this criterion.
-/

namespace Subgroup

/-- A nontrivial Sylow five-action makes the two-core self-centralizing
in a solvable group of order `10240`. -/
public theorem centralizer_pCore_le_of_prime_sylow_action
    {H : Type*} [Group H] [Finite H]
    (hsolv : Group.IsSolvable H) (hcard : Nat.card H = 10240)
    (P : Sylow 5 H)
    (haction : ¬ pCore 2 H ≤ centralizer (P : Set H)) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    decide +kernel
  have hoddcore : pPrimeCore 2 H = ⊥ := by
    let O := pPrimeCore 2 H
    have hcop : Nat.Coprime (Nat.card O) (2 ^ 11) :=
      (pPrimeCore_coprime_card (p := 2) (G := H)).symm.pow_right 11
    have hdiv : Nat.card O ∣ 2 ^ 11 * 5 := by
      simpa only [hcard, show 2 ^ 11 * 5 = 10240 by norm_num]
        using O.card_subgroup_dvd_card
    have hdiv5 : Nat.card O ∣ 5 := hcop.dvd_of_dvd_mul_left hdiv
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdiv5 with hone | hfive
    · exact Subgroup.card_eq_one.mp hone
    · have hO5 : IsPGroup 5 O := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hfive)
      have hOP : O = (P : Subgroup H) :=
        eq_of_le_of_card_ge (hO5.le_sylow_of_normal P) (by simp only [hfive, hPcard, le_refl])
      have hdis : Disjoint (pCore 2 H) O :=
        IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup hO5
      have hcent : pCore 2 H ≤ centralizer (O : Set H) :=
        commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
      exact (haction (by simpa only [hOP, P.coe_coe] using hcent)).elim
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 hoddcore
  rw [← hfit]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

end Subgroup
