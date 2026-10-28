module

public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.AutomorphismFixedSubgroup
import Mathlib.Tactic.IntervalCases

/-!
# A fixed plane for an extraspecial group with a commuting inverter

Let G be actually isomorphic to the prime Heisenberg group, for an odd prime p.
An automorphism a of order dividing p, nontrivial on G/Z(G), fixes exactly a
line in that quotient. If a commutes with an automorphism t inverting the
quotient, the full preimage of that line is fixed by a and is elementary
abelian of order p².

Orbit counting gives the fixed line and shows that a fixes the center.
Heisenberg commutator coordinates show that t also fixes the center. For a
lift y of a fixed vector, the central displacement d = a(y)y⁻¹ satisfies
d² = 1 by applying a to t(y)y; odd exponent then gives d = 1. No order
condition on t is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.33(1), printed p.29, combined manuscript of 1 March 2004.
-/

open Subgroup
open scoped commutatorElement

namespace HeisenbergPrime.InversionFixedPlane

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

private theorem inverter_fixes_center (e : G ≃* HeisenbergPrime p) (t : MulAut G)
    (ht : ∀ y, t y * y ∈ center G) (z : G) (hz : z ∈ center G) : t z = z := by
  have hab (y : G) : (e (t y)).a = -(e y).a ∧ (e (t y)).b = -(e y).b := by
    have h := HeisenbergPrime.mem_center_iff (e (t y * y)) |>.mp
      (centerCongr e ⟨t y * y, ht y⟩).property
    simpa only [map_mul, HeisenbergPrime.mul_a, HeisenbergPrime.mul_b,
      add_eq_zero_iff_eq_neg] using h
  let u := e.symm (⟨(e z).c, 0, 0⟩ : HeisenbergPrime p)
  let v := e.symm (⟨0, 1, 0⟩ : HeisenbergPrime p)
  have hzab := (HeisenbergPrime.mem_center_iff (e z)).mp
    (centerCongr e ⟨z, hz⟩).property
  have huv : ⁅u, v⁆ = z := by
    apply e.injective
    rw [map_commutatorElement, HeisenbergPrime.commutator_coordinates]
    ext <;> simp [u, v, hzab.1, hzab.2]
  have htz : t ⁅u, v⁆ = ⁅u, v⁆ := by
    apply e.injective
    rw [map_commutatorElement, map_commutatorElement, map_commutatorElement,
      HeisenbergPrime.commutator_coordinates, HeisenbergPrime.commutator_coordinates]
    ext <;> simp [hab]
  simpa only [huv] using htz

private theorem fixed_card_mod [Finite G] (a : MulAut G) (ha : a ^ p = 1) :
    Nat.card a.fixedSubgroup % p = Nat.card G % p := by
  let A := zpowers a
  have hp : IsPGroup p A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have heq : FixedPoints.subgroup A G = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      rw [MulAut.mem_fixedSubgroup]
      exact ((FixedPoints.mem_subgroup (M := A) (α := G) (a := x)).mp hx)
        ⟨a, mem_zpowers a⟩
    · intro hx
      rw [FixedPoints.mem_subgroup]
      have hle : A ≤ MulAction.stabilizer (MulAut G) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup a x).mp hx)
      intro b
      exact hle b.property
  have hmod := hp.card_modEq_card_fixedPoints G
  change Nat.card G % p = Nat.card (FixedPoints.subgroup A G) % p at hmod
  rw [heq] at hmod
  exact hmod.symm

private theorem fixes_of_card_prime [Finite G] (a : MulAut G) (ha : a ^ p = 1)
    (hc : Nat.card G = p) : a = 1 := by
  have hdiv := a.fixedSubgroup.card_subgroup_dvd_card
  rw [hc] at hdiv
  have hcfix : Nat.card a.fixedSubgroup = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdiv with h | h
    · have hm := fixed_card_mod a ha
      rw [h, hc, Nat.mod_self, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at hm
      omega
    · exact h
  have htop := a.fixedSubgroup.eq_top_of_card_eq (hcfix.trans hc.symm)
  ext x
  exact (MulAut.mem_fixedSubgroup a x).mp (htop ▸ mem_top x)

private theorem fixed_card_prime [Finite G] (a : MulAut G) (ha : a ^ p = 1)
    (hne : a ≠ 1) (hc : Nat.card G = p ^ 2) : Nat.card a.fixedSubgroup = p := by
  have hdiv := a.fixedSubgroup.card_subgroup_dvd_card
  rw [hc] at hdiv
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdiv
  interval_cases n
  · have hm := fixed_card_mod a ha
    simp only [hcard, pow_zero, hc, Nat.pow_mod, Nat.mod_self, zero_pow (by decide : 2 ≠ 0),
      Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt, Nat.zero_mod] at hm
    omega
  · simpa using hcard
  · exfalso
    apply hne
    have htop := a.fixedSubgroup.eq_top_of_card_eq (hcard.trans hc.symm)
    ext x
    exact (MulAut.mem_fixedSubgroup a x).mp (htop ▸ mem_top x)

private theorem fixed_lift_of_inverter (a t : MulAut G)
    (hp : p ≠ 2) (hpow : ∀ y : G, y ^ p = 1)
    (hat : Commute a t) (hacenter : ∀ z ∈ center G, a z = z)
    (htcenter : ∀ z ∈ center G, t z = z)
    (ht : ∀ y, t y * y ∈ center G)
    (y : G) (hy : a y * y⁻¹ ∈ center G) : a y = y := by
  let d := a y * y⁻¹
  have hd : d ∈ center G := hy
  have hdy : d * y = a y := by simp [d, mul_assoc]
  have hcomm : a (t y) = t (a y) := congrArg (fun f : MulAut G => f y) hat.eq
  have heq : (d * d) * (t y * y) = t y * y := by
    calc
      _ = (d * t y) * (d * y) := by
        simpa only [mul_assoc] using congrArg (fun z : G => d * z)
          ((show Commute d (t y) from (Subgroup.mem_center_iff.mp hd (t y)).symm).left_comm y)
      _ = t (a y) * a y := by rw [← hdy, map_mul, htcenter d hd]
      _ = a (t y * y) := by rw [map_mul, hcomm]
      _ = t y * y := hacenter _ (ht y)
  have hd2 : d ^ 2 = 1 := by
    rw [pow_two]
    exact mul_right_cancel (heq.trans (one_mul _).symm)
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm
  have hd1 : d = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hd2)
      (orderOf_dvd_of_pow_eq_one (hpow d)))
  simpa only [hd1, one_mul] using hdy.symm

private theorem card_comap_quotient [Finite G] (N : Subgroup G) [N.Normal]
    (E : Subgroup (G ⧸ N)) :
    Nat.card (E.comap (QuotientGroup.mk' N)) = Nat.card E * Nat.card N := by
  let q := QuotientGroup.mk' N
  let P := E.comap q
  let f : P →* E := q.restrict (fun _ hx => hx)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N e
    exact ⟨⟨x, by change q x ∈ E; rw [hx]; exact e.property⟩, Subtype.ext hx⟩
  have hNP : N ≤ P := by
    intro x hx
    change q x ∈ E
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact E.one_mem
  have hker : f.ker = N.subgroupOf P := by
    ext x
    change (⟨q x, x.property⟩ : E) = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hc : Nat.card f.ker = Nat.card N := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv
  have hi : f.ker.index = Nat.card E := by
    rw [index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [← f.ker.index_mul_card, hi, hc]

/-- The preimage of the actual quotient fixed subgroup is the fixed subgroup
in G, and is an elementary abelian plane. The automorphisms act on the
literal central quotient, and the concrete model is supplied by an isomorphism. -/
public theorem fixed_plane [Finite G] (e : G ≃* HeisenbergPrime p)
    (hp : p ≠ 2) (a t : MulAut G) (ha : a ^ p = 1) (hat : Commute a t)
    (ht : ∀ v : G ⧸ center G, quotientAut (center G) t v = v⁻¹)
    (hne : quotientAut (center G) a ≠ 1) :
    let E := (quotientAut (center G) a).fixedSubgroup.comap (QuotientGroup.mk' (center G))
    IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧ E = a.fixedSubgroup := by
  let q := QuotientGroup.mk' (center G)
  let b := quotientAut (center G) a
  let E := b.fixedSubgroup.comap q
  have hZ : Nat.card (center G) = p :=
    (Nat.card_congr (centerCongr e).toEquiv).trans HeisenbergPrime.card_center
  have hQ : Nat.card (G ⧸ center G) = p ^ 2 := by
    have h := (center G).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr e.toEquiv, HeisenbergPrime.card, hZ, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h.symm
  have hpow (y : G) : y ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one, HeisenbergPrime.pow_prime hp]
  have hacenter (z : G) (hz : z ∈ center G) : a z = z := by
    have haZ : (MulAut.characteristic (center G) a) ^ p = 1 := by
      rw [← map_pow, ha, map_one]
    have hh := fixes_of_card_prime (MulAut.characteristic (center G) a) haZ hZ
    exact congrArg Subtype.val (DFunLike.congr_fun hh ⟨z, hz⟩)
  have htz (y : G) : t y * y ∈ center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (t y * y) = 1
    rw [map_mul, ← quotientAut_apply_mk, ht, inv_mul_cancel]
  have htcenter := inverter_fixes_center e t htz
  have hb : b ^ p = 1 := by dsimp [b]; rw [← map_pow, ha, map_one]
  have hline : Nat.card b.fixedSubgroup = p := fixed_card_prime b hb hne hQ
  have hE : Nat.card E = p ^ 2 := by
    rw [card_comap_quotient, hline, hZ, pow_two]
  refine ⟨{ toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE
            exponent_dvd_p := ?_ }, hE, ?_⟩
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro y
    exact Subtype.ext (hpow y)
  · apply le_antisymm
    · intro y hy
      apply (MulAut.mem_fixedSubgroup a y).mpr
      have hqy : q (a y) = q y := by
        simpa only [b, q, quotientAut_apply_mk] using
          (MulAut.mem_fixedSubgroup b (q y)).mp hy
      have hdy : a y * y⁻¹ ∈ center G := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (a y * y⁻¹) = 1
        rw [map_mul, map_inv, hqy, mul_inv_cancel]
      exact fixed_lift_of_inverter a t hp hpow hat hacenter htcenter htz y hdy
    · intro y hy
      change q y ∈ b.fixedSubgroup
      apply (MulAut.mem_fixedSubgroup b (q y)).mpr
      dsimp only [b, q]
      rw [quotientAut_apply_mk, (MulAut.mem_fixedSubgroup a y).mp hy]

end HeisenbergPrime.InversionFixedPlane
