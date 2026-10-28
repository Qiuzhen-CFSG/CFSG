module

public import Theory.GroupAction.InvertedFixedCentralizer
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Cyclic fixed subgroups of involutions on odd rank-two prime groups

A nontrivial involutive automorphism has a nonidentity inverted element
centralizing its fixed subgroup. The p-group normalizer condition constructs
that element; taking a power supplies an inverted element of order p.
If the fixed subgroup were noncyclic, it would contain an elementary subgroup
of order p². Their commuting, disjoint product has order p³, contradicting
the rank bound.

This is the involution step of Aschbacher–Smith, Lemma A.1.31(1), printed
pp.27–28. The normalizer-condition proof of the inverted-element lemma gives
the same consequence as the source's Thompson A × B argument.
-/

public section

open Subgroup
namespace Theory.GroupTheory

theorem cyclic_fixedSubgroup_of_involution_rank_le_two
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp : Odd p) (hrank : primeRank p P ≤ 2)
    (a : MulAut P) (ha : Function.Involutive a) (hne : a ≠ 1) :
    IsCyclic a.fixedSubgroup := by
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact hp.pow
  have hproper : a.toMonoidHom.eqLocus (MonoidHom.id P) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    apply hne
    ext x
    have hx : x ∈ a.toMonoidHom.eqLocus (MonoidHom.id P) := by rw [h]; trivial
    exact hx
  obtain ⟨y, hy, hay, hyc⟩ :=
    Theory.GroupAction.exists_ne_one_inverted_centralizing_fixedPoints hP hodd a ha hproper
  have hdiv : p ∣ Nat.card (zpowers y) := by
    rw [Nat.card_zpowers]
    exact hP.dvd_orderOf hy
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hzP : orderOf (z : P) = p := (Subgroup.orderOf_coe z).trans hz
  have haz : a (z : P) = (z : P)⁻¹ := by
    obtain ⟨n, hn⟩ := z.property
    rw [← hn, map_zpow, hay, inv_zpow]
  have hzc (x : P) (hx : a x = x) : Commute (z : P) x := by
    obtain ⟨n, hn⟩ := z.property
    rw [← hn]
    exact (hyc x hx).zpow_left n
  have hzfix : (z : P) ∉ a.fixedSubgroup := by
    intro h
    have hzself : (z : P) = (z : P)⁻¹ :=
      ((MulAut.mem_fixedSubgroup _ _).mp h).symm.trans haz
    have hz2 : (z : P) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (z : P) * z = (z : P)⁻¹ * z := congrArg (· * (z : P)) hzself
        _ = 1 := inv_mul_cancel _
    have hz1 : (z : P) = 1 := hodd.coprime_two_right.pow_left_bijective.injective
      (hz2.trans (one_pow 2).symm)
    rw [hz1, orderOf_one] at hzP
    exact (Fact.out : p.Prime).ne_one hzP.symm
  by_contra hnon
  have hpne : p ≠ 2 := by intro he; exact hp.not_two_dvd_nat (he.symm ▸ dvd_refl 2)
  obtain ⟨E, _, hEcard, hE⟩ :=
    (hP.to_subgroup a.fixedSubgroup).exists_normal_elementary_prime_sq_of_odd_not_isCyclic hpne hnon
  let E' := E.map a.fixedSubgroup.subtype
  let : IsElementaryAbelian p E := hE
  let : IsElementaryAbelian p E' := IsElementaryAbelian.map_subtype
  have hE' : Nat.card E' = p ^ 2 := by
    rw [show E' = E.map a.fixedSubgroup.subtype from rfl,
      card_map_of_injective a.fixedSubgroup.subtype_injective, hEcard]
  have hfix : E' ≤ centralizer ({(z : P)} : Set P) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact (hzc x ((MulAut.mem_fixedSubgroup _ _).mp (map_subtype_le E hx))).eq.symm
  have hthree := IsElementaryAbelian.primeRank_ge_of_fixed_join E' z hzP
    (fun hx => hzfix (map_subtype_le E hx)) hfix hE'
  omega

end Theory.GroupTheory
