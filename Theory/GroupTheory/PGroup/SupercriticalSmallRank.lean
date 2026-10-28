module

public import Theory.GroupTheory.PGroup.SupercriticalRank
public import Theory.Quasithin.Rank

/-!
# Supercritical subgroups of small prime rank

A supercritical subgroup is nontrivial whenever the ambient finite p-group is:
an order-p element would otherwise lie in its centralizer and hence in the
trivial subgroup. For odd p, rank detection above one and rank monotonicity
then give equality of ranks when the ambient rank is at most two. The trivial
ambient group is retained in the equality statement.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(1), printed p.25.
-/

open Subgroup
open scoped IsMulCommutative

private theorem primeRank_pos_of_nontrivial_pGroup
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup p P) : 0 < primeRank p P := by
  obtain ⟨n, hn, hc⟩ := hP.nontrivial_iff_card.mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p
    (hc ▸ dvd_pow_self p (by omega : n ≠ 0))
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  by_contra h
  have hb := (primeRank_le_iff_elementary_card_le P (p := p) (n := 0)).mp
    (by omega) (zpowers x) inferInstance
  rw [Nat.card_zpowers, hx, pow_zero] at hb
  exact (not_le_of_gt (Fact.out : p.Prime).one_lt) hb

namespace IsSupercriticalPSubgroup

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

/-- A supercritical subgroup of a nontrivial finite p-group is nontrivial. -/
public theorem nontrivial_of_nontrivial [Nontrivial P]
    (hX : IsSupercriticalPSubgroup p X) (hP : IsPGroup p P) : Nontrivial X := by
  apply X.nontrivial_iff_ne_bot.mpr
  intro hb
  obtain ⟨n, hn, hc⟩ := hP.nontrivial_iff_card.mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p
    (hc ▸ dvd_pow_self p (by omega : n ≠ 0))
  have hmem := hX.order_p_mem x (by
    intro y hy
    have hy1 : y = 1 := by simpa [hb] using hy
    simp [hy1]) hx
  have he : x = 1 := by simpa [hb] using hmem
  rw [he, orderOf_one] at hx
  exact (Fact.out : p.Prime).ne_one hx.symm

/-- Supercritical subgroups preserve prime rank when the ambient odd p-group has rank at most two.
This includes the trivial ambient group. -/
public theorem primeRank_eq_of_le_two (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) (hr : primeRank p P ≤ 2) :
    primeRank p X = primeRank p P := by
  have hle := primeRank_subgroup_le p X
  cases subsingleton_or_nontrivial P with
  | inl hs =>
    let : Subsingleton P := hs
    have hz : primeRank p P ≤ 0 :=
      (primeRank_le_iff_elementary_card_le P).mpr (fun E _ => by simp)
    omega
  | inr hn =>
    let : Nontrivial P := hn
    let : Nontrivial X := hX.nontrivial_of_nontrivial hP
    have hxpos := primeRank_pos_of_nontrivial_pGroup (hP.to_subgroup X)
    by_cases htwo : 1 < primeRank p P
    · have hx := hX.one_lt_primeRank hP hp htwo
      omega
    · omega

end IsSupercriticalPSubgroup

