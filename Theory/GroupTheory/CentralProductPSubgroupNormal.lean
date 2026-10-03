module
public import Mathlib.GroupTheory.PGroup

/-!
# Normality of a p-subgroup from its central product

Let `U` be a p-subgroup of a finite group `G`. If `U Z(G)` is normal and
`U` contains every central p-element, then `U` is normal. The statement uses
`IsPGroup p (zpowers z)` to express that `z` is a p-element; the argument
works for every natural number `p` and needs no primality hypothesis.

Choose a common p-power annihilating all elements of `U`. A conjugate of an
element of `U` lies in `U Z(G)`, so write it as `u z`, with `u` in `U` and
`z` central. Since the factors commute, the same p-power annihilates `z`.
The central-element hypothesis puts `z`, and hence the conjugate, in `U`.

This source-neutral normality lift is used to pass from normality of
`U Z(G_a)` to normality of the actual finite subgroup `U` in the
characteristic-two case of Stellmacher, *Pushing up*, Arch. Math. 46 (1986),
proof of (3.3), assertions (4)--(6), p.15.
-/

namespace Subgroup

/-- A finite p-subgroup containing every central p-element is normal whenever
its product with the center is normal. -/
public theorem normal_of_sup_center_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} (U : Subgroup G)
    (hU : IsPGroup p U) (hn : (U ⊔ center G).Normal)
    (hcentral : ∀ z ∈ center G, IsPGroup p (zpowers z) → z ∈ U) : U.Normal := by
  obtain ⟨n, hnU⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hU
  have hp (x : G) (hx : x ∈ U) : x ^ p ^ n = 1 :=
    congrArg Subtype.val (hnU ⟨x, hx⟩)
  refine ⟨fun x hx g ↦ ?_⟩
  obtain ⟨u, hu, z, hz, hprod⟩ :=
    mem_sup_of_normal_right.mp (hn.conj_mem x ((show U ≤ U ⊔ center G from le_sup_left) hx) g)
  have hzpow : z ^ p ^ n = 1 := by
    have hcomm : Commute u z := mem_center_iff.mp hz u
    have hh : (u * z) ^ p ^ n = 1 := by
      rw [hprod, conj_pow, hp x hx]
      simp
    simpa only [hcomm.mul_pow, hp u hu, one_mul] using hh
  have hzU : z ∈ U := hcentral z hz (IsPGroup.of_card_dvd_pow (n := n) (by
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    exact hzpow))
  exact hprod ▸ U.mul_mem hu hzU

end Subgroup
