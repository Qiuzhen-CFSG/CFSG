module

public import Mathlib.GroupTheory.Sylow

/-!
# Square roots of central Sylow involutions

Let `S` be a Sylow two-subgroup of a finite group `G`, and let `t` be a
central involution of `S`. Then `t` is a square in `G` if and only if it is
a square in the supplied subgroup `S`.

An ambient square root has fourth power one and centralizes `t`, so its
cyclic subgroup is a two-subgroup of `C_G(t)`. Centrality of `t` in `S`
allows `S` to restrict to a Sylow subgroup of this centralizer. Sylow
conjugacy within the centralizer then carries the square root into `S`
while fixing its square `t`.

This is the centralizer refinement of the square argument in
Kurzweil--Stellmacher, *The Theory of Finite Groups*, Chapter 12, Theorem 3,
pp. 365--366. It supplies the square-root transfer independently of any
maximal-local-subgroup hypotheses.
-/

open scoped Pointwise

/-- A central involution of a supplied Sylow two-subgroup has an ambient
square root exactly when it has a square root in that Sylow subgroup. -/
public theorem Sylow.exists_square_iff_of_mem_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : S) (ht : t ∈ Subgroup.center S)
    (ht2 : orderOf t = 2) :
    (∃ x : G, x ^ 2 = (t : G)) ↔ ∃ x : S, x ^ 2 = t := by
  constructor
  · rintro ⟨x, hx⟩
    let C : Subgroup G := Subgroup.centralizer {(t : G)}
    have hS : (S : Subgroup G) ≤ C := by
      intro s hs
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ht ⟨s, hs⟩)
    have hxc : x ∈ C := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← hx]
      simp only [pow_two, mul_assoc]
    let xc : C := ⟨x, hxc⟩
    have ht_sq : t ^ 2 = 1 := by simpa only [ht2] using pow_orderOf_eq_one t
    have hxc4 : xc ^ (2 ^ 2) = 1 := by
      apply Subtype.ext
      change x ^ (2 * 2) = 1
      rw [pow_mul, hx]
      exact congrArg Subtype.val ht_sq
    have hxp : IsPGroup 2 (Subgroup.zpowers xc) :=
      IsPGroup.of_card_dvd_pow (n := 2) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hxc4)
    obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q (S.subtype hS)
    let y : C := MulAut.conj c xc
    have hy : y ∈ S.subtype hS := by
      rw [← hc]
      exact Subgroup.smul_mem_pointwise_smul xc (MulAut.conj c) (Q : Subgroup C)
        (hQ (Subgroup.mem_zpowers xc))
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    change (y : G) ^ 2 = (t : G)
    change (MulAut.conj (c : G) x) ^ 2 = (t : G)
    rw [← map_pow, hx, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff.mp c.property]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
