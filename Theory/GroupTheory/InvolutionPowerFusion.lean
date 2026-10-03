module

public import Theory.GroupTheory.InvolutionSquareFusion
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Fusion of central involutions which are higher powers

If a central Sylow involution is the unique involution among the `n`-th
powers, it cannot fuse to an element centralizing one of its `n`-th roots.
Conjugate that root into the original Sylow subgroup inside the centralizer
of the central involution. Uniqueness of its power forces both conjugations
to fix the involution.

A cyclic subgroup containing all `n`-th powers supplies the uniqueness.
This is the power argument in Janko–Thompson, Math. Z. 113 (1970),
§4, Case 1, p.392, in a form requiring only the particular commuting root.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- A unique involution among the `n`-th powers cannot fuse to an element
centralizing one of its `n`-th roots. -/
public theorem eq_of_isConj_of_unique_involution_power
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (z : S) (hz : z ∈ center S) (hz2 : orderOf z = 2)
    (hunique : ∀ x : S, orderOf (x ^ n) = 2 → x ^ n = z)
    (t : S) (hroot : ∃ x : S, x ^ n = z ∧ Commute x t)
    (hconj : IsConj (t : G) (z : G)) : t = z := by
  obtain ⟨x, hx, hxt⟩ := hroot
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  let H : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩))
  let y : H := ⟨f (x : G), mem_centralizer_singleton_iff.mpr (by
    have hh := (hxt.map ((f : G →* G).comp (S : Subgroup G).subtype)).eq
    change f (x : G) * f (t : G) = f (t : G) * f (x : G) at hh
    rwa [hft] at hh)⟩
  have hy : orderOf y = orderOf x := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  obtain ⟨m, hm⟩ := S.isPGroup'.exists_orderOf_dvd_pow x
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := m) (by rw [Nat.card_zpowers, hy]; exact hm)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have hyS : (MulAut.conj k) y ∈ S.subtype hSH := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (T : Set H)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let v : S := ⟨((MulAut.conj k) y : H), hyS⟩
  have hvpower : orderOf (v ^ n) = 2 := by
    have he : ((v ^ n : S) : G) = (((MulAut.conj k) (y ^ n) : H) : G) := by
      simp only [Subgroup.coe_pow, map_pow]
      rfl
    rw [← Subgroup.orderOf_coe, he, Subgroup.orderOf_coe,
      MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    change orderOf (f (x : G) ^ n) = 2
    rw [← map_pow, MulEquiv.orderOf_eq, ← Subgroup.coe_pow, Subgroup.orderOf_coe, hx, hz2]
  have hvz : (v : G) ^ n = z := congrArg Subtype.val (hunique v hvpower)
  have hxz : (x : G) ^ n = z := congrArg Subtype.val hx
  have hfix : (MulAut.conj (k : G)) (z : G) = z := by
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
  have hcomp : (MulAut.conj (k : G)) (f (z : G)) = z := by
    calc
      _ = (MulAut.conj (k : G)) (f ((x : G) ^ n)) := by rw [hxz]
      _ = (v : G) ^ n := by rw [map_pow, map_pow]; rfl
      _ = z := hvz
  have hfz : f (z : G) = z := (MulAut.conj (k : G)).injective (hcomp.trans hfix.symm)
  exact Subtype.ext (f.injective (hft.trans hfz.symm))


/-- A cyclic subgroup containing the `n`-th powers prevents fusion to any
element centralizing an `n`-th root of the central involution. -/
public theorem eq_of_isConj_of_powers_mem_cyclic
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (R : Subgroup S) [IsCyclic R]
    (hpowers : ∀ x : S, x ^ n ∈ R)
    (z : S) (hz : z ∈ center S) (hz2 : orderOf z = 2)
    (t : S) (hroot : ∃ x : S, x ^ n = z ∧ Commute x t)
    (hconj : IsConj (z : G) (t : G)) : t = z := by
  have hzR : z ∈ R := by
    obtain ⟨x, hx, -⟩ := hroot
    rw [← hx]
    exact hpowers x
  apply S.eq_of_isConj_of_unique_involution_power n z hz hz2 ?_ t hroot hconj.symm
  intro x hx
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨x ^ n, hpowers x⟩ : R)) (y := (⟨z, hzR⟩ : R))
    (by rwa [← Subgroup.orderOf_coe]) (by rwa [← Subgroup.orderOf_coe]))

/-- An index-at-most-two subgroup whose squares lie in a cyclic subgroup
supplies uniqueness of involutions among fourth powers in the whole Sylow. -/
public theorem eq_of_isConj_of_index_le_two_of_squares_mem_cyclic
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup S) (hi : H.index ≤ 2)
    (R : Subgroup H) [IsCyclic R] (hsquares : ∀ x : H, x ^ 2 ∈ R)
    (z : H) (hz : (z : S) ∈ center S) (hz2 : orderOf z = 2)
    (t : H) (hroot : ∃ x : H, x ^ 4 = z ∧ Commute x t)
    (hconj : IsConj ((z : S) : G) ((t : S) : G)) : t = z := by
  let R' := R.map H.subtype
  let : IsCyclic R' := isCyclic_of_surjective (H.subtype.subgroupMap R)
    (H.subtype.subgroupMap_surjective R)
  have hsq (x : S) : x ^ 2 ∈ H := by
    have hn := H.index_ne_zero_of_finite
    have hh : H.index = 1 ∨ H.index = 2 := by omega
    rcases hh with hh | hh
    · rw [index_eq_one.mp hh]
      trivial
    · exact sq_mem_of_index_two hh x
  have hpowers (x : S) : x ^ 4 ∈ R' := by
    have hh := mem_map_of_mem H.subtype (hsquares (⟨x ^ 2, hsq x⟩ : H))
    change (x ^ 2) ^ 2 ∈ R' at hh
    simpa only [← pow_mul, Nat.reduceMul] using hh
  apply Subtype.ext
  apply S.eq_of_isConj_of_powers_mem_cyclic 4 R' hpowers z hz
    ((Subgroup.orderOf_coe z).trans hz2) t ?_ hconj
  obtain ⟨x, hx, hxt⟩ := hroot
  exact ⟨x, congrArg Subtype.val hx, hxt.map H.subtype⟩

/-- If all Sylow fourth powers lie in the cyclic center of a subgroup,
and that center has order at least eight, a central Sylow involution
cannot fuse to a different element of the subgroup. -/
public theorem eq_of_isConj_of_fourth_powers_in_cyclic_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (R : Subgroup S) [IsCyclic (center R)]
    (hlarge : 8 ≤ Nat.card (center R))
    (hfourth : ∀ x : S, x ^ 4 ∈ (center R).map R.subtype)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) (hzR : z ∈ R)
    (t : S) (htR : t ∈ R) (hconj : IsConj (z : G) (t : G)) : t = z := by
  let zC : center R := ⟨⟨z, hzR⟩, mem_center_iff.mpr (fun a =>
    Subtype.ext (mem_center_iff.mp hzC a))⟩
  have hzCorder : orderOf zC = 2 := by
    rw [← orderOf_coe, ← orderOf_coe]
    exact hz
  have hunique (x : S) (hx : orderOf x = 8) : x ^ 4 = z := by
    obtain ⟨y, hy, heq⟩ := hfourth x
    have hyorder : orderOf (⟨y, hy⟩ : center R) = 2 := by
      rw [← orderOf_coe, ← orderOf_coe]
      change orderOf (R.subtype y) = 2
      rw [heq, orderOf_pow, hx]
      decide
    exact heq.symm.trans (congrArg (fun a : center R => ((a : R) : S))
      (IsCyclic.eq_of_orderOf_eq_two hyorder hzCorder))
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := center R)
  obtain ⟨n, hn⟩ := ((S.isPGroup'.to_subgroup R).to_subgroup (center R)).exists_card_eq
  have hn3 : 3 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [hn] using hlarge
  have hd : 8 ∣ orderOf c := by
    rw [hc, hn]
    exact pow_dvd_pow 2 hn3
  let d : center R := c ^ (orderOf c / 8)
  have hd8 : orderOf d = 8 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hd
  let x : S := ((d : R) : S)
  have hx8 : orderOf x = 8 := (orderOf_coe (d : R)).trans ((orderOf_coe d).trans hd8)
  let C := (center R).map R.subtype
  let : IsCyclic C := isCyclic_of_surjective (R.subtype.subgroupMap (center R))
    (R.subtype.subgroupMap_surjective (center R))
  apply S.eq_of_isConj_of_powers_mem_cyclic 4 C hfourth z hzC hz t ?_ hconj
  exact ⟨x, hunique x hx8,
    (congrArg R.subtype (mem_center_iff.mp d.property ⟨t, htR⟩)).symm⟩

end Sylow
