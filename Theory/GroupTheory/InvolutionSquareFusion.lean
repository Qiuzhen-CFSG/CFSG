module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Weak closure from unique involution squares

Suppose all elements of order four in a Sylow two-subgroup have the same
square `z`, which is central in that Sylow subgroup. If every involution
centralizes an element of order four, then `z` is weakly closed.

Given a conjugation taking `t` to `z`, transport a commuting element of order
four into the centralizer of `z`, and conjugate it into the original Sylow
subgroup there. Its square is again `z`. Since the second conjugator fixes
`z`, the first conjugator must also fix `z`, hence `t = z`.

This supplies the local fusion argument for the dihedral-quaternion central
products in MacWilliams's theorem, quoted in Janko–Thompson, Math. Z. 113
(1970), 1.2, pp.385–386. It does not use a transfer or Z-star hypothesis.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- A unique involution square is weakly closed if every involution centralizer
contains a square root of it. -/
public theorem eq_of_isConj_of_unique_involution_square
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hz : z ∈ center S)
    (hunique : ∀ x : S, orderOf x = 4 → x ^ 2 = z)
    (hroot : ∀ t : S, orderOf t = 2 → ∃ x : S, orderOf x = 4 ∧ Commute x t)
    (t : S) (ht : orderOf t = 2) (hconj : IsConj (t : G) (z : G)) : t = z := by
  obtain ⟨x, hx, hxt⟩ := hroot t ht
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
  have hy : orderOf y = 4 := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy]; rfl)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have hyS : (MulAut.conj k) y ∈ S.subtype hSH := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (T : Set H)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let v : S := ⟨((MulAut.conj k) y : H), hyS⟩
  have hv : orderOf v = 4 := by
    calc
      orderOf v = orderOf (((MulAut.conj k) y : H) : G) := (Subgroup.orderOf_coe v).symm
      _ = orderOf ((MulAut.conj k) y) := Subgroup.orderOf_coe _
      _ = 4 := ((MulAut.conj k).orderOf_eq y).trans hy
  have hvz : (v : G) ^ 2 = z := congrArg Subtype.val (hunique v hv)
  have hxz : (x : G) ^ 2 = z := congrArg Subtype.val (hunique x hx)
  have hfix : (MulAut.conj (k : G)) (z : G) = z := by
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
  have hcomp : (MulAut.conj (k : G)) (f (z : G)) = z := by
    calc
      _ = (MulAut.conj (k : G)) (f ((x : G) ^ 2)) := by rw [hxz]
      _ = (v : G) ^ 2 := by rw [map_pow, map_pow]; rfl
      _ = z := hvz
  have hfz : f (z : G) = z := (MulAut.conj (k : G)).injective (hcomp.trans hfix.symm)
  exact Subtype.ext (f.injective (hft.trans hfz.symm))

end Sylow
