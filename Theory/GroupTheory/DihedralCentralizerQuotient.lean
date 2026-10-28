module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Centralizer quotients in dihedral-eight extensions

The centralizer of a noncentral element of the dihedral group of order eight
is abelian. Consequently a centralizer upstairs has abelian quotient by its
intersection with the kernel when its distinguished element has noncentral
image. An element outside an index-two subgroup containing the kernel has
noncentral image: every central element of the dihedral eight is a square.

These elementary quotient calculations support the local centralizer step in
Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

open Subgroup
open scoped commutatorElement

namespace DihedralGroup

/-- Elements centralizing a noncentral dihedral-eight element commute. -/
public theorem noncentral_commuting_pair (q a b : DihedralGroup 4)
    (hq : q ∉ center (DihedralGroup 4))
    (ha : a * q = q * a) (hb : b * q = q * b) : a * b = b * a := by
  have hcalc : ∀ q : DihedralGroup 4, (∃ y, y*q ≠ q*y) →
      ∀ a b, a*q=q*a → b*q=q*b → a*b=b*a := by decide
  apply hcalc q _ a b ha hb
  simpa only [mem_center_iff, not_forall] using hq

/-- Every central element of the dihedral eight is a square. -/
public theorem central_is_square (q : DihedralGroup 4) (hq : q ∈ center (DihedralGroup 4)) :
    ∃ y : DihedralGroup 4, y ^ 2 = q := by
  have hcalc : ∀ q : DihedralGroup 4, (∀ y, y*q=q*y) → ∃ y, y^2=q := by decide
  exact hcalc q (mem_center_iff.mp hq)

end DihedralGroup

namespace Subgroup

/-- Outside an index-two subgroup above the kernel, the dihedral image is noncentral. -/
public theorem quotient_noncentral_of_not_mem_index_two {P : Type*} [Group P]
    (H M : Subgroup P) [H.Normal] (e : (P ⧸ H) ≃* DihedralGroup 4)
    (hM : M.index = 2) (hHM : H ≤ M) (x : P) (hx : x ∉ M) :
    QuotientGroup.mk' H x ∉ center (P ⧸ H) := by
  intro hc
  have hec : e (QuotientGroup.mk' H x) ∈ center (DihedralGroup 4) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨v, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hc v)
  obtain ⟨y, hy⟩ := DihedralGroup.central_is_square _ hec
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective H (e.symm y)
  have huq : (QuotientGroup.mk' H) (u ^ 2) = (QuotientGroup.mk' H) x := by
    apply e.injective
    rw [map_pow, hu, map_pow, e.apply_symm_apply, hy]
  have hd : u ^ 2 / x ∈ H := QuotientGroup.eq_iff_div_mem.mp huq
  apply hx
  simpa using M.mul_mem (M.inv_mem (hHM hd)) (M.sq_mem_of_index_two hM u)

/-- A noncentral dihedral image makes the centralizer quotient abelian. -/
public theorem centralizer_quotient_commutative_of_dihedral_noncentral
    {P : Type*} [Group P] (H : Subgroup P) [H.Normal]
    (e : (P ⧸ H) ≃* DihedralGroup 4) (x : P)
    (hx : QuotientGroup.mk' H x ∉ center (P ⧸ H)) :
    IsMulCommutative ((centralizer ({x} : Set P)) ⧸
      H.subgroupOf (centralizer ({x} : Set P))) := by
  let q := QuotientGroup.mk' H
  let f := e.toMonoidHom.comp q
  have hfx : f x ∉ center (DihedralGroup 4) := by
    intro h
    apply hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp h (e y)
  apply Normal.quotient_commutative_iff_commutator_le.mpr
  rw [_root_.commutator_def]
  apply commutator_le.mpr
  intro a _ b _
  change ⁅(a : P), (b : P)⁆ ∈ H
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅(a : P), (b : P)⁆ = 1
  apply e.injective
  change f ⁅(a : P), (b : P)⁆ = e 1
  rw [map_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  apply DihedralGroup.noncentral_commuting_pair (f x) _ _ hfx
  · simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp a.property)
  · simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp b.property)

end Subgroup
