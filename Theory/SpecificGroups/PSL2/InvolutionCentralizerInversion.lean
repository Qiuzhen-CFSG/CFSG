module
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Inverting the odd part of a PSL₂ involution centralizer

The reflected torus identifies the centralizer with a dihedral group.
Every odd-order element is a rotation, and a reflection inverts all such
rotations. Involution fusion realizes that reflection as a conjugate of
the original involution, preserving the original centralizer elements.

Source: Huppert II.8.3--4; the inversion step in Aschbacher--Smith,
proof of 12.6.26, printed p.833.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- One conjugate of the original involution simultaneously inverts every
odd-order element of its centralizer. -/
theorem conjugate_inverts_odd_centralizer
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ g : PSL(2,F), ∀ x : PSL(2,F), Odd (orderOf x) → Commute x t →
      (g*t*g⁻¹)*x*(g*t*g⁻¹)⁻¹ = x⁻¹ := by
  obtain ⟨R,s,hR,_,hs,hsR,hi,hc,_⟩ := psl2_reflected_torus_card hF
    (show GorensteinWalter.IsInvolution t from ⟨by intro h; simp [h] at ht,
      by simpa only [ht] using pow_orderOf_eq_one t⟩)
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R s hR hs.2 hsR hi
  let C := centralizer ({t} : Set PSL(2,F))
  let d : C ≃* DihedralGroup (Nat.card R) := (MulEquiv.subgroupCongr hc).trans e
  let j : C := d.symm (DihedralGroup.sr 0)
  have hj : orderOf (j : PSL(2,F)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (d.symm.orderOf_eq _).trans (DihedralGroup.orderOf_sr 0)
  obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_isConj t (j : PSL(2,F)) ht hj)
  refine ⟨g,fun x ho hx => ?_⟩
  rw [hg]
  let y : C := ⟨x,mem_centralizer_singleton_iff.mpr hx.eq⟩
  have he : j*y*j⁻¹ = y⁻¹ := by
    apply d.injective
    simp only [map_mul,map_inv,show d j = DihedralGroup.sr 0 from d.apply_symm_apply _]
    cases hy : d y with
    | r i => simp
    | sr i =>
      have hh : Odd (orderOf (d y)) := (d.orderOf_eq y).symm ▸ ((Subgroup.orderOf_coe y) ▸ ho)
      rw [hy,DihedralGroup.orderOf_sr] at hh
      norm_num at hh
  exact congrArg Subtype.val he
end Theory.PSL2
