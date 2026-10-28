module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Centralizers in a product with a dihedral supplement

If U commutes with a dihedral group D of order eight and contains the central
involution of D, then centralizing a noncentral involution d in D cuts U D
down to U⟨d⟩. The proof separates the two factors and uses the eight-element
centralizer calculation in D. This is the two-core kernel calculation in
Aschbacher--Smith 14.3.20, printed pp.997--998.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
private theorem dihedral_centralizer_data : ∀ z d : DihedralGroup 4,
    z ∈ center (DihedralGroup 4) → z ≠ 1 → d^2 = 1 → d ≠ 1 → d ≠ z →
    ∀ x : DihedralGroup 4, x*d=d*x → x=1 ∨ x=z ∨ x=d ∨ x=z*d := by
  decide +kernel

/-- A reflection in a commuting dihedral supplement leaves precisely U⟨d⟩
in the centralizer of the product. -/
theorem centralizer_inf_of_dihedral_supplement
    {G : Type*} [Group G] (U D : Subgroup G) (z d : G)
    (hDU : D ≤ centralizer (U : Set G)) (eD : D ≃* DihedralGroup 4)
    (hzU : z ∈ U) (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hdD : d ∈ D) (hd2 : d^2=1) (hd1 : d ≠ 1) (hdz : d ≠ z) :
    (U ⊔ D) ⊓ centralizer ({d} : Set G) = U ⊔ zpowers d := by
  let zD : D := ⟨z,hzD⟩
  let dD : D := ⟨d,hdD⟩
  have hzC : eD zD ∈ center (DihedralGroup 4) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := eD.surjective x
    rw [←map_mul,←map_mul]
    exact congrArg eD (Subtype.ext (hDU y.property z hzU).symm)
  have hz1' : eD zD ≠ 1 := by
    intro hh
    exact hz1 (congrArg Subtype.val (eD.injective (hh.trans eD.map_one.symm)))
  have hd2' : (eD dD)^2=1 := by
    rw [←map_pow,show dD^2=1 from Subtype.ext hd2,map_one]
  have hd1' : eD dD ≠ 1 := by
    intro hh
    exact hd1 (congrArg Subtype.val (eD.injective (hh.trans eD.map_one.symm)))
  have hdz' : eD dD ≠ eD zD := fun hh => hdz (congrArg Subtype.val (eD.injective hh))
  have hc := dihedral_centralizer_data (eD zD) (eD dD) hzC hz1' hd2' hd1' hdz'
  have hUC : U ≤ centralizer ({d} : Set G) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (hDU hdD u hu)
  have hDC : zpowers d ≤ centralizer ({d} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (U : Set G) * (D : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U D (hDU.trans (centralizer_le_normalizer _))]
      exact hx.1
    obtain ⟨u,hu,b,hb,rfl⟩ := hp
    have hbd : b*d=d*b := by
      have h := mem_centralizer_singleton_iff.mp hx.2
      have hud := mem_centralizer_singleton_iff.mp (hUC hu)
      apply mul_left_cancel (a:=u)
      calc
        u*(b*d) = (u*b)*d := (mul_assoc _ _ _).symm
        _ = d*(u*b) := h
        _ = u*(d*b) := by rw [←mul_assoc,←hud,mul_assoc]
    let bD : D := ⟨b,hb⟩
    have hbe : eD bD * eD dD = eD dD * eD bD := by
      rw [←map_mul,←map_mul]
      exact congrArg eD (Subtype.ext hbd)
    have hzmem : z ∈ U ⊔ zpowers d := (show U ≤ U ⊔ zpowers d from le_sup_left) hzU
    have hdmem : d ∈ U ⊔ zpowers d := (show zpowers d ≤ U ⊔ zpowers d from le_sup_right) (mem_zpowers d)
    have hbmem : b ∈ U ⊔ zpowers d := by
      rcases hc (eD bD) hbe with hh | hh | hh | hh
      · have he : b=1 := congrArg Subtype.val (eD.injective (hh.trans eD.map_one.symm))
        exact he.symm ▸ (U ⊔ zpowers d).one_mem
      · have he : b=z := congrArg Subtype.val (eD.injective hh)
        exact he.symm ▸ hzmem
      · have he : b=d := congrArg Subtype.val (eD.injective hh)
        exact he.symm ▸ hdmem
      · have he : b=z*d := congrArg Subtype.val (eD.injective (hh.trans (map_mul eD zD dD).symm))
        exact he.symm ▸ (U ⊔ zpowers d).mul_mem hzmem hdmem
    exact (U ⊔ zpowers d).mul_mem ((show U ≤ U ⊔ zpowers d from le_sup_left) hu) hbmem
  · exact le_inf (sup_le_sup_left (zpowers_le.mpr hdD) U) (sup_le hUC hDC)
end Subgroup
