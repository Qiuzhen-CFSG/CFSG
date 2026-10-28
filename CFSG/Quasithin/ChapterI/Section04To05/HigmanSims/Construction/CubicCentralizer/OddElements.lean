module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.DihedralShape

/-!
# The original cubic contains every local odd-order element

The exact multiplication equivalence for C_H(t)=<t>×D8 retains the cubic
factor. Projection of an odd-order element to the dihedral eight is trivial
by coprime orders, so that element belongs to the original cyclic subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every odd-order element in the actual point/cubic centralizer belongs
to the specified original cubic subgroup. -/
theorem TypeAt.cubic_point_centralizer_odd_mem (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3)
    (x : G) (hxH : x ∈ involutionCentralizer z) (hxt : Commute x t)
    (hxodd : Odd (orderOf x)) : x ∈ zpowers t := by
  obtain ⟨c,b,_,_,_,_,_,_,_,_,hD8,_,_,_,e,he⟩ :=
    h.cubic_point_centralizer_dihedral_shape t ht ht3
  let D : Subgroup G := zpowers c ⊔ zpowers b
  let L := involutionCentralizer z ⊓ centralizer ({t} : Set G)
  let xL : L := ⟨x,hxH,mem_centralizer_singleton_iff.mpr hxt.eq⟩
  let q : L →* D := (MonoidHom.snd (zpowers t) D).comp e.symm.toMonoidHom
  have hdiv : orderOf (q xL) ∣ orderOf x :=
    (orderOf_map_dvd q xL).trans ((orderOf_coe xL).symm.dvd)
  have hdiv8 : orderOf (q xL) ∣ 8 := hD8 ▸ orderOf_dvd_natCard (q xL)
  have hqo : q xL=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime (orderOf x) 8 from hxodd.coprime_two_right.pow_right 3) hdiv hdiv8)
  have hs : (e.symm xL).2 = 1 := hqo
  have hm := he (e.symm xL).1 (e.symm xL).2
  rw [Prod.mk.eta,e.apply_symm_apply] at hm
  have hx : x = ((e.symm xL).1 : G) := by simpa only [hs,OneMemClass.coe_one,mul_one] using hm
  exact hx.symm ▸ (e.symm xL).1.property

end CFSG.Quasithin.HigmanSims
