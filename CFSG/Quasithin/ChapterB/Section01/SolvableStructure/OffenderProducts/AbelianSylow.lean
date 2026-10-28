module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.Representation.BinaryOffender.Stability
/-!
# Two-subgroups in the actual solvable FF product

Each coordinate is S₃, so every two-subgroup of the offender product has
exponent two. If an abelian Sylow acts transitively on the factor family,
a nontrivial intersection with a factor is fixed by that Sylow. Independence
then forces the family to contain a single factor.

Source: Aschbacher–Smith B.1.8 and B.6.9, used in C.1.28, pp.132–134.
-/
public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

include d in
omit [Finite G] in
theorem two_subgroup_elementary (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAY : A ≤ offenderSubgroup ρ) : IsElementaryAbelian 2 A := by
  let f := d.groupProduct.symm.toMonoidHom.comp (inclusion hAY)
  have hfi : Function.Injective f := d.groupProduct.symm.injective.comp (inclusion_injective hAY)
  have hp (a : A) : a^2=1 := by
    apply hfi
    rw [map_pow, map_one]
    apply funext
    intro i
    let fi := (Pi.evalMonoidHom (fun i => d.factor i) i).comp f
    have hcop : Nat.Coprime (orderOf (fi a)) 3 :=
      (hA.orderOf_coprime (by decide : Nat.Coprime 2 3) a).of_dvd_left (orderOf_map_dvd fi a)
    have hd : orderOf (fi a) ∣ 2*3 := by
      have hh := orderOf_dvd_natCard (fi a)
      rwa [d.factor_card] at hh
    have hh : (fi a)^2=1 := orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_mul_right.mp hd)
    exact hh
  refine { is_comm := ?_, exponent_dvd_p := ?_ }
  · exact ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (hp a)) x y).eq⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp


theorem count_eq_one_of_abelian_sylow_transitive
    (T : Sylow 2 G) (hT : IsMulCommutative T)
    (htrans : ∀ i j, ∃ t : T,
      (d.factor i).map (MulAut.conj (t : G)).toMonoidHom = d.factor j) : d.count = 1 := by
  have heq (i j : Fin d.count) : i=j := by
    by_contra hij
    let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
    have hs : (d.factor i).IsSubnormal :=
      (d.factor_normal_in_offenderSubgroup i).isSubnormal.trans (d.factor_le_offenderSubgroup i)
        (inferInstance : (offenderSubgroup ρ).Normal).isSubnormal
    obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal (d.factor i) hs
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (d.factorSylow_ne_bot i P)
    let x : G := a
    have hx : x ∈ d.factorSylow i P := a.property
    have hne : x ≠ 1 := fun hh => ha (Subtype.ext hh)
    have hxi : x ∈ d.factor i := d.factorSylow_le i P hx
    have hxT : x ∈ (T : Subgroup G) := by
      obtain ⟨y,hy,hyx⟩ := hx
      change y ∈ (P : Subgroup (d.factor i)) at hy
      rw [hP] at hy
      rw [←hyx]
      exact hy
    obtain ⟨t,ht⟩ := htrans i j
    have htx : (t : G)*x*(t : G)⁻¹=x := by
      have hh := congrArg Subtype.val (hT.is_comm.comm t (⟨x,hxT⟩ : T))
      change (t : G)*x=x*(t : G) at hh
      rw [hh,mul_inv_cancel_right]
    have hxj : x ∈ d.factor j := by
      rw [←ht]
      have hh := mem_map_of_mem (MulAut.conj (t : G)).toMonoidHom hxi
      change (t : G)*x*(t : G)⁻¹ ∈ _ at hh
      rwa [htx] at hh
    exact hne ((Subgroup.disjoint_def.mp (d.factors_independent.pairwiseDisjoint hij)) hxi hxj)
  by_contra hn
  have hpos := d.count_pos
  have htwo : 1 < d.count := by omega
  have hh := congrArg Fin.val (heq ⟨0,hpos⟩ ⟨1,htwo⟩)
  change 0=1 at hh
  omega
end CFSG.Quasithin.ChapterB.SolvableFFFactors
