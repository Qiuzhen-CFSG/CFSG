module
public import Theory.LinearAlgebra.FieldFourTransvectionPairs
public import Theory.SpecificGroups.PSL2.LargeOddInverter

/-!
# No faithful PSL₂(31) action contains a transvection over F₄

The split torus in PSL₂(31) is cyclic of order fifteen and has a reflection.
Involution fusion moves that reflection onto any prescribed involution.
The product of this involution and a torus conjugate has order fifteen.
A faithful action therefore contradicts the elementary order restriction
for two F₄ transvections. Both the torus and conjugating elements belong
to the given concrete PSL₂ model.

Source: the multiplicity argument of Aschbacher–Smith 8.2.9, printed p.721,
refs/quasithin.pdf; torus data are Huppert II.8.3.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

theorem exists_fifteen_inverted_thirty_one
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F=31)
    (t : PSL(2,F)) (ht : orderOf t=2) :
    ∃ r : PSL(2,F), orderOf r=15 ∧ t*r*t⁻¹=r⁻¹ := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
    BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data
      (F := F) (p := 31) (f := 1) (by simpa only [pow_one] using hF)
  have hUcard : Nat.card U=15 := by norm_num [hF] at hcard; exact hcard
  let := hU
  obtain ⟨r,hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  have hwc : orderOf w=2 := orderOf_eq_prime (by simpa only [pow_two] using hw2)
    (fun he => hw (he ▸ U.one_mem))
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj w t hwc ht)
  refine ⟨c*(r:PSL(2,F))*c⁻¹,?_,?_⟩
  · change orderOf (MulAut.conj c (r:PSL(2,F)))=15
    rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hr,hUcard]
  · rw [←hc]
    calc
      _ = c*(w*(r:PSL(2,F))*w⁻¹)*c⁻¹ := by group
      _ = c*(r:PSL(2,F))⁻¹*c⁻¹ := by rw [hi r r.property]
      _ = _ := by group

end Theory.PSL2

namespace Representation
variable {G F k X : Type*} [Group G] [Field F] [Finite F]
  [Field k] [Finite k] [CharP k 2] [AddCommGroup X] [Module k X]
  [FiniteDimensional k X]

theorem no_faithful_thirty_one_field_four_transvection
    (hF : Nat.card F=31) (hk : Nat.card k=4) (e : G ≃* PSL(2,F))
    (μ : G →* (X ≃ₗ[k] X)) (hμ : Function.Injective μ)
    (t : G) (ht : orderOf t=2)
    (hr : Module.finrank k (LinearMap.range ((μ t).toLinearMap-1)) ≤ 1) : False := by
  obtain ⟨r,hr15,hi⟩ := Theory.PSL2.exists_fifteen_inverted_thirty_one hF
    (e t) ((e.orderOf_eq t).trans ht)
  let x := e.symm r
  have hx : orderOf x=15 := (e.symm.orderOf_eq r).trans hr15
  have hix : t*x*t⁻¹=x⁻¹ := by
    apply e.injective
    simpa only [map_mul,map_inv,x,e.apply_symm_apply] using hi
  have ht2 : t*t=1 := by simpa only [pow_two,ht] using pow_orderOf_eq_one t
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht2
  have he : t*(x*t*x⁻¹)=(x^2)⁻¹ := by
    calc
      _ = (t*x*t⁻¹)*x⁻¹ := by rw [hti]; group
      _ = (x^2)⁻¹ := by rw [hix,pow_two,mul_inv_rev]
  have hord : orderOf (t*(x*t*x⁻¹))=15 := by
    rw [he,orderOf_inv,Nat.Coprime.orderOf_pow (show (orderOf x).Coprime 2 by rw [hx]; decide),hx]
  have htμ : μ t ∈ LinearEquiv.transvections k X :=
    LinearEquiv.mem_transvections_of_square_one_rank_one (μ t)
      (by rw [←map_mul,ht2,map_one]) hr
  have hxμ : μ (x*t*x⁻¹) ∈ LinearEquiv.transvections k X := by
    simpa only [map_mul,map_inv] using LinearEquiv.conjugate_mem_transvections (μ x) (μ t) htμ
  apply LinearEquiv.transvection_pair_not_order_fifteen hk (μ t) (μ (x*t*x⁻¹)) htμ hxμ
  rw [←map_mul,orderOf_injective μ hμ,hord]

end Representation
