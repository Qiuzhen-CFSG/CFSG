module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCentralizers

/-!
# Involutory generators of the noncentral involution centralizer

The existing intrinsic Q₈*Q₈ calculation generates each noncentral
involution centralizer by involutions. This exports generation within
that subgroup and transports it through the actual ambient inclusion.
It supplies the W-generation input in source 14.3.18(4), without choosing
a new abstract C₂×D₈ in place of the literal W.
-/

public section
namespace Subgroup.QuaternionCentralProductData
open Subgroup
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

include d in
theorem involution_centralizer_generated (t : Q) (ht : orderOf t = 2)
    (hnc : t ∉ center Q) :
    closure {x : centralizer ({t} : Set Q) | x ^ 2 = 1} = ⊤ := by
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
  have hz2 : orderOf (z : Q) = 2 := by
    exact (Subgroup.orderOf_coe z).trans (orderOf_eq_prime (d.center_square z) hz)
  have htz : t ≠ (z : Q) := by intro he; exact hnc (he ▸ z.property)
  obtain ⟨hg,_⟩ := quaternion_central_product_involution_centralizer_geometry
    d.left d.right d.left_model.some d.right_model.some d.span d.intersection_card
    d.commute z t hz2 z.property ht htz
  let C := centralizer ({t} : Set Q)
  apply map_injective C.subtype_injective
  rw [← MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm (map_subtype_le _)
  apply hg.ge.trans
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hx,hx2⟩
  refine ⟨⟨x,hx⟩, ?_, rfl⟩
  apply subset_closure
  apply Subtype.ext
  change x ^ 2 = 1
  simpa only [hx2] using pow_orderOf_eq_one x

theorem ambient_involution_centralizer_generated
    {G : Type*} [Group G] [Finite G] (U C : Subgroup G)
    (dU : QuaternionCentralProductData U) (t : U) (ht : orderOf t = 2)
    (hnc : t ∉ center U)
    (hC : C = (centralizer ({t} : Set U)).map U.subtype) :
    closure {x : C | x ^ 2 = 1} = ⊤ := by
  let D := centralizer ({t} : Set U)
  let e : D ≃* C :=
    (D.equivMapOfInjective U.subtype U.subtype_injective).trans (MulEquiv.subgroupCongr hC.symm)
  have hgen := dU.involution_centralizer_generated t ht hnc
  have hle : closure {x : D | x ^ 2 = 1} ≤
      (closure {x : C | x ^ 2 = 1}).comap e.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    apply subset_closure
    change e x ^ 2 = 1
    rw [← map_pow,hx,map_one]
  rw [hgen] at hle
  apply top_unique
  intro c _
  have hh := hle (mem_top (e.symm c))
  change e (e.symm c) ∈ closure {x : C | x ^ 2 = 1} at hh
  simpa only [e.apply_symm_apply] using hh

end Subgroup.QuaternionCentralProductData
