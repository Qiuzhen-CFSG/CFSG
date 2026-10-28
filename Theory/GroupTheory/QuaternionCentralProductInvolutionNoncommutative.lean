module
public import Theory.GroupTheory.QuaternionCentralProductInvolutionGeneration

/-!
# Noncommutativity of an involution centralizer in Q8*Q8

The intrinsic derived subgroup is the shared central involution line, hence
nontrivial. The ambient version keeps the actual inclusion and containing
group, supplying nonabelianity for source 14.3.18(4).
-/

public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
include d in
theorem involution_centralizer_noncommutative (t:Q) (ht:orderOf t=2)
    (hnc:t∉center Q) : ¬IsMulCommutative (centralizer ({t}:Set Q)) := by
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1:center Q)).mp d.center_card
  have hz2 : orderOf (z:Q)=2 :=
    (Subgroup.orderOf_coe z).trans (orderOf_eq_prime (d.center_square z) hz)
  have htz : t≠(z:Q) := fun he=>hnc (he ▸ z.property)
  obtain ⟨_,hc⟩ := quaternion_central_product_involution_centralizer_geometry
    d.left d.right d.left_model.some d.right_model.some d.span d.intersection_card
    d.commute z t hz2 z.property ht htz
  intro ha
  let := ha
  rw [commutator_eq_bot,map_bot] at hc
  have he : (z:Q)=1 := by
    have hzmem := mem_zpowers (z:Q)
    rw [←hc] at hzmem
    exact hzmem
  exact hz (Subtype.ext he)

/-- A subgroup containing the literal ambient involution centralizer is
noncommutative. -/
theorem ambient_involution_centralizer_overgroup_noncommutative
    {G : Type*} [Group G] [Finite G] (U R : Subgroup G)
    (dU : QuaternionCentralProductData U) (t:U) (ht:orderOf t=2)
    (hnc:t∉center U)
    (hle : (centralizer ({t}:Set U)).map U.subtype≤R) : ¬IsMulCommutative R := by
  intro hR
  let := hR
  apply dU.involution_centralizer_noncommutative t ht hnc
  refine ⟨⟨fun x y=>?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z:R=>(z:G)) (IsMulCommutative.is_comm.comm
    (⟨(x:U),hle (mem_map_of_mem U.subtype x.property)⟩:R)
    (⟨(y:U),hle (mem_map_of_mem U.subtype y.property)⟩:R))
end Subgroup.QuaternionCentralProductData
