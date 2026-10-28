module
public import Theory.GroupTheory.ClassTwoCommutator
public import Mathlib.GroupTheory.NoncommCoprod
/-! # Class two under faithful maps and commuting products
A faithful subgroup of a class-two image is class two. Surjective marked
maps and multiplication of commuting factors preserve the same property.
The application is the original crossing Thompson product in 2.5.7.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement Pointwise
namespace Subgroup.ClassTwo
variable {G H:Type*} [Group G] [Group H]
theorem of_injective (f:G→*H) (hf:Function.Injective f) (hc:_root_.commutator H≤center H) :
    _root_.commutator G≤center G := by
  apply commutator_le.mpr
  intro a _ b _
  apply mem_center_iff.mpr
  intro x
  apply hf
  simpa only [map_mul,map_commutatorElement] using
    mem_center_iff.mp (hc (commutator_mem_commutator (mem_top (f a)) (mem_top (f b)))) (f x)

theorem of_surjective (f:G→*H) (hf:Function.Surjective f) (hc:_root_.commutator G≤center G) :
    _root_.commutator H≤center H := by
  apply commutator_le.mpr
  intro a _ b _
  obtain ⟨a,rfl⟩:=hf a
  obtain ⟨b,rfl⟩:=hf b
  apply mem_center_iff.mpr
  intro x
  obtain ⟨x,rfl⟩:=hf x
  simpa only [map_mul,map_commutatorElement] using congrArg f
    (mem_center_iff.mp (hc (commutator_mem_commutator (mem_top a) (mem_top b))) x)

theorem prod (hG:_root_.commutator G≤center G) (hH:_root_.commutator H≤center H) :
    _root_.commutator (G×H)≤center (G×H) := by
  apply commutator_le.mpr
  rintro ⟨a,b⟩ _ ⟨c,d⟩ _
  apply mem_center_iff.mpr
  rintro ⟨x,y⟩
  exact Prod.ext
    (mem_center_iff.mp (hG (commutator_mem_commutator (mem_top a) (mem_top c))) x)
    (mem_center_iff.mp (hH (commutator_mem_commutator (mem_top b) (mem_top d))) y)

theorem commuting_product (K C:Subgroup G) (hc:K≤centralizer (C:Set G))
    (hK:_root_.commutator K≤center K) (hC:_root_.commutator C≤center C) :
    _root_.commutator (K⊔C:Subgroup G)≤center (K⊔C:Subgroup G) := by
  have hcomm (k:K) (c:C):Commute (k:G) (c:G):=(hc k.property c c.property).symm
  let f:K×C→*(K⊔C:Subgroup G):=
    (K.subtype.noncommCoprod C.subtype hcomm).codRestrict (K⊔C)
      (fun u=>mul_mem_sup u.1.property u.2.property)
  have hf:Function.Surjective f:=by
    rintro ⟨x,hx⟩
    have hx':x∈(K:Set G)*(C:Set G):=by
      rw [←coe_mul_of_left_le_normalizer_right K C (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨k,hk,c,hc,h⟩:=hx'
    exact ⟨(⟨k,hk⟩,⟨c,hc⟩),Subtype.ext h⟩
  exact of_surjective f hf (prod hK hC)
end Subgroup.ClassTwo
namespace Subgroup.ClassTwo
variable {G H E:Type*} [Group G] [Group H] [Group E]
theorem of_injective_range_le_image (A:Subgroup G) (f:G→*H)
    (hA:_root_.commutator A≤center A) (j:E→*H) (hj:Function.Injective j)
    (himage:j.range≤A.map f) : _root_.commutator E≤center E := by
  let r:A→*A.map f:=(f.comp A.subtype).codRestrict (A.map f) (fun a=>mem_map_of_mem f a.property)
  have hr:Function.Surjective r:=by
    rintro ⟨y,⟨a,ha,h⟩⟩
    exact ⟨⟨a,ha⟩,Subtype.ext h⟩
  let k:E→*A.map f:=j.codRestrict (A.map f) (fun x=>himage ⟨x,rfl⟩)
  have hk:Function.Injective k:=fun _ _ h=>hj (congrArg Subtype.val h)
  exact of_injective k hk (of_surjective r hr hA)
end Subgroup.ClassTwo
