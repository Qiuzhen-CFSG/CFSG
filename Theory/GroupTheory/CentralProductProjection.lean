module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-! # Projection from a commuting product
Multiplication from the two factors descends a marked quotient of the first
factor whenever its kernel is exactly their intersection. The resulting map
kills precisely the second factor, so every disjoint subgroup embeds into the
same marked quotient. No finiteness or elementary-factor assumption is needed.
Source: Aschbacher--Smith 2.5.7, printed p.555, the conjugate-core embedding.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G Y:Type*} [Group G] [Group Y]
theorem exists_sup_projection (K C:Subgroup G) (hc:K≤centralizer (C:Set G))
    (q:K→*Y) (hq:q.ker=C.subgroupOf K) :
    ∃ π:(K⊔C:Subgroup G)→*Y,
      (∀k:K,π (inclusion le_sup_left k)=q k) ∧
      π.ker=C.subgroupOf (K⊔C) := by
  have hcomm (k:K) (c:C):Commute (k:G) (c:G):=(hc k.property c c.property).symm
  let f:K×C→*(K⊔C:Subgroup G):=
    (K.subtype.noncommCoprod C.subtype hcomm).codRestrict (K⊔C)
      (fun u=>mul_mem_sup u.1.property u.2.property)
  have hf:Function.Surjective f:=by
    rintro ⟨x,hx⟩
    have hx':x∈(K:Set G)*(C:Set G):=by
      rw [←coe_mul_of_left_le_normalizer_right K C (hc.trans (centralizer_le_normalizer _))]
      exact hx
    obtain ⟨k,hk,c,hc,h⟩:=hx'
    exact ⟨(⟨k,hk⟩,⟨c,hc⟩),Subtype.ext h⟩
  let g:K×C→*Y:=q.comp (MonoidHom.fst K C)
  have hk:f.ker≤g.ker:=by
    rintro ⟨k,c⟩ hk
    have he:(k:G)*(c:G)=1:=congrArg Subtype.val hk
    change q k=1
    apply MonoidHom.mem_ker.mp
    rw [hq]
    change (k:G)∈C
    rw [eq_inv_of_mul_eq_one_left he]
    exact C.inv_mem c.property
  let e:=QuotientGroup.quotientKerEquivOfSurjective f hf
  let π:(K⊔C:Subgroup G)→*Y:=(QuotientGroup.lift f.ker g hk).comp e.symm.toMonoidHom
  have hπ (u:K×C):π (f u)=q u.1:=by
    change QuotientGroup.lift f.ker g hk (e.symm (f u))=_
    rw [show f u=e (QuotientGroup.mk' f.ker u) from rfl,e.symm_apply_apply]
    rfl
  refine ⟨π,?_,?_⟩
  · intro k
    have he:f (k,1)=inclusion le_sup_left k:=Subtype.ext (mul_one _)
    rw [←he,hπ]
  · ext x
    obtain ⟨⟨k,c⟩,rfl⟩:=hf x
    change π (f (k,c))=1 ↔ (k:G)*(c:G)∈C
    rw [hπ,←MonoidHom.mem_ker,hq]
    change (k:G)∈C ↔ (k:G)*(c:G)∈C
    constructor
    · exact fun hk=>C.mul_mem hk c.property
    · intro hk
      have he:=C.mul_mem hk (C.inv_mem c.property)
      simpa only [mul_inv_cancel_right] using he

theorem exists_injective_of_disjoint_sup (K C D:Subgroup G)
    (hc:K≤centralizer (C:Set G)) (q:K→*Y) (hq:q.ker=C.subgroupOf K)
    (hD:D≤K⊔C) (hd:Disjoint D C) :
    ∃j:D→*Y,Function.Injective j := by
  obtain ⟨π,_,hker⟩:=exists_sup_projection K C hc q hq
  let j:=π.comp (inclusion hD)
  refine ⟨j,?_⟩
  rw [←MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro d hd'
  have he:(inclusion hD d)∈π.ker:=hd'
  rw [hker] at he
  exact Subtype.ext (disjoint_def.mp hd d.property he)
end Subgroup
