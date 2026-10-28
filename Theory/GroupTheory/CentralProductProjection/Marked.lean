module
public import Theory.GroupTheory.CentralProductProjection
/-! # Marked projection from a full commuting product
Projection along the second factor preserves the supplied map on the first
and identifies its literal kernel. Source application: AS 2.5.7.
-/
public section
open Subgroup
namespace Subgroup
variable {G Q:Type*} [Group G] [Group Q]
theorem exists_marked_projection (K C:Subgroup G)
    (hc:K≤centralizer (C:Set G)) (hgen:K⊔C=⊤)
    (q:K→*Q) (hq:q.ker=C.subgroupOf K) (hs:Function.Surjective q) :
    ∃f:G→*Q, f.comp K.subtype=q ∧ f.ker=C ∧ Function.Surjective f := by
  obtain ⟨π,hπ,hker⟩:=exists_sup_projection K C hc q hq
  let j:G→*(K⊔C:Subgroup G):={
    toFun x:=⟨x,by rw [hgen];trivial⟩
    map_one':=rfl
    map_mul' _ _:=rfl }
  let f:=π.comp j
  have hf:f.comp K.subtype=q:=by
    ext k
    exact hπ k
  refine ⟨f,hf,?_,?_⟩
  · ext x
    change j x∈π.ker ↔ x∈C
    rw [hker]
    rfl
  · intro y
    obtain ⟨k,hk⟩:=hs y
    exact ⟨k,show (f.comp K.subtype) k=y from hf.symm ▸ hk⟩
end Subgroup
