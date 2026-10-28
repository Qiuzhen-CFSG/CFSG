module
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Equivariant group equivalence from full graph-action rigidity

If faithful group actions on two graphs realize every graph automorphism by a
group element, a graph isomorphism induces a unique equivariant group
equivalence.
-/

@[expose] public section
noncomputable section
namespace SimpleGraph
variable {G H X Y:Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
variable [FaithfulSMul G X] [FaithfulSMul H Y]
variable {Γ:SimpleGraph X} {Λ:SimpleGraph Y}
variable (hG:∀g:G,∀x y,Γ.Adj (g•x) (g•y)↔Γ.Adj x y)
variable (hH:∀k:H,∀x y,Λ.Adj (k•x) (k•y)↔Λ.Adj x y)
variable (fullG:∀a:Γ≃gΓ,∃g:G,∀x,a x=g•x)
variable (fullH:∀a:Λ≃gΛ,∃k:H,∀y,a y=k•y)

include hG hH fullG fullH in
theorem exists_equivariant_groupEquiv (e:Γ≃gΛ) :
    ∃f:G≃*H,∀g x,e (g•x)=f g•e x := by
  classical
  let a (g:G):Γ≃gΓ:={toEquiv:=MulAction.toPerm g,map_rel_iff':=hG g _ _}
  let b (k:H):Λ≃gΛ:={toEquiv:=MulAction.toPerm k,map_rel_iff':=hH k _ _}
  have hex:∀g:G,∃k:H,∀x:X,e (g•x)=k•e x:=by
    intro g
    obtain ⟨k,hk⟩:=fullH (e.symm.trans ((a g).trans e))
    refine ⟨k,fun x=>?_⟩
    have hh:=hk (e x)
    change e (g•e.symm (e x))=k•e x at hh
    simpa only [e.symm_apply_apply] using hh
  choose f hf using hex
  have hi:Function.Injective f:=by
    intro g k hgk
    apply eq_of_smul_eq_smul (α:=X)
    intro x
    apply e.injective
    rw [hf,hf,hgk]
  have hs:Function.Surjective f:=by
    intro k
    obtain ⟨g,hg⟩:=fullG (e.trans ((b k).trans e.symm))
    refine ⟨g,eq_of_smul_eq_smul (α:=Y) ?_⟩
    intro y
    obtain ⟨x,rfl⟩:=e.surjective y
    rw [←hf]
    have hh:=congrArg e (hg x)
    change e (e.symm (k•e x))=e (g•x) at hh
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  have hm:∀g k,f (g*k)=f g*f k:=by
    intro g k
    apply eq_of_smul_eq_smul (α:=Y)
    intro y
    obtain ⟨x,rfl⟩:=e.surjective y
    rw [←hf,mul_smul,hf,mul_smul,←hf,hf]
    exact congrArg (fun z:Y=>f g•z) (hf k x)
  exact ⟨{toEquiv:=Equiv.ofBijective f ⟨hi,hs⟩,map_mul':=hm},hf⟩
end SimpleGraph
