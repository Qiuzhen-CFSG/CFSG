module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

/-!
# Coordinates on a commuting product from one factor

If C=AB with commuting subgroups, a surjective homomorphism from B whose
kernel is A intersect B extends uniquely across the product by killing A.
Descending the product homomorphism constructs the actual map and preserves
its formula on both original factors. This supplies the HC/HB coordinates
used with the original natural U/Z section in J.2.7(8).
-/

open Subgroup
namespace Subgroup

public theorem exists_hom_from_commuting_product {C W:Type*} [Group C] [Group W]
    (A B:Subgroup C) (hc:∀a:A,∀b:B,Commute (a:C) (b:C)) (ht:A⊔B=⊤)
    (f:B→*W) (hf:Function.Surjective f) (hk:∀b:B,f b=1↔(b:C)∈A) :
    ∃p:C→*W,Function.Surjective p ∧ p.ker=A ∧
      ∀a:A,∀b:B,p ((a:C)*(b:C))=f b := by
  let F := MonoidHom.noncommCoprod A.subtype B.subtype hc
  have hF : Function.Surjective F := by
    apply MonoidHom.range_eq_top.mp
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hc).trans
      ((congrArg₂ (·⊔·) A.range_subtype B.range_subtype).trans ht)
  let ff:=f.comp (MonoidHom.snd A B)
  have hker : F.ker≤ff.ker := by
    intro x hx
    have hx' : (x.1:C)*(x.2:C)=1 := hx
    have hb : (x.2:C)∈A := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact A.inv_mem x.1.property
    exact (hk x.2).mpr hb
  let p:=F.liftOfSurjective hF ⟨ff,hker⟩
  have he (a:A) (b:B) : p ((a:C)*(b:C))=f b :=
    F.liftOfRightInverse_comp_apply (Function.surjInv hF) (Function.rightInverse_surjInv hF)
      ⟨ff,hker⟩ (a,b)
  refine ⟨p,?_,?_,he⟩
  · intro w
    obtain ⟨b,hb⟩ := hf w
    exact ⟨(1:C)*b,(he 1 b).trans hb⟩
  · ext x
    obtain ⟨⟨a,b⟩,rfl⟩ := hF x
    change p ((a:C)*(b:C))=1↔(a:C)*(b:C)∈A
    rw [he,hk]
    exact (A.mul_mem_cancel_left a.property).symm

end Subgroup
