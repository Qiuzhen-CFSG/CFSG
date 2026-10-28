module
public import CFSG.Quasithin.ChapterB.InternalThompsonAction

/-!
# Fixed vectors of the literal internal Thompson action

The fixed space of a subgroup image is exactly its original conjugation
centralizer. This identifies the source fixed seed before passing to the
central quotient used in B.5.1 and 10.2.9.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.InternalThompsonAction
variable {H : Type*} [Group H]

theorem mem_fixedSpace_iff (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (K : Subgroup H) (u : Additive U) :
    u ∈ fixedSpace (action U) (K.map (actionMk U)) ↔
      (u.toMul : H) ∈ centralizer (K : Set H) := by
  constructor
  · intro hf k hk
    have ha := action_apply U k u
    have he := congrArg (fun v : Additive U => ((v.toMul : U) : H))
      (hf ⟨actionMk U k,mem_map_of_mem _ hk⟩)
    change (((action U (actionMk U k) u).toMul : U) : H) = (u.toMul : H) at he
    rw [he] at ha
    exact mul_inv_eq_iff_eq_mul.mp ha.symm
  · intro hc g
    obtain ⟨k,hk,hkg⟩ := g.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change (((action U (g : ActionQuotient U) u).toMul : U) : H) = _
    rw [←hkg,action_apply U]
    rw [hc k hk,mul_inv_cancel_right]

end CFSG.Quasithin.ChapterB.InternalThompsonAction
