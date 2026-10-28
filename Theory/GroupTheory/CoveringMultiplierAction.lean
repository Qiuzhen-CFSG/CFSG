module

public import Theory.GroupTheory.Covering

/-!
# The canonical action on a universal covering kernel

Uniqueness of lifts gives a homomorphism from base automorphisms to the
stabilizer of the covering kernel. Restriction gives the canonical action
on that literal kernel, which represents the Schur multiplier. Its
evaluation law retains the chosen covering map and its unique lift.

This supplies the action used in Aschbacher--Smith I.2.2(7a), printed p.412,
without assuming either nontriviality or irreducibility of any specific action.
-/

namespace Theory.GroupTheory.Covering

universe u
variable {K L : Type u}
variable [Group K] [Finite K] [IsQuasisimple K]
variable [Group L] [Finite L] [IsQuasisimple L]

/-- Restrict an automorphism stabilizing the kernel to that kernel. -/
@[expose] public def kernelRestriction (f : Covering L K) :
    kernelStabilizer f →* MulAut f.toMonoidHom.ker where
  toFun a := {
    toFun x := ⟨a.val x, (a.property x).mp x.property⟩
    invFun x := ⟨a.val.symm x, (a.property (a.val.symm x)).mpr (by
      rw [a.val.apply_symm_apply]
      exact x.property)⟩
    left_inv x := Subtype.ext (a.val.symm_apply_apply x)
    right_inv x := Subtype.ext (a.val.apply_symm_apply x)
    map_mul' x y := Subtype.ext (map_mul a.val (x : L) (y : L)) }
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

/-- The automorphism action induced by unique universal lifts. -/
@[expose] public noncomputable def multiplierAction (f : Covering L K)
    (hf : IsUniversal.{u,u,u} f) : MulAut K →* MulAut f.toMonoidHom.ker :=
  (kernelRestriction f).comp hf.liftMulAutToStabilizer

/-- The action is the restriction of the unique lift, with no choice of
coordinates on the multiplier. -/
@[simp] public theorem multiplierAction_apply (f : Covering L K)
    (hf : IsUniversal.{u,u,u} f) (a : MulAut K) (x : f.toMonoidHom.ker) :
    (multiplierAction f hf a x : L) = hf.liftMulAut a x := rfl

end Theory.GroupTheory.Covering
