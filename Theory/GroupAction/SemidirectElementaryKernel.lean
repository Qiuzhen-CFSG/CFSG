module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.Group

/-!
# Elementary kernels in a semidirect product

For a commutative subgroup of a semidirect product, a coboundary for one
actor conjugates the kernel of the right projection into its coefficient
fixed group. Both maps retain the literal projection kernel and are injective.
This is the group-theoretic transport used in the G₂ field-offender exclusion.
Source: Aschbacher–Smith B.4.6(9), (13), and 16.1.7(3a).
-/

public section
open scoped IsMulCommutative

namespace Theory.GroupTheory.SemidirectElementaryKernel
variable {N C : Type*} [Group N] [Group C] {φ : C →* MulAut N}

/-- The actual projection kernel embeds by its first coordinate. -/
def kernelLeft (E : Subgroup (N ⋊[φ] C)) :
    ((SemidirectProduct.rightHom : N ⋊[φ] C →* C).comp E.subtype).ker →* N where
  toFun x := x.1.1.left
  map_one' := rfl
  map_mul' x y := by
    have hx : x.1.1.right = 1 := x.2
    change x.1.1.left * φ x.1.1.right y.1.1.left = _
    simp only [hx, map_one, MulAut.one_apply]

theorem kernelLeft_injective (E : Subgroup (N ⋊[φ] C)) :
    Function.Injective (kernelLeft E) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext h
  exact x.2.trans y.2.symm

/-- Conjugating by the inverse coboundary places the kernel in the pure fixed group. -/
def kernelFixed (E : Subgroup (N ⋊[φ] C)) [IsMulCommutative E]
    (z : E) (c : N) (hc : z.1.left = c * φ z.1.right c⁻¹) :
    ((SemidirectProduct.rightHom : N ⋊[φ] C →* C).comp E.subtype).ker →*
      (φ z.1.right).fixedSubgroup := by
  let f := (MulAut.conj c⁻¹).toMonoidHom.comp (kernelLeft E)
  refine f.codRestrict _ ?_
  intro x
  rw [MulAut.mem_fixedSubgroup]
  change φ z.1.right (c⁻¹ * x.1.1.left * (c⁻¹)⁻¹) = c⁻¹ * x.1.1.left * (c⁻¹)⁻¹
  rw [inv_inv]
  have hx : x.1.1.right = 1 := x.2
  have hcomm := congrArg (fun a : E => a.1.left)
    (IsMulCommutative.is_comm.comm x.1 z)
  change x.1.1.left * φ x.1.1.right z.1.left =
    z.1.left * φ z.1.right x.1.1.left at hcomm
  simp only [hx, map_one, MulAut.one_apply] at hcomm
  have hfix : z.1.left * φ z.1.right x.1.1.left * z.1.left⁻¹ = x.1.1.left := by
    rw [← hcomm, mul_inv_cancel_right]
  calc
    _ = c⁻¹ * (z.1.left * φ z.1.right x.1.1.left * z.1.left⁻¹) * c := by
      rw [hc]
      simp only [map_mul, map_inv]
      group
    _ = _ := by rw [hfix]

theorem kernelFixed_injective (E : Subgroup (N ⋊[φ] C)) [IsMulCommutative E]
    (z : E) (c : N) (hc : z.1.left = c * φ z.1.right c⁻¹) :
    Function.Injective (kernelFixed E z c hc) := by
  intro x y h
  apply kernelLeft_injective E
  exact (MulAut.conj c⁻¹).injective (congrArg Subtype.val h)

end Theory.GroupTheory.SemidirectElementaryKernel
