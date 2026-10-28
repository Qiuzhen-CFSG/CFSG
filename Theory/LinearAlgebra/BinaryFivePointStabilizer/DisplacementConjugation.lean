module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the actual point-stabilizer displacement kernel

The point stabilizer fixes the marked line pointwise. Conjugation therefore
acts on quotient-to-line displacement maps by precomposition with the inverse
quotient action. An invariant displacement map determines a fixed kernel
element through the original displacement equivalence.
-/

public section
namespace Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The actual conjugation action is the contragredient quotient action on
displacements; the target line is fixed pointwise. -/
theorem kernelDisplacement_conjugation (z : E) (g : stabilizer z) (d : kernel z)
    (x : QuotientSpace z) :
    kernelDisplacement z (MulAut.conjNormal g d) x =
      kernelDisplacement z d ((quotientAction z g)⁻¹ x) := by
  rw [←map_inv]
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply Subtype.ext
    change (kernelDisplacement z (MulAut.conjNormal g d) ((line z).mkQ x) : E) =
      (kernelDisplacement z d (quotientAction z g⁻¹ ((line z).mkQ x)) : E)
    rw [quotientAction_mk,kernelDisplacement_mk,kernelDisplacement_mk]
    change g.val (d.val.val (g.val.symm x))-x =
      d.val.val (g.val.symm x)-g.val.symm x
    have hf := fixes_line z g _
      ((mem_kernel_iff z d.val).mp d.property (g.val.symm x))
    rw [map_sub,g.val.apply_symm_apply] at hf
    exact hf

/-- An invariant displacement map fixes the original kernel element. -/
theorem conjNormal_eq_self_of_displacement_fixed (z : E) (g : stabilizer z)
    (d : kernel z)
    (h : ∀ x : QuotientSpace z,
      kernelDisplacement z d ((quotientAction z g)⁻¹ x) = kernelDisplacement z d x) :
    MulAut.conjNormal g d = d := by
  apply (kernelDisplacementEquiv z).injective
  simp only [kernelDisplacementEquiv_apply]
  apply congrArg Multiplicative.ofAdd
  apply LinearMap.ext
  intro x
  exact (kernelDisplacement_conjugation z g d x).trans (h x)

end Theory.LinearAlgebra.BinaryFivePointStabilizer
