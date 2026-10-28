module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleSolvableComparison

/-!
# Solvable kernels over a simple generalized Fitting subgroup

A solvable normal kernel lies in the embedded center of a quasisimple
generalized Fitting subgroup. If that component is simple, perfectness makes
its center trivial, so the original homomorphism is injective. Surjectivity
is not required.

The original point-action comparison in Aschbacher--Smith 13.2.12, printed
p.882, uses this to transport the B.5 component models across the actual
solvable-kernel map in the simple-component rows of F.6.18.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

/-- A solvable kernel is trivial when the source generalized Fitting subgroup
is both quasisimple and simple. -/
theorem injective_of_simple_fitting_of_solvable_kernel
    {D E : Type*} [Group D] [Group E] [Finite D]
    [IsQuasisimple (generalizedFitting D)] [IsSimpleGroup (generalizedFitting D)]
    (g : D →* E) [Group.IsSolvable g.ker] : Function.Injective g := by
  have hz : center (generalizedFitting D) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (generalizedFitting D))
      inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (generalizedFitting D)
        (center_eq_top_iff.mp h)).elim
  apply (MonoidHom.ker_eq_bot_iff g).mp
  apply bot_unique
  have h := solvable_kernel_le_fitting_center g
  simpa only [hz,Subgroup.map_bot] using h

end Theory.GroupTheory
