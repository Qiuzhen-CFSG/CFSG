module

public import Theory.GroupTheory.SolvableResidual

/-!
# Commutators above the solvable residual in an abelian extension

A surjection maps the finite solvable residual onto the quotient residual.
Its full preimage is therefore the product of the original residual and the
kernel. Modulo the original residual this preimage is abelian whenever the
kernel is abelian. Its subgroups consequently have commutators in the residual.

This is the nonsplitting step used for the triple cover in Aschbacher–Smith,
J.2.7, printed p.437 (PDF p.448).
-/

public section
namespace Subgroup
variable {E Q : Type*} [Group E] [Finite E] [Group Q]
/-- In an extension with abelian kernel, commutators above the solvable
residual of the quotient lie in the solvable residual of the domain. -/
theorem commutator_le_solvableResidual_of_image_le (f : E →* Q)
    (hf : Function.Surjective f) [IsMulCommutative f.ker]
    (H : Subgroup E) (hH : H.map f ≤ solvableResidual Q) :
    ⁅H,H⁆ ≤ solvableResidual E := by
  have hle : H ≤ solvableResidual E ⊔ f.ker := by
    rw [← comap_map_eq, map_solvableResidual_eq f hf]
    exact map_le_iff_le_comap.mp hH
  let q := QuotientGroup.mk' (solvableResidual E)
  have hmap : (solvableResidual E ⊔ f.ker).map q = f.ker.map q := by
    rw [map_sup, show (solvableResidual E).map q = ⊥ from
      (map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
  apply (commutator_mono hle hle).trans
  rw [← QuotientGroup.ker_mk' (solvableResidual E), ← map_eq_bot_iff, map_commutator]
  rw [QuotientGroup.ker_mk']
  change ⁅(solvableResidual E ⊔ f.ker).map q, (solvableResidual E ⊔ f.ker).map q⁆ = ⊥
  rw [hmap]
  exact commutator_self_eq_bot_iff.mpr inferInstance
end Subgroup
