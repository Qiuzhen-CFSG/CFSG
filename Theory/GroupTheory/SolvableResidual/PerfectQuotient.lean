module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Solvable residuals over a perfect prime-core quotient

If a finite group modulo its prime core is perfect, its solvable residual
maps onto that quotient. Restricting the literal quotient map has kernel
exactly the residual's own prime core. The prime core supplements the
residual, so the quotient by the residual is a prime-group.

These statements do not identify the original group with its residual.
Source application: the parabolic residual in Aschbacher–Smith 13.6.23,
combined manuscript of 1 March 2004, printed p.933/PDF p.950.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] (p : ℕ)
variable [Group.IsPerfect (G ⧸ pCore p G)]

/-- Restriction of the original quotient map is onto. -/
theorem residual_core_quotient_surjective :
    Function.Surjective ((QuotientGroup.mk' (pCore p G)).comp (solvableResidual G).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, range_subtype,
    map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _), solvableResidual_eq_top]

/-- The quotient identification induced by inclusion of the residual. -/
noncomputable def solvableResidualPCoreQuotientEquiv :
    (solvableResidual G ⧸ pCore p (solvableResidual G)) ≃* (G ⧸ pCore p G) :=
  QuotientGroup.liftEquiv (pCore p (solvableResidual G))
    (residual_core_quotient_surjective p) (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        pCore_subnormal_eq_comap p (inferInstance : (solvableResidual G).Normal).isSubnormal])

/-- The induced identification retains the literal quotient map. -/
theorem solvableResidualPCoreQuotientEquiv_mk (x : solvableResidual G) :
    solvableResidualPCoreQuotientEquiv p (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' (pCore p G) x.val := rfl

/-- The prime core supplements the residual, so the remaining quotient is a prime-group. -/
theorem quotient_solvableResidual_isPGroup_of_perfect_pCore_quotient :
    IsPGroup p (G ⧸ solvableResidual G) := by
  have hm : (solvableResidual G).map (QuotientGroup.mk' (pCore p G)) = ⊤ := by
    rw [map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _), solvableResidual_eq_top]
  have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore p G))) hm
  rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at hh
  exact isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hh
end Subgroup

end
