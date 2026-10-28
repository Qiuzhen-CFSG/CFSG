module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalStructure

/-!
# The intrinsic first Hall--Janko cores and quotients

The checked order of the four-generator radical discharges the kernel
conditions for the concrete five-block actions. Since A₅ and S₅ have trivial
two-core, these kernels are exactly the intrinsic two-cores of the literal
numerators `Seed.l₁` and `Seed.l₁s`. The first is thereby identified with the
radical whose commuting quaternion and dihedral factors were constructed in
`RadicalStructure`.

All statements below are unconditional on the fixed ATLAS degree-100 carrier
and its concrete permutation extension. The source-facing first-parabolic
module uses these equivalences to express the central product and PSL₂(4)
clauses of Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263 (PDF p.274).
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Theory.GroupTheory Seed QuotientActions

/-- The literal centralizer's intrinsic two-core is the fixed radical. -/
theorem l₁_core_eq : pCore 2 l₁ = radical.subgroupOf l₁ :=
  l₁_core_eq_of_radical_action card_radical innerAction innerAction_surjective
    (innerAction_ker card_radical)

/-- The full outer numerator has the same radical, included in the extension. -/
theorem l₁s_core_eq : pCore 2 l₁s = outerRadical.subgroupOf l₁s :=
  l₁s_core_eq_of_radical_action card_radical outerAction outerAction_surjective
    (outerAction_ker card_radical)

/-- Transport the constructed quaternion--dihedral factors to the intrinsic core. -/
noncomputable def radicalCoreEquiv : radical ≃* pCore 2 l₁ :=
  (Subgroup.subgroupOfEquivOfLe radical_le_l₁).symm.trans
    (MulEquiv.subgroupCongr l₁_core_eq.symm)

/-- The actual five-block action identifies the inner quotient with A₅. -/
theorem l₁_quotient : Nonempty ((l₁ ⧸ pCore 2 l₁) ≃* alternatingGroup (Fin 5)) :=
  l₁_quotient_of_radical_action card_radical innerAction innerAction_surjective
    (innerAction_ker card_radical)

/-- The outer word extends the five-block quotient to the full S₅. -/
theorem l₁s_quotient : Nonempty ((l₁s ⧸ pCore 2 l₁s) ≃* Equiv.Perm (Fin 5)) :=
  l₁s_quotient_of_radical_action card_radical outerAction outerAction_surjective
    (outerAction_ker card_radical)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
