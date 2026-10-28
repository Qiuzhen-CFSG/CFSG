module

public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.AutomorphismFixedResidual
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Lifting the fixed perfect residual through a central quotient

Take the preimage of the quotient's fixed subgroup and then its solvable
residual. Surjectivity carries this perfect group onto the quotient's fixed
perfect residual. The automorphism fixes the lift pointwise: its action and
the inclusion agree modulo a central kernel, and maps from a perfect group
into a central extension are uniquely determined by their quotient maps.

The argument keeps arbitrary central covers, including even centers. It is
the cover reduction needed for the involution-centralizer calculation in
Aschbacher--Smith 15.3.38, printed p.1137.
-/

public section

open Subgroup
namespace MulAut
variable {K Q : Type*} [Group K] [Group Q]

/-- The fixed perfect residual in the quotient has a perfect pointwise-fixed
lift, with no restriction on the center of the covering group. -/
theorem exists_perfect_fixed_lift [Finite K] (e : K ⧸ center K ≃* Q)
    (a : MulAut K) :
    ∃ F : Subgroup K, Group.IsPerfect F ∧ F ≤ a.fixedSubgroup ∧
      F.map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
        fixedPerfectResidual (MulAut.centralQuotientAction e a) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let b := MulAut.centralQuotientAction e a
  let P := b.fixedSubgroup.comap q
  let F := (solvableResidual P).map P.subtype
  have hF : Group.IsPerfect F := Group.IsPerfect.map P.subtype
  let := hF
  have hker : q.ker ≤ center K := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact hx.trans (map_one e).symm
  have hfac : q.comp (a.toMonoidHom.comp F.subtype) = q.comp F.subtype := by
    ext x
    have hx : b (q x) = q x := (mem_fixedSubgroup b (q x)).mp
      (map_subtype_le (solvableResidual P) x.property)
    exact (MulAut.centralQuotientAction_apply e a x).symm.trans hx
  have heq := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq q hker
    (a.toMonoidHom.comp F.subtype) F.subtype hfac
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    apply (mem_fixedSubgroup a x).mpr
    exact DFunLike.congr_fun heq ⟨x, hx⟩
  · exact map_solvableResidual_comap q
      (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) b.fixedSubgroup

end MulAut
