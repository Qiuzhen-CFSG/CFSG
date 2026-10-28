module
public import Theory.GroupTheory.PerfectCentralCoverOuter
/-!
# Outer actions of self-centralizing normal subgroups

If the centralizer of a normal subgroup N lies in N, the literal quotient
G/N embeds in Out(N). For perfect N the same quotient embeds in Out(N/Z(N)):
innerness on the central quotient lifts to innerness on N. Thus this argument
retains a nontrivial scalar center, rather than requiring a trivial centralizer.

Source: the elementary outer-action step in Aschbacher–Smith 12.6.31(1),
printed pp.836–837.
-/
public section
open Subgroup
namespace MulAut
variable {J Q : Type*} [Group J] [Group Q]

/-- Self-centralization suffices for faithfulness of the actual outer quotient action. -/
theorem outerAction_injective_of_centralizer_le (N : Subgroup J) [N.Normal]
    (hc : centralizer (N : Set J) ≤ N) : Function.Injective (outerAction N) := by
  apply (MonoidHom.ker_eq_bot_iff (outerAction N)).mp
  change (QuotientGroup.map _ _ _ _).ker = ⊥
  rw [QuotientGroup.ker_map, conjNormal_comap_innerSubgroup, sup_eq_left.mpr hc,
    QuotientGroup.map_mk'_self]

/-- The same quotient acts faithfully through outer automorphisms of the central quotient. -/
theorem centralQuotientOuter_comp_outerAction_injective (N : Subgroup J) [N.Normal]
    [Group.IsPerfect N] (e : N ⧸ center N ≃* Q)
    (hc : centralizer (N : Set J) ≤ N) :
    Function.Injective ((centralQuotientOuter e).comp (outerAction N)) :=
  (centralQuotientOuter_injective e).comp (outerAction_injective_of_centralizer_le N hc)

end MulAut
