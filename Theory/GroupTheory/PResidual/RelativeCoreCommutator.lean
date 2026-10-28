module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Independence of the core commutator from the local overgroup

For a p-perfect subgroup X subnormal in J, [Oₚ(J),X] equals
[Oₚ(X),X], with both cores embedded in the original ambient group.
Subnormal core monotonicity gives one inclusion; p-perfect commutator
idempotence gives the other. Thus two local overgroups of the same
component have the same commutator core, without identifying their radicals.

Source: Aschbacher--Smith A.4.2(2), p.57, and the core Q used in
C.1.34, pp.136--137; refs/quasithin.pdf.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The ambient core acts through the intrinsic core commutator of a
subnormal p-perfect subgroup. -/
theorem commutator_pCoreIn_eq_intrinsic_of_subnormal (X J : Subgroup G) (hXJ : X ≤ J)
    (hsub : (X.subgroupOf J).IsSubnormal) (hp : IsPPerfect p X) :
    ⁅J.pCoreIn p, X⁆ = ⁅X.pCoreIn p, X⁆ := by
  let A := X.subgroupOf J
  have hpA : IsPPerfect p A := hp.of_surjective
    (subgroupOfEquivOfLe hXJ).symm.toMonoidHom
    (subgroupOfEquivOfLe hXJ).symm.surjective
  have hh := commutator_le_core_commutator_of_isSubnormal A (pCore p J)
    hsub hpA pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hh
  have hm := map_mono hh (f := J.subtype)
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hXJ] at hm
  have hcore : ((pCore p A).map A.subtype).map J.subtype = X.pCoreIn p := by
    change (A.pCoreIn p).map J.subtype = _
    rw [pCoreIn_subgroupOf p X J hXJ,
      map_subgroupOf_eq_of_le ((pCoreIn_le p X).trans hXJ)]
  rw [hcore] at hm
  exact le_antisymm hm (commutator_mono
    (pCoreAmbient_mono_of_isSubnormalIn X J p hXJ hsub) le_rfl)

end Subgroup
