module
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
/-!
# Odd containment through an ambient two-core

An odd subgroup lying in a subnormal two-perfect subgroup times the ambient
two-core already lies in that subgroup. The two-core normalizes the
subnormal subgroup, and the resulting quotient is a two-group, so the odd
image vanishes. Containment may therefore be checked through any map whose
kernel is the ambient two-core.

The consumer is the original general-field torus axes in Aschbacher–Smith
10.2.3(4), pp.746–747. No commutation or elementary-core assumption is used.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]
/-- An odd subgroup contained in a subnormal two-perfect subgroup times
its ambient two-core is contained in that subgroup itself. -/
theorem odd_le_of_le_sup_twoCore (A B : Subgroup G)
    (ho : Odd (Nat.card A)) (hB : B.IsSubnormal) (hpB : IsPPerfect 2 B)
    (hAB : A ≤ B ⊔ pCore 2 G) : A ≤ B := by
  have hpA : IsPPerfect 2 A := by
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (A ⧸ N) = 1
    exact htwo.card_eq_or_dvd.resolve_right
      (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))
  exact le_of_isPPerfect_of_le_sup_of_normalizes A B (pCore 2 G) hpA pCore_isPGroup
    (le_normalizer_of_isSubnormal_isPPerfect B (pCore 2 G) hB hpB pCore_isPGroup
      le_normalizer_of_normal) hAB

/-- Odd containment lifts through a map whose kernel is the ambient two-core,
against a subnormal two-perfect subgroup. -/
theorem odd_le_of_map_le_of_ker_eq_twoCore {Q : Type*} [Group Q] (A B : Subgroup G)
    (ho : Odd (Nat.card A)) (hB : B.IsSubnormal) (hpB : IsPPerfect 2 B)
    (q : G →* Q) (hk : q.ker = pCore 2 G) (hAB : A.map q ≤ B.map q) : A ≤ B := by
  apply odd_le_of_le_sup_twoCore A B ho hB hpB
  have hh := le_trans (le_comap_map q A) (comap_mono hAB)
  simpa only [comap_map_eq,hk] using hh
end Subgroup
