module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Subgroup quotients of a p-group quotient

If G/N is a p-group, the literal quotient R/(N ∩ R) is a p-group for
every subgroup R. Restricting the quotient map to R identifies this quotient
with its image in G/N by the first isomorphism theorem.

This is the quotient transport used when passing to a constituent stabilizer
in Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.42.
-/

namespace Subgroup

/-- Every subgroup inherits a p-group quotient by the intersection with the
original normal denominator; containment of the denominator is unnecessary. -/
public theorem isPGroup_quotient_subgroupOf {G : Type*} [Group G] {p : ℕ}
    (N R : Subgroup G) [N.Normal] (hquot : IsPGroup p (G ⧸ N)) :
    IsPGroup p (R ⧸ N.subgroupOf R) := by
  let f := (QuotientGroup.mk' N).comp R.subtype
  have hk : f.ker = N.subgroupOf R := by
    ext x
    exact QuotientGroup.eq_one_iff (N := N) (x : G)
  have hp := (hquot.to_subgroup f.range).of_equiv
    (QuotientGroup.quotientKerEquivRange f).symm
  exact hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hk)

end Subgroup
