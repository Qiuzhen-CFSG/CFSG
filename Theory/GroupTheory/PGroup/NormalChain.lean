module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Nilpotent

/-!
# Subnormal chains in finite p-groups

Every subgroup of a finite p-group is subnormal. The normalizer condition
strictly enlarges each proper subgroup, and well-founded induction on the
finite subgroup lattice produces a chain of genuine normal inclusions.

This supplies the subnormal-chain step in Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
Lemma 1.1.4(1), printed p.501.
-/

namespace IsPGroup

/-- Every subgroup of a finite p-group admits a subnormal chain to the group. -/
public theorem subgroup_isSubnormal {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (U : Subgroup P) : U.IsSubnormal := by
  let : Group.IsNilpotent P := hP.isNilpotent
  induction U using WellFoundedGT.induction with
  | ind U ih =>
    by_cases he : U = ⊤
    · simpa only [he] using (Subgroup.IsSubnormal.top : (⊤ : Subgroup P).IsSubnormal)
    · have hlt := Group.normalizerCondition_of_isNilpotent U (lt_top_iff_ne_top.mpr he)
      exact .step U (Subgroup.normalizer (U : Set P)) hlt.le (ih _ hlt) inferInstance

end IsPGroup
