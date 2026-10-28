module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Prime cores of finite quasisimple groups

The prime core of a finite quasisimple group is central. A normal subgroup
is central or is the whole group; the second alternative would make the
nontrivial perfect group nilpotent and hence solvable.

Source: the normal-subgroup property of quasisimple groups, as in GLS,
volume 2, Chapter 1; see `ComponentCalculus` for the quotient argument.
-/

public section

namespace Theory.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsQuasisimple G]

/-- A finite quasisimple group's prime core is central, with no splitting
or trivial-center assumption. -/
theorem IsQuasisimple.pCore_le_center (p : ℕ) [Fact p.Prime] :
    pCore p G ≤ center G := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (pCore p G) with hc | ht
  · exact hc
  · have hp : IsPGroup p G := by
      have he : IsPGroup p (⊤ : Subgroup G) := ht ▸ pCore_isPGroup
      exact he.of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent G := hp.isNilpotent
    let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    let : Nontrivial G := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (center G))
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

end Theory.GroupTheory

end
