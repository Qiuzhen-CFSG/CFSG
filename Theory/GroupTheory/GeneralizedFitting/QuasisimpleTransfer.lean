module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Quasisimple generalized Fitting subgroups from embedded models

A quasisimple group is its own generalized Fitting subgroup. An injective
copy of a quasisimple group of index two is normal, so the two-quotient
calculation identifies it with F* whenever the ambient two-core is trivial.
This uses the actual image and does not require a split extension.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, F.6.18(4)–(11), pp.309–310, and 15.4.18, p.1163.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G M : Type*} [Group G] [Group M]

/-- A quasisimple group is already its full generalized Fitting subgroup. -/
theorem generalizedFitting_eq_top_of_quasisimple [IsQuasisimple G] :
    generalizedFitting G = ⊤ := by
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  exact top_unique (component_le_generalizedFitting G ⊤ ⟨.top, inferInstance⟩)

/-- Quasisimplicity of a group passes to its generalized Fitting subgroup. -/
theorem generalizedFitting_isQuasisimple_of_quasisimple [IsQuasisimple G] :
    IsQuasisimple (generalizedFitting G) := by
  rw [generalizedFitting_eq_top_of_quasisimple]
  exact IsQuasisimple.of_mulEquiv topEquiv.symm

/-- An actual embedded quasisimple subgroup of index two is F* when O₂ = 1. -/
theorem generalizedFitting_eq_range_of_quasisimple_index_two [Finite G]
    [IsQuasisimple M] (i : M →* G) (hi : Function.Injective i)
    (hindex : i.range.index = 2) (hcore : pCore 2 G = ⊥) :
    generalizedFitting G = i.range := by
  let : i.range.Normal := normal_of_index_eq_two hindex
  let : IsQuasisimple i.range := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi)
  apply generalizedFitting_eq_of_quasisimple_two_quotient i.range _ hcore
  exact IsPGroup.of_card (n := 1) (by simpa [index_eq_card] using hindex)

/-- Quasisimplicity of F* for an arbitrary, possibly nonsplit, index-two extension. -/
theorem generalizedFitting_isQuasisimple_of_index_two [Finite G]
    [IsQuasisimple M] (i : M →* G) (hi : Function.Injective i)
    (hindex : i.range.index = 2) (hcore : pCore 2 G = ⊥) :
    IsQuasisimple (generalizedFitting G) := by
  rw [generalizedFitting_eq_range_of_quasisimple_index_two i hi hindex hcore]
  exact IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi)

end Theory.GroupTheory
