module
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.IsPerfect
/-!
# Inner realizations of perfect automorphism subgroups

A perfect subgroup of an automorphism group has trivial image in a soluble
outer quotient. If the original group is centerless, conjugation gives a
unique faithful realization of that subgroup inside the original group.
The returned homomorphism retains the exact implementing-conjugation formula.

This is the Schreier-action step in Aschbacher--Smith C.4.5, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {G : Type*} [Group G]

theorem perfect_subgroup_le_inner (A : Subgroup (MulAut G)) [Group.IsPerfect A]
    [Group.IsSolvable (Outer G)] : A ≤ innerSubgroup G := by
  let f : A →* Outer G := (QuotientGroup.mk' (innerSubgroup G)).comp A.subtype
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro a ha
  exact (QuotientGroup.eq_one_iff _).mp (show f ⟨a,ha⟩ = 1 from
    congrArg f.range.subtype (hs.elim (⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ : f.range) 1))

theorem perfect_subgroup_exists_inner_lift (A : Subgroup (MulAut G))
    [Group.IsPerfect A] [Group.IsSolvable (Outer G)] (hz : center G = ⊥) :
    ∃ f : A →* G, Function.Injective f ∧ ∀ a : A, MulAut.conj (f a) = (a : MulAut G) := by
  let e : G ≃* innerSubgroup G := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)
  let f : A →* G := e.symm.toMonoidHom.comp (inclusion (perfect_subgroup_le_inner A))
  refine ⟨f,e.symm.injective.comp (inclusion_injective _),?_⟩
  intro a
  exact congrArg (innerSubgroup G).subtype (e.apply_symm_apply (inclusion (perfect_subgroup_le_inner A) a))

end MulAut
