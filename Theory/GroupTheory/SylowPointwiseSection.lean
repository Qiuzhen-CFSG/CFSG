module

public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The two-Schreier property on actual sections

The hypothesis quantifies over surjections from subgroups to simple groups,
and over the pointwise automorphism fixer of every Sylow two-subgroup.
It passes to subgroups and surjective images by composing the actual maps.

Source: GLS II, Definition A.2.2. At the prime two we use the explicit
solvability hypothesis requested by the source application; the odd order
theorem equates this with the source's two-solvability formulation.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory

universe u

/-- Every actual simple section has solvable Sylow-two pointwise automorphism fixer. -/
def HasTwoSchreier (G : Type u) [Group G] : Prop :=
  ∀ (U : Subgroup G) (S : Type u) [Group S] [IsSimpleGroup S],
    ∀ f : U →* S, Function.Surjective f →
      ∀ P : Sylow 2 S, Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S))

namespace HasTwoSchreier
variable {G H : Type u} [Group G] [Group H]

theorem subgroup (h : HasTwoSchreier G) (U : Subgroup G) : HasTwoSchreier U := by
  intro V S _ _ f hf P
  let e := equivMapOfInjective V U.subtype U.subtype_injective
  exact h (V.map U.subtype) S (f.comp e.symm.toMonoidHom)
    (hf.comp e.symm.surjective) P

theorem of_surjective (h : HasTwoSchreier G) (f : G →* H)
    (hf : Function.Surjective f) : HasTwoSchreier H := by
  intro V S _ _ g hg P
  exact h (V.comap f) S (g.comp (f.subgroupComap V))
    (hg.comp (f.subgroupComap_surjective_of_surjective V hf)) P
end HasTwoSchreier

end Theory.GroupTheory
