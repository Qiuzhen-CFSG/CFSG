module

public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Lifting subgroup quotients

Suppose G surjects onto Q and embeds in H. Every quotient of a subgroup
of Q is then a quotient of a subgroup of H. The quotient is represented
by its actual surjective homomorphism, so no normal-subgroup or quotient
type choices enter the interface. No finiteness or simplicity is needed.

Pull the subgroup of Q back into G. Restriction of the surjection still
surjects onto that subgroup. Map this preimage through the embedding and
use its actual image equivalence to compose the required surjection.

This is the section transfer from a centralizer supplement quotient into
an involution centralizer in ABG II.3 Lemma 2, article page 24.
-/

namespace MonoidHom

public theorem exists_section_of_surjective_of_injective
    {G Q H T : Type*} [Group G] [Group Q] [Group H] [Group T]
    (q : G →* Q) (hq : Function.Surjective q)
    (i : G →* H) (hi : Function.Injective i)
    (U : Subgroup Q) (f : U →* T) (hf : Function.Surjective f) :
    ∃ V : Subgroup H, ∃ g : V →* T, Function.Surjective g := by
  let W := U.comap q
  let e := Subgroup.equivMapOfInjective W i hi
  refine ⟨W.map i, f.comp ((q.subgroupComap U).comp e.symm.toMonoidHom), ?_⟩
  exact hf.comp ((q.subgroupComap_surjective_of_surjective U hq).comp e.symm.surjective)

end MonoidHom
