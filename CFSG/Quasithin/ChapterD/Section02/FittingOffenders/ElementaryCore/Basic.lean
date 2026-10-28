module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Frattini.PGroup

/-!
# The preceding hyperplane inputs for the elementary-core argument

The input records exactly the order and module-support conclusions obtained
from D.2.13 for the rank-one subgroups of the four-group actor. Centralizers
are ambient intersections, and the moved subspace is formed inside the actual
fixed space of the given representation.

Source: Aschbacher--Smith, D.2.14, printed p.186, the paragraph preceding (+).
This is a conditional input to the elementary-core argument, not a source
theorem or an assertion of elementarity.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The two preceding-source conclusions for each nontrivial hyperplane centralizer. -/
def HyperplaneSupport (ρ : Representation (ZMod 2) G V) (P A : Subgroup G) : Prop :=
  ∀ B ≤ A, rank B = 1 → P ⊓ centralizer (B : Set G) ≠ ⊥ →
    Nat.card (P ⊓ centralizer (B : Set G) : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator ρ (fixedSpace ρ B) (P ⊓ centralizer (B : Set G))) = 2

end CFSG.Quasithin.ChapterD.ElementaryCore
