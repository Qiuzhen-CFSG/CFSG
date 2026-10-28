module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# Local inputs for Held involution fixed subgroups

These predicates specify the consequences of GLS3 Table 5.3p needed to
exclude centerless components of order 360. They are proof obligations,
not assertions that the concrete Held carrier satisfies the table.

The two inner rows are `(E₄.L₃(4)).2` and `2^(1+6).L₃(2)`. The first
requires an actual normal quasisimple subgroup of index two with center
of order four. The second requires the fixed subgroup's order 21504.
The outer row `3A₇.2` requires an actual normal quasisimple subgroup of
index two with center of order three; it does have a component.
No row is replaced by a split product or a group-family tag.

The outer obligation concerns automorphisms induced by the full permutation
normalizer. The separate realization theorem must still show that every
abstract automorphism is so induced. Keeping that hypothesis separate allows
the finite local calculations and realization to be proved independently.

Sources: GLS3, Table 5.3p, printed p.277; Aschbacher–Smith, Theorem C,
printed p.33, and the inspection in E.6.23, printed p.254 (PDF p.265).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Held.InvolutionFixedData

/-- The two inner involution rows, on literal fixed subgroups of the actual
degree-2058 Held carrier. Only the local facts consumed by the exclusion occur. -/
def InnerRows : Prop :=
  ∀ g : He, orderOf (MulAut.conj g) = 2 →
    HasQuasisimpleNormalOfIndexTwo (MulAut.conj g).fixedSubgroup 4 ∨
      Nat.card (MulAut.conj g).fixedSubgroup = 21504

/-- The genuine outer covering row for every involution implemented by the
permutation normalizer. The non-inner condition is about the induced action,
not merely membership of the implementing permutation in the Held subgroup. -/
def OuterRow : Prop :=
  ∀ n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))),
    orderOf (permutationGroup.normalizerMonoidHom n) = 2 →
    (¬ ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) →
      HasQuasisimpleNormalOfIndexTwo
        (permutationGroup.normalizerMonoidHom n).fixedSubgroup 3

end Held.InvolutionFixedData
