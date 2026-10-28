module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# The two remaining three-index calculations

The count-one decomposition gives a selected subnormal block. Its intrinsic
three-generation is proved in `Generation`; to identify it with O^{3′}(H)
it remains to show that its relative index in H is prime to three.

These are separate proof obligations for the two alternatives in E.6.14(ii),
not additional clauses of E.6.7. They impose no normality on the selected
block. Their owners may use Hypothesis E.6.1 and the full E.6.7 input, and
must derive the index bound rather than assume that H has no further
three-elements.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
E.6.14, printed p.251, using E.6.7 on printed p.246.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G]

/-- The missing index calculation when the centralizer has three-rank at
most one. This definition does not assert the calculation. -/
def LowRankIndexInput (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ W ∈ obstructionFamily M V,
    HasCharacteristicTwo (centralizer (W : Set G)) →
    primeRank 3 (centralizer (W : Set G)) ≤ 1 →
    ∀ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V W
      (centralizer (W : Set G)), d.count = 1 →
      ∀ i, Nat.Coprime 3 ((d.block i).relIndex (centralizer (W : Set G)))

/-- The missing index calculation with a faithful three-action on W.
The actor is in N_G(W), and no action on the selected block is assumed. -/
def FaithfulIndexInput (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ W ∈ obstructionFamily M V,
    HasCharacteristicTwo (centralizer (W : Set G)) → HasFaithfulThreeAction W →
    ∀ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V W
      (centralizer (W : Set G)), d.count = 1 →
      ∀ i, Nat.Coprime 3 ((d.block i).relIndex (centralizer (W : Set G)))

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
