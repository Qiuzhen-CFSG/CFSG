module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Overgroups

/-!
# Model inputs for uniqueness of a J₄ max4 overgroup

The conjugacy input ranges over all actual subgroups of the specified
isomorphism type containing the same ambient Sylow subgroup. It is not
restricted to conjugates of the named ATLAS subgroup. Together with the
Sylow-normalizer input it implies uniqueness, hence odd incidence whenever
the pair's overgroup family is nonempty.

These are unproved model contracts, not assertions from the book passage.
The source application is Aschbacher–Smith, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow subgroups in
sporadic groups* (1986). The concrete subgroup and ATLAS provenance are in
`Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model`.
-/

@[expose] public section

open Subgroup Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Ambient Sylow-normalizer control, without an automorphism-group premise. -/
def JankoFourSylowSelfNormalizer : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), normalizer (S : Set Janko4.Model) ≤ S.toSubgroup

/-- All max4-type overgroups of a fixed Sylow subgroup are conjugate in
the actual matrix carrier. Their abstract isomorphisms alone do not prove this. -/
def MaximalFourSylowConjugacy : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M N : Subgroup Janko4.Model),
      S.toSubgroup ≤ M → S.toSubgroup ≤ N →
      Nonempty (M ≃* max4Subgroup) → Nonempty (N ≃* max4Subgroup) →
      ∃ g : Janko4.Model, M.map (MulAut.conj g).toMonoidHom = N

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
