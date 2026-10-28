module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.Reduction

/-!
# The separate embedding comparisons for the three J₄ local carriers

Each comparison concerns an actual subgroup isomorphic to one fixed literal
carrier. Isomorphism classification is not an input to these comparisons.
The supplied Sylow overgroup also proves that the literal carrier contains
an ambient Sylow: transport the restricted Sylow through the isomorphism,
then use its unchanged cardinality to prove ambient Sylow maximality.

This avoids asking for a separate order or odd-index theorem about the model.
Source context: Kleidman--Wilson, *The maximal subgroups of J₄* (1988),
pp.484--510. These are embedding proof obligations, not consequences of
the ATLAS list or of the passage on printed p.511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The embedding comparison for one specified literal subgroup. -/
@[expose] def MaximalEmbeddingConjugacyAt (L : Subgroup Janko4.Model) : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M → Nonempty (M ≃* L) →
      ∃ g : Janko4.Model, M = L.map (MulAut.conj g).toMonoidHom

/-- An isomorphic copy containing a Sylow supplies a Sylow in the literal
carrier. No ambient order calculation or maximality assumption is needed. -/
theorem exists_sylow_le_of_equiv (S : Sylow 2 Janko4.Model)
    (M L : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) (e : M ≃* L) :
    ∃ T : Sylow 2 Janko4.Model, T.toSubgroup ≤ L := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card S := by
    change Nat.card ((S.subtype hSM).toSubgroup.map e.toMonoidHom) = Nat.card S
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv
  let T : Sylow 2 Janko4.Model := Sylow.ofCard (P.toSubgroup.map L.subtype) (by
    rw [card_map_of_injective L.subtype_injective, hcard, S.card_eq_multiplicity])
  exact ⟨T, map_subtype_le P.toSubgroup⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
