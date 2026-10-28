module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Inputs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index

/-!
# The local index for the principal eleven-block

There is one class of elements of order eleven. Fusion control in the cyclic
Sylow subgroup realizes every image of a generator by its actual normalizer.
Consequently the normalizer induces the whole automorphism group of order ten.
Its kernel is the actual centralizer, giving the index used by Feit VII.2.11.
Identifying this local index with the block's inertial index still uses the
principal-block theorem.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Every automorphism of a Sylow eleven-subgroup comes from its normalizer. -/
public theorem sylow_eleven_normalizer_surjective (d : OrdinaryData G)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    Function.Surjective (P : Subgroup G).normalizerMonoidHom := by
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [sylow_eleven_card horder P]
    decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  intro a
  obtain ⟨n, hn, hnx⟩ := sylow_eleven_normalizer_transitive d horder P x (a x) hx (by
    intro h
    exact hx (a.injective (h.trans a.map_one.symm)))
  refine ⟨⟨n, hn⟩, ?_⟩
  have hx' : (P : Subgroup G).normalizerMonoidHom ⟨n, hn⟩ x = a x := Subtype.ext hnx
  ext y
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card (sylow_eleven_card horder P) hx (g' := y))
  rw [← hk, map_zpow, map_zpow, hx']

/-- The centralizer has index ten in the actual Sylow normalizer. -/
public theorem sylow_eleven_centralizer_index (d : OrdinaryData G)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 10 := by
  let : IsCyclic P := sylow_eleven_isCyclic horder P
  have h := index_ker (P : Subgroup G).normalizerMonoidHom
  rw [Subgroup.normalizerMonoidHom_ker,
    MonoidHom.range_eq_top.mpr (sylow_eleven_normalizer_surjective d horder P),
    Subgroup.card_top, IsCyclic.card_mulAut, sylow_eleven_card horder P] at h
  exact h

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
