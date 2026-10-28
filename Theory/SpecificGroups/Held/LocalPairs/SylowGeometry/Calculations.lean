module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer
public import Mathlib.GroupTheory.Nilpotent

/-!
# Assembly of the concrete Held Sylow calculations

Fix the literal subgroup from `Calculations/Representative`. The three imported
finite certificates prove that it is a two-group, its normalizer in Held is
itself, and its centralizer in the full permutation normalizer has at most two elements.
The normalizer condition inside a Sylow overgroup proves that the representative
is Sylow, without an order formula for Held. Sylow conjugacy then transports
its ambient normalizer identity.

The full centralizer bound controls both centers: inject the representative's
center using the inner embedding, and inject the larger Sylow's center using
its containment of the embedded representative. Nontrivial finite two-groups
have nontrivial centers, so both bounds are equalities. The existing Reduction
module constructs the larger Sylow. This argument does not require identifying
an exhibited He:2 with the full normalizer or realizing abstract automorphisms.

The conditional transfer lemmas are retained, and the final three theorems
discharge all their finite premises. Every Held Sylow two-subgroup has center
of order two and is self-normalizing, without simplicity or perfectness
assumptions. The center of every Sylow two-subgroup of the full permutation
normalizer has order two when the quotient by the relatively normal Held copy
has order at most two.
Source: GLS3 Table 5.3p and the actual ATLAS HeG1-p2058B0 action.
-/

public section

namespace Held.LocalPairs.SylowGeometry.Calculations
open Subgroup
open scoped Pointwise

private theorem center_card_le_centralizer {G : Type*} [Group G] [Finite G]
    (P K : Subgroup G) (hPK : P ≤ K) :
    Nat.card (center K) ≤ Nat.card (centralizer (P : Set G)) := by
  let f : center K → centralizer (P : Set G) := fun z =>
    ⟨z.val.val, by
      apply mem_centralizer_iff.mpr
      intro x hx
      exact congrArg (fun k : K => k.val) ((mem_center_iff.mp z.property) ⟨x, hPK hx⟩)⟩
  exact Nat.card_le_card_of_injective f (fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : centralizer (P : Set G) => z.val) h)))

private theorem center_card_eq_two_of_le {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hp : IsPGroup 2 G) (hbound : Nat.card (center G) ≤ 2) :
    Nat.card (center G) = 2 := by
  let := hp.center_nontrivial
  have := Finite.one_lt_card (α := center G)
  omega

/-- A self-normalizing two-subgroup is Sylow, by the normalizer condition
inside a Sylow overgroup. No ambient order calculation is needed. -/
theorem exists_representative_sylow
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative) :
    ∃ S : Sylow 2 He, (S : Subgroup He) = representative := by
  obtain ⟨S, hPS⟩ := hp.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hPS⟩
  by_contra hle
  have hproper : representative.subgroupOf (S : Subgroup He) < ⊤ := by
    rwa [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  obtain ⟨g, hg, hgout⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hproper)
  rw [← subgroupOf_normalizer_eq hPS] at hg
  exact hgout (show g.val ∈ representative from hn ▸ hg)

/-- A bound on the full ambient centralizer bounds the intrinsic center of
the chosen subgroup, using the literal injective Held inclusion. -/
theorem representative_center_card_of_centralizer_bound
    (hp : IsPGroup 2 representative)
    (hc : Nat.card (centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer)) ≤ 2) :
    Nat.card (center representative) = 2 := by
  let : Nontrivial representative :=
    (Subgroup.nontrivial_iff_ne_bot representative).mpr representative_ne_bot
  apply center_card_eq_two_of_le hp
  calc
    Nat.card (center representative) =
        Nat.card (center (representative.map innerEmbedding)) :=
      Nat.card_congr (Subgroup.centerCongr
        (representative.equivMapOfInjective innerEmbedding innerEmbedding_injective)).toEquiv
    _ ≤ Nat.card (centralizer
        (representative.map innerEmbedding : Set PermutationNormalizer)) :=
      center_card_le_centralizer _ _ le_rfl
    _ ≤ 2 := hc

/-- Conjugation transports the actual ambient normalizer identity. -/
theorem inner_self_normalizing_of_representative
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative)
    (S : Sylow 2 He) : normalizer (S : Set He) = (S : Subgroup He) := by
  obtain ⟨P, hP⟩ := exists_representative_sylow hp hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq He P S
  change normalizer ((P : Subgroup He).map (MulAut.conj g).toMonoidHom : Set He) =
    (P : Subgroup He).map (MulAut.conj g).toMonoidHom
  rw [← map_equiv_normalizer_eq, hP, hn]

/-- Sylow equivalences preserve centers. -/
theorem inner_center_card_of_representative
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative)
    (hc : Nat.card (centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer)) ≤ 2)
    (S : Sylow 2 He) : Nat.card (center S) = 2 := by
  obtain ⟨P, hP⟩ := exists_representative_sylow hp hn
  calc
    Nat.card (center S) = Nat.card (center P) :=
      Nat.card_congr (Subgroup.centerCongr (S.equiv P)).toEquiv
    _ = Nat.card (center representative) := by rw [hP]
    _ = 2 := representative_center_card_of_centralizer_bound hp hc

/-- The same centralizer bound controls the larger Sylow center. The larger
Sylow is constructed by the existing full-normalizer reduction. -/
theorem normalizer_center_card_of_representative
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative)
    (hc : Nat.card (centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer)) ≤ 2)
    (T : Sylow 2 PermutationNormalizer) : Nat.card (center T) = 2 := by
  obtain ⟨P, hP⟩ := exists_representative_sylow hp hn
  obtain ⟨Q, hQ, _⟩ := exists_normalizer_sylow_of_self_normalizing hbound P
    (by change normalizer (P.toSubgroup : Set He) = P.toSubgroup; rw [hP]; exact hn)
  have hPQ : representative.map innerEmbedding ≤ (Q : Subgroup PermutationNormalizer) := by
    rw [hQ, hP]
    exact le_normalizer
  have hne : Q.toSubgroup ≠ ⊥ := by
    intro he
    have hm := hPQ (mem_map_of_mem innerEmbedding (generator_mem 1))
    rw [he, mem_bot] at hm
    exact generator_one_ne_one (innerEmbedding_injective (hm.trans (map_one innerEmbedding).symm))
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q.toSubgroup).mpr hne
  have hQc : Nat.card (center Q) = 2 := center_card_eq_two_of_le Q.isPGroup'
    ((center_card_le_centralizer _ _ hPQ).trans hc)
  exact (Nat.card_congr (Subgroup.centerCongr (T.equiv Q)).toEquiv).trans hQc

/-- Every Sylow two-subgroup of the actual Held carrier has center of order two. -/
theorem inner_center_card (S : Sylow 2 He) : Nat.card (center S) = 2 :=
  inner_center_card_of_representative representative_isPGroup
    InnerNormalizer.normalizer_eq representative_fullCentralizer_card_le_two S

/-- Every Sylow two-subgroup is self-normalizing in the actual Held carrier. -/
theorem inner_self_normalizing (S : Sylow 2 He) :
    normalizer (S : Set He) = (S : Subgroup He) :=
  inner_self_normalizing_of_representative representative_isPGroup
    InnerNormalizer.normalizer_eq S

/-- Every Sylow two-subgroup of the full permutation normalizer has center of
order two, under the bound on its quotient by the relatively normal Held copy. -/
theorem normalizer_center_card
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 PermutationNormalizer) : Nat.card (center T) = 2 :=
  normalizer_center_card_of_representative hbound representative_isPGroup
    InnerNormalizer.normalizer_eq representative_fullCentralizer_card_le_two T

end Held.LocalPairs.SylowGeometry.Calculations
