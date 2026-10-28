module

public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankCoarse
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# Sporadic obstructions to the moved pair of alternating-five blocks

Two independent commuting deleted alternating-five modules force two-rank
at least eight, while the two alternating-five quotients force divisibility
of the ambient order by twenty-five. Every sporadic row of original 1.1.5
except J4 has two-rank at most seven. The exact order of J4 has only one
factor of five. Thus no allowed sporadic carrier admits an injective image
with both numerical properties.

The map formulation retains the actual kernel obligation when the target
is the ordinary component modulo its two-core. In particular it makes no
assumption that a full Sylow subgroup normalizes an individual moved block.

Source: Aschbacher--Smith 14.6.9, printed p.1026, and 1.1.5(3),
printed pp.501--503; the intrinsic ranks are those used in G.7.3(2), p.348.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open ClassificationModels Sporadic.Mathieu

/-- Every allowed sporadic row violates one of the two necessary numerical
conditions for a commuting independent pair of deleted alternating-five blocks. -/
theorem sporadic_rank_or_order_obstruction (name : SporadicName) (hne : name ≠ .j3) :
    primeRank 2 name.Carrier < 8 ∨ ¬ 25 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 =>
      left
      change primeRank 2 M11 < 8
      have h := (primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot)).trans
          m11_automorphism_twoRank_le_two
      omega
  | m12 =>
      exact Or.inl (lt_of_le_of_lt m12_twoRank_le_three (by decide))
  | m22 =>
      exact Or.inl (lt_of_le_of_lt m22_twoRank_le_four (by decide))
  | m23 =>
      exact Or.inl (lt_of_le_of_lt m23_twoRank_le_four (by decide))
  | m24 =>
      exact Or.inl (lt_of_le_of_lt m24_twoRank_le_six (by decide))
  | j2 =>
      exact Or.inl (lt_of_le_of_lt
        Sporadic.LeechRelated.J2.primeRank_two_le_seven (by decide))
  | j3 => exact (hne rfl).elim
  | j4 =>
      right
      change ¬ 25 ∣ Nat.card Janko4.Model
      rw [Janko4.Cardinality.model_card]
      norm_num
  | hs =>
      exact Or.inl (lt_of_le_of_lt Sporadic.LeechRelated.HS.twoRank_le_four (by decide))
  | he =>
      exact Or.inl (lt_of_le_of_lt Held.primeRank_two_le_six (by decide))
  | ru =>
      exact Or.inl (lt_of_le_of_lt Rudvalis.primeRank_le_six (by decide))

/-- An actual model equivalence cannot preserve both numerical invariants
forced by an independent pair of deleted alternating-five blocks. -/
theorem not_sporadic_model_of_pair_numerics
    {A : Type*} [Group A] [Finite A]
    (hrank : 8 ≤ primeRank 2 A) (hcard : 25 ∣ Nat.card A)
    (name : SporadicName) (hne : name ≠ .j3) :
    ¬ Nonempty (A ≃* name.Carrier) := by
  rintro ⟨e⟩
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  rcases sporadic_rank_or_order_obstruction name hne with hr | hc
  · rw [primeRank_equiv 2 e] at hrank
    omega
  · exact hc ((Nat.card_congr e.toEquiv) ▸ hcard)

/-- The sporadic exclusion for a literal injective homomorphism. Applied
to the block product, this uses the same target as the source embedding. -/
theorem not_injective_to_sporadic_of_pair_numerics
    {X A : Type*} [Group X] [Finite X] [Group A] [Finite A]
    (hrank : 8 ≤ primeRank 2 X) (hcard : 25 ∣ Nat.card X)
    (name : SporadicName) (hne : name ≠ .j3)
    (hmodel : Nonempty (A ≃* name.Carrier)) (f : X →* A) :
    ¬ Function.Injective f := by
  intro hf
  exact not_sporadic_model_of_pair_numerics
    (hrank.trans (primeRank_le_of_injective 2 f hf))
    (hcard.trans (Subgroup.card_dvd_of_injective f hf)) name hne hmodel

end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
