module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Marking

/-!
# The original summand normalizer has half the Sylow order

The natural-summand normalizer in the action quotient is its layer, of
index two. A Sylow two-subgroup meets that layer in index two. Relative
indices pull back through the literal action projection, even if the
projection has an odd-order kernel.
Source: Aschbacher--Smith H.9.1(3), 12.1.4--5, pp.390,790--791.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
private theorem sylow_relIndex_of_index_two {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (P : Sylow 2 A) (hi : N.index = 2) :
    N.relIndex (P : Subgroup A) = 2 := by
  have hd : N.relIndex (P : Subgroup A) ∣ 2 := by
    simpa only [hi] using relIndex_dvd_index_of_normal N (P : Subgroup A)
  apply ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
  intro hone
  apply P.not_dvd_index
  have hdiv := index_dvd_of_le (relIndex_eq_one.mp hone)
  rwa [hi] at hdiv

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)
include S

/-- The actual T₁, with its original ambient embedding, has index two in T. -/
theorem naturalSylowNormalizer_relIndex
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)).relIndex T = 2 := by
  let P := T.subtype hTM
  let Pbar := P.mapSurjective B.actionProjection_surjective
  have hi : (componentLayer B.ActionQuotient).index = 2 :=
    BinaryNaturalDual.ModelOrbits.SourceComparison.componentLayer_index
      S.setup.degree S.setup.projective
  have hrel : (componentLayer B.ActionQuotient).relIndex Pbar = 2 :=
    sylow_relIndex_of_index_two _ Pbar hi
  have he := congrArg (fun A : Subgroup (normalizer (L : Set G)) =>
    A.relIndex (P : Subgroup _)) S.naturalNormalizer_comap
  have hmap := S.setup.naturalNormalizer.relIndex_comap B.actionProjection (P : Subgroup _)
  rw [hmap] at he
  rw [S.setup.naturalNormalizer_eq_layer] at he
  change (componentLayer B.ActionQuotient).relIndex Pbar =
    ((normalizer (B.naturalSummand : Set G)).subgroupOf (normalizer (L : Set G))).relIndex
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G))) at he
  rw [relIndex_subgroupOf hTM] at he
  rw [inf_relIndex_left]
  exact he.symm.trans hrel

/-- The half-order assertion is independent of ambient point-centralizer control. -/
theorem naturalSylowNormalizer_card
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    2 * Nat.card ↥((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)) = Nat.card T := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)) (T : Subgroup G)
    bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, S.naturalSylowNormalizer_relIndex hTM] at hc
  exact (mul_comm _ _).trans hc

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
