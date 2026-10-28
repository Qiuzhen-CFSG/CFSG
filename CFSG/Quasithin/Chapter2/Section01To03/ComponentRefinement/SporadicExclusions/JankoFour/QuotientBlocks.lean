module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# Block exclusions for two-group extensions of M24

The allowed chi-zero quotients have orders 3, 60, or q(q^2-1) for a binary
field order q greater than two. None has the order of M24. For a surjection
with two-group kernel onto M24, the kernel is exactly the two-core.
Subnormality then makes the image of any proposed block either trivial or
all of M24. The first case contradicts two-perfectness, and the second is
excluded by the quotient order.

Applied to the actual E2048.M24 subgroup in the J4 matrix model, this proves
that every subnormal subgroup fails to be a chi-zero block. No statement
about the dimension of its conjugation module is needed for this argument.
The application is the local calculation in Aschbacher–Smith 2.3.9(7),
printed p.526, using the subgroup in GLS3, Table 5.3i.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

open Subgroup ChapterC Sporadic.Mathieu

variable {K : Type*} [Group K]

/-- The order of M24 is not the order of an allowed chi-zero quotient. -/
theorem not_chiZero_of_quotient_card_m24
    (hq : Nat.card (K ⧸ pCore 2 K) = 244823040) : ¬ IsChiZeroBlock K := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, _, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn : n < 10 := by
      by_contra hn
      have hl : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 20 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n <;> norm_num [hq] at he
  · omega
  · omega

/-- A two-group extension of the actual M24 carrier cannot be a chi-zero block. -/
theorem not_chiZero_of_surjective_m24 [Finite K]
    (f : K →* M24) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker) :
    ¬ IsChiZeroBlock K := by
  apply not_chiZero_of_quotient_card_m24
  rw [← ker_eq_twoCore_of_surjective_m24 f hf hp]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans
    m24_order

/-- This obstruction applies to every subnormal subgroup, not just to the local group. -/
theorem not_chiZero_subnormal_of_surjective_m24 [Finite K]
    (f : K →* M24) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (B : Subgroup K) (hB : B.IsSubnormal) : ¬ IsChiZeroBlock B := by
  rcases (hB.map hf).eq_bot_or_top_of_isSimpleGroup m24_isSimpleGroup with hbot | htop
  · have hle : B ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hBP : IsPGroup 2 B := hp.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    intro h
    have hs := h.chi.short
    have he : (⊥ : Subgroup B) = ⊤ := hs.twoPerfect ⊥ inferInstance (hBP.to_quotient ⊥)
    apply hs.blockU_ne_bot
    apply le_bot_iff.mp
    rw [he]
    exact le_top
  · have hsurj : Function.Surjective (f.comp B.subtype) := by
      apply MonoidHom.range_eq_top.mp
      rw [MonoidHom.range_comp, Subgroup.range_subtype, htop]
    have hker : IsPGroup 2 (f.comp B.subtype).ker :=
      hp.comap_of_injective B.subtype Subtype.val_injective
    exact not_chiZero_of_surjective_m24 (f.comp B.subtype) hsurj hker

/-- There are no subnormal chi-zero blocks inside the concrete J4 local subgroup. -/
theorem max1_no_chiZero_subnormal
    (hA : Janko4.matrixA * Janko4.matrixA = 1) (hB : Janko4.matrixB ^ 4 = 1)
    (B : Subgroup (Janko4.Cardinality.max1Subgroup hA hB)) (hsub : B.IsSubnormal) :
    ¬ IsChiZeroBlock B := by
  let f := (Janko4.LocalStructure.localQuotientEquivM24 hA hB).toMonoidHom.comp
    (QuotientGroup.mk' (Janko4.Cardinality.localKernel hA hB))
  have hs : Function.Surjective f :=
    (Janko4.LocalStructure.localQuotientEquivM24 hA hB).surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hk : f.ker = Janko4.Cardinality.localKernel hA hB := by
    ext x
    change Janko4.LocalStructure.localQuotientEquivM24 hA hB
      (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff _ (Janko4.LocalStructure.localQuotientEquivM24 hA hB).injective]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact IsPGroup.of_card (n := 11) (Janko4.Cardinality.localKernel_card hA hB)
  exact not_chiZero_subnormal_of_surjective_m24 f hs hp B hsub

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
