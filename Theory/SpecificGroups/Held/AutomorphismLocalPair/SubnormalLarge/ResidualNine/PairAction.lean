module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.CenterImage
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.Product
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual


/-!
# The literal pure Held pair quotient onto S₃ × S₃

Let B be the unchanged candidate product (false,0). Its canonical conjugation
image on the center of the certified normal word subgroup has 36 elements.
The four original generators act on a central sixteen-set by explicit
permutations. Their mixed-radix words give a bijective enumeration of the image,
and Product checks exactly the same multiplication in S₃ × S₃. This constructs
an actual isomorphism of the image, hence an unconditional surjection from B.

The word subgroup lies in the action kernel and has order 256. Since B has
order 9216 and its image has order 36, the kernel also has order 256. Therefore
the kernel is exactly that two-group. The final application supplies the
residual-nine calculation for this literal pair. The independent comparison
with the full representative normalizer remains with the parent assembly.

Sources: Aschbacher--Smith 2.3.9(7), printed p.526; GLS3 Table 5.3p. The finite
certificates are extracted from the PureInnerCore calculation for 15.3.41–42,
with original ATLAS words, left-action convention and attribution preserved.
-/

set_option Elab.async false
@[expose] public section

open Subgroup
namespace Held.AutomorphismLocalPair.ResidualNine
open PairActionCertificate PairActionCertificate.CenterImageCertificate

namespace PairActionCertificate.CenterImageCertificate

/-- Restriction to the certified central sixteen-set is faithful on the actual image. -/
theorem compatible_unique {a b : pureCenterAction.range} {p : Equiv.Perm (Fin 16)}
    (ha : Compatible a p) (hb : Compatible b p) : a = b := by
  obtain ⟨v, rfl⟩ := actualWord_surjective a
  obtain ⟨w, rfl⟩ := actualWord_surjective b
  congr 1
  apply smallWord_injective
  apply Equiv.ext
  intro x
  apply centralWord_injective
  rw [← word_compatible v x, ← word_compatible w x, ha x, hb x]

theorem actualWord_mul (v w : Fin 36) :
    actualWord v * actualWord w = actualWord (mulIndex v w) := by
  apply compatible_unique ((word_compatible v).mul (word_compatible w))
  rw [smallWord_mul]
  exact word_compatible _

noncomputable def imageCoordinates : Fin 36 ≃ pureCenterAction.range :=
  Equiv.ofBijective actualWord ⟨actualWord_injective, actualWord_surjective⟩

noncomputable def targetCoordinates : Fin 36 ≃ QuotientModel :=
  Equiv.ofBijective targetWord ⟨targetWord_injective, targetWord_surjective⟩

/-- The comparison uses the same word coordinates and their checked multiplication. -/
noncomputable def centerImageEquiv : pureCenterAction.range ≃* QuotientModel where
  toEquiv := imageCoordinates.symm.trans targetCoordinates
  map_mul' x y := by
    obtain ⟨v, rfl⟩ := actualWord_surjective x
    obtain ⟨w, rfl⟩ := actualWord_surjective y
    change targetCoordinates (imageCoordinates.symm (actualWord v * actualWord w)) =
      targetCoordinates (imageCoordinates.symm (actualWord v)) *
      targetCoordinates (imageCoordinates.symm (actualWord w))
    rw [actualWord_mul]
    change targetCoordinates (imageCoordinates.symm (imageCoordinates (mulIndex v w))) =
      targetCoordinates (imageCoordinates.symm (imageCoordinates v)) *
      targetCoordinates (imageCoordinates.symm (imageCoordinates w))
    simp only [Equiv.symm_apply_apply]
    exact (targetWord_mul v w).symm

theorem centerImageEquiv_word (v : Fin 36) :
    centerImageEquiv (actualWord v) = targetWord v := by
  change targetCoordinates (imageCoordinates.symm (imageCoordinates v)) = _
  rw [Equiv.symm_apply_apply]
  rfl

end PairActionCertificate.CenterImageCertificate

/-- Quotient of the literal pure Held pair onto the actual product of symmetric groups. -/
noncomputable def pairQuotient :
    LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateProduct false 0 →* QuotientModel :=
  centerImageEquiv.toMonoidHom.comp pureCenterAction.rangeRestrict

/-- Compatibility with the original four pair generators in the canonical left action. -/
theorem pairQuotient_actor (k : Fin 4) :
    pairQuotient (actor k) = targetGenerator k := by
  change centerImageEquiv (actualGenerator k) = targetGenerator k
  fin_cases k
  · simpa [actualWord, targetWord, word] using centerImageEquiv_word 1
  · simpa [actualWord, targetWord, word] using centerImageEquiv_word 3
  · simpa [actualWord, targetWord, word] using centerImageEquiv_word 9
  · simpa [actualWord, targetWord, word] using centerImageEquiv_word 18

/-- Every mixed-radix word is sent to the identically marked product word. -/
theorem pairQuotient_word (v : Fin 36) :
    pairQuotient (word v actor) = targetWord v := by
  change centerImageEquiv (pureCenterAction.rangeRestrict (word v actor)) = _
  rw [map_word]
  exact centerImageEquiv_word v

theorem pairQuotient_surjective : Function.Surjective pairQuotient :=
  centerImageEquiv.surjective.comp pureCenterAction.rangeRestrict_surjective

theorem pairQuotient_kernel_eq_wordCore : pairQuotient.ker = pureWordCore := by
  have hker : pairQuotient.ker = pureCenterAction.ker := by
    ext x
    change centerImageEquiv (pureCenterAction.rangeRestrict x) = 1 ↔ pureCenterAction x = 1
    rw [← map_one centerImageEquiv, centerImageEquiv.injective.eq_iff]
    exact Subtype.ext_iff
  rw [hker]
  symm
  apply eq_of_le_of_card_ge pureWordCore_le_centerAction_kernel
  have hk := pureCenterAction.ker.card_mul_index
  rw [Subgroup.index_ker, pureCenterAction_range_card] at hk
  have hB : Nat.card pairGroup = 9216 :=
    (LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateOrders false 0).2.2
  rw [hB] at hk
  rw [pureWordCore_card]
  omega

theorem pairQuotient_kernel_isPGroup : IsPGroup 2 pairQuotient.ker := by
  rw [pairQuotient_kernel_eq_wordCore]
  exact pureWordCore_isPGroup

/-- The literal pure pair satisfies the residual-nine input used by the marked normalizer. -/
theorem pair_residual_core_quotient_card :
    Nat.card (pResidual 2 (LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateProduct false 0) ⧸
      pCore 2 (pResidual 2
        (LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateProduct false 0))) = 9 :=
  SymmetricThreeProductResidual.residual_core_quotient_card_of_surjective
    pairQuotient pairQuotient_surjective pairQuotient_kernel_isPGroup

end Held.AutomorphismLocalPair.ResidualNine
