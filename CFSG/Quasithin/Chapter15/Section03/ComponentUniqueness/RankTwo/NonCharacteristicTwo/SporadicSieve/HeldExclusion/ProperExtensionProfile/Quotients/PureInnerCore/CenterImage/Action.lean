module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.CenterImage.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.CenterImage.SmallPerm

/-!
# Literal Held conjugation on the central sixteen-set

The four original pair generators r₀,r₁,t₀,t₁ act on the sixteen central
words by the checked permutations of SmallPerm. These identities are
verified on every letter of the existing faithful degree-2058 representation
and then transported to the canonical action on the center of pureWordCore.
The remaining two pair generators are unnecessary: these four already give
36 distinct images, matching the independently proved upper bound.

Sources: unchanged ATLAS pair words and ResidualRoots.Pair00 tables;
GLS3 Table 5.3p; Aschbacher--Smith 15.3.41–42, printed p.1138.
-/

set_option Elab.async false
@[expose] public section
open Subgroup
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open ResidualRoots.Pair00
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CenterImageCertificate
attribute [local irreducible] ResidualRoots.generator ResidualRoots.pairGenerator

def actor (k : Fin 4) : innerLocal true :=
  ⟨ResidualRoots.pairGenerator false 0 ⟨k.val, by omega⟩,
    ResidualRoots.pairGenerator_mem false 0 _⟩

def actorTable (k : Fin 4) : Equiv.Perm (Fin 2058) := ![Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair00.odd0,
    Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair00.odd1, pair2, pair3] k

theorem actorTable_eq (k : Fin 4) : actorTable k = Held.representation (actor k) := by
  fin_cases k
  · exact pair0_eq
  · exact pair1_eq
  · exact pair2_eq
  · exact pair3_eq

private theorem action_0_0 :
    actorTable 0 * centralTable 0 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_1 :
    actorTable 0 * centralTable 1 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_2 :
    actorTable 0 * centralTable 2 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_3 :
    actorTable 0 * centralTable 3 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_4 :
    actorTable 0 * centralTable 4 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_5 :
    actorTable 0 * centralTable 5 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_6 :
    actorTable 0 * centralTable 6 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_7 :
    actorTable 0 * centralTable 7 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_8 :
    actorTable 0 * centralTable 8 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_9 :
    actorTable 0 * centralTable 9 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_10 :
    actorTable 0 * centralTable 10 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_11 :
    actorTable 0 * centralTable 11 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_12 :
    actorTable 0 * centralTable 12 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_13 :
    actorTable 0 * centralTable 13 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_14 :
    actorTable 0 * centralTable 14 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_0_15 :
    actorTable 0 * centralTable 15 * (actorTable 0)⁻¹ =
      centralTable (smallGenerator 0 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_0 :
    actorTable 1 * centralTable 0 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_1 :
    actorTable 1 * centralTable 1 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_2 :
    actorTable 1 * centralTable 2 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_3 :
    actorTable 1 * centralTable 3 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_4 :
    actorTable 1 * centralTable 4 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_5 :
    actorTable 1 * centralTable 5 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_6 :
    actorTable 1 * centralTable 6 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_7 :
    actorTable 1 * centralTable 7 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_8 :
    actorTable 1 * centralTable 8 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_9 :
    actorTable 1 * centralTable 9 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_10 :
    actorTable 1 * centralTable 10 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_11 :
    actorTable 1 * centralTable 11 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_12 :
    actorTable 1 * centralTable 12 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_13 :
    actorTable 1 * centralTable 13 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_14 :
    actorTable 1 * centralTable 14 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_1_15 :
    actorTable 1 * centralTable 15 * (actorTable 1)⁻¹ =
      centralTable (smallGenerator 1 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_0 :
    actorTable 2 * centralTable 0 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_1 :
    actorTable 2 * centralTable 1 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_2 :
    actorTable 2 * centralTable 2 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_3 :
    actorTable 2 * centralTable 3 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_4 :
    actorTable 2 * centralTable 4 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_5 :
    actorTable 2 * centralTable 5 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_6 :
    actorTable 2 * centralTable 6 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_7 :
    actorTable 2 * centralTable 7 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_8 :
    actorTable 2 * centralTable 8 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_9 :
    actorTable 2 * centralTable 9 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_10 :
    actorTable 2 * centralTable 10 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_11 :
    actorTable 2 * centralTable 11 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_12 :
    actorTable 2 * centralTable 12 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_13 :
    actorTable 2 * centralTable 13 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_14 :
    actorTable 2 * centralTable 14 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_2_15 :
    actorTable 2 * centralTable 15 * (actorTable 2)⁻¹ =
      centralTable (smallGenerator 2 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_0 :
    actorTable 3 * centralTable 0 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_1 :
    actorTable 3 * centralTable 1 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_2 :
    actorTable 3 * centralTable 2 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_3 :
    actorTable 3 * centralTable 3 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_4 :
    actorTable 3 * centralTable 4 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 4) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_5 :
    actorTable 3 * centralTable 5 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 5) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_6 :
    actorTable 3 * centralTable 6 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 6) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_7 :
    actorTable 3 * centralTable 7 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 7) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_8 :
    actorTable 3 * centralTable 8 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 8) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_9 :
    actorTable 3 * centralTable 9 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 9) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_10 :
    actorTable 3 * centralTable 10 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 10) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_11 :
    actorTable 3 * centralTable 11 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 11) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_12 :
    actorTable 3 * centralTable 12 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 12) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_13 :
    actorTable 3 * centralTable 13 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 13) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_14 :
    actorTable 3 * centralTable 14 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 14) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem action_3_15 :
    actorTable 3 * centralTable 15 * (actorTable 3)⁻¹ =
      centralTable (smallGenerator 3 15) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

theorem action_certificate (k : Fin 4) (v : Fin 16) :
    actorTable k * centralTable v * (actorTable k)⁻¹ =
      centralTable (smallGenerator k v) := by
  fin_cases k <;> fin_cases v
  · exact action_0_0
  · exact action_0_1
  · exact action_0_2
  · exact action_0_3
  · exact action_0_4
  · exact action_0_5
  · exact action_0_6
  · exact action_0_7
  · exact action_0_8
  · exact action_0_9
  · exact action_0_10
  · exact action_0_11
  · exact action_0_12
  · exact action_0_13
  · exact action_0_14
  · exact action_0_15
  · exact action_1_0
  · exact action_1_1
  · exact action_1_2
  · exact action_1_3
  · exact action_1_4
  · exact action_1_5
  · exact action_1_6
  · exact action_1_7
  · exact action_1_8
  · exact action_1_9
  · exact action_1_10
  · exact action_1_11
  · exact action_1_12
  · exact action_1_13
  · exact action_1_14
  · exact action_1_15
  · exact action_2_0
  · exact action_2_1
  · exact action_2_2
  · exact action_2_3
  · exact action_2_4
  · exact action_2_5
  · exact action_2_6
  · exact action_2_7
  · exact action_2_8
  · exact action_2_9
  · exact action_2_10
  · exact action_2_11
  · exact action_2_12
  · exact action_2_13
  · exact action_2_14
  · exact action_2_15
  · exact action_3_0
  · exact action_3_1
  · exact action_3_2
  · exact action_3_3
  · exact action_3_4
  · exact action_3_5
  · exact action_3_6
  · exact action_3_7
  · exact action_3_8
  · exact action_3_9
  · exact action_3_10
  · exact action_3_11
  · exact action_3_12
  · exact action_3_13
  · exact action_3_14
  · exact action_3_15

/-- Compatibility is with the canonical center action, including its orientation. -/
theorem generator_action (k : Fin 4) (v : Fin 16) :
    pureCenterAction (actor k) (centralWord v) = centralWord (smallGenerator k v) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Held.representation_injective
  change Held.representation ((actor k : Held.He) *
    (((centralWord v : pureWordCore) : innerLocal true) : Held.He) *
    (actor k : Held.He)⁻¹) = _
  simp only [map_mul, map_inv]
  change Held.representation (actor k) * centerRepresentation (centralWord v) *
    (Held.representation (actor k))⁻¹ =
      centerRepresentation (centralWord (smallGenerator k v))
  rw [← actorTable_eq, ← centralTable_eq, ← centralTable_eq]
  exact action_certificate k v

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CenterImageCertificate
