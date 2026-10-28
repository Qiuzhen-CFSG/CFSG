module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.WordCover
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.NormalSteps

/-!
# Finite branches for the outer Held elementary catalogue

The nodes are exactly bottom and the four published inner-automorphism images,
regarded as subgroups of the full outer stabilizer. One-element extensions use
the fixed 2048-word cover. Normality and elementary abelianness exclude an
outer-coset element if its square is nonidentity, or if it fails to commute
with a conjugate by one of the four inner generators or the published actor.

Explicit lifts into the faithful permutation normalizer connect these tests to
the original ATLAS carrier. This module proves the soundness of rejection; it
does not assert any finite rejection or extension calculation.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`Coverage/source/README.md` and the existing pure-pair collection certificates.
-/

@[expose] public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
open RepresentativeImages Exhaustion.CandidateOrderCertificate.Factors

/-- The four fixed rows and bottom, restricted to the full stabilizer. -/
def node : Option (Fin 4) → Subgroup outerRepresentative
  | none => ⊥
  | some j => (ambientRow j).subgroupOf outerRepresentative

/-- The exact one-element extension to which the normal-index-two argument applies. -/
def extension (i : Option (Fin 4)) (n : Bool × Fin 1024) : Subgroup outerRepresentative :=
  node i ⊔ zpowers (element n)

theorem node_map_subtype (j : Fin 4) :
    (node (some j)).map outerRepresentative.subtype = ambientRow j :=
  map_subgroupOf_eq_of_le (ambientRow_le_outerRepresentative j)

theorem element_mem_extension (i : Option (Fin 4)) (n : Bool × Fin 1024) :
    element n ∈ extension i n := mem_sup_right (mem_zpowers _)

/-- The four inner generators followed by the actual outer actor. -/
def testActor : Fin 5 → outerRepresentative
  | 0 => inner (generator 0)
  | 1 => inner (generator 1)
  | 2 => inner (generator 2)
  | 3 => inner (generator 3)
  | 4 => actor

/-- A finite rejection condition for the 1024 outer-coset words. -/
def outerObstruction (n : Fin 1024) : Prop :=
  element (true, n) ^ 2 ≠ 1 ∨ ∃ k : Fin 5,
    ¬Commute (element (true, n))
      ((testActor k)⁻¹ * element (true, n) * testActor k)

/-- Either obstruction excludes the element from every normal elementary subgroup
of the same full stabilizer. -/
theorem not_mem_of_outerObstruction (n : Fin 1024) (h : outerObstruction n)
    (R : Subgroup outerRepresentative) (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    element (true, n) ∉ R := by
  let := he
  intro hx
  rcases h with hsq | ⟨k, hc⟩
  · exact hsq (elemPow_eq_one_of_isElementaryAbelian _ hx)
  · apply hc
    exact setLike_mul_comm hx (hn.conj_mem' _ hx (testActor k))

/-- The same word in the faithful permutation normalizer, for finite certificates. -/
def elementLift (n : Bool × Fin 1024) : PermutationNormalizer :=
  innerEmbedding (pureElement n.2).val * if n.1 then (PureActors.actor false).val else 1

/-- Permutation lifts of precisely the five permitted normality tests. -/
def testLift : Fin 5 → PermutationNormalizer
  | 0 => innerEmbedding (generator 0).val
  | 1 => innerEmbedding (generator 1).val
  | 2 => innerEmbedding (generator 2).val
  | 3 => innerEmbedding (generator 3).val
  | 4 => (PureActors.actor false).val

theorem elementLift_action (n : Bool × Fin 1024) :
    permutationGroup.normalizerMonoidHom (elementLift n) = (element n).val := by
  rcases n with ⟨b, n⟩
  cases b
  · change permutationGroup.normalizerMonoidHom (innerEmbedding (pureElement n).val * 1) =
      MulAut.conj (pureElement n).val * 1
    rw [map_mul, map_one, normalizerAction_innerEmbedding]
  · change permutationGroup.normalizerMonoidHom
      (innerEmbedding (pureElement n).val * (PureActors.actor false).val) =
      MulAut.conj (pureElement n).val * _
    rw [map_mul, normalizerAction_innerEmbedding]
    rfl

theorem testLift_action (k : Fin 5) :
    permutationGroup.normalizerMonoidHom (testLift k) = (testActor k).val := by
  fin_cases k
  · exact normalizerAction_innerEmbedding _
  · exact normalizerAction_innerEmbedding _
  · exact normalizerAction_innerEmbedding _
  · exact normalizerAction_innerEmbedding _
  · rfl

/-- The already certified tables evaluate the word family on the original 2058 letters. -/
theorem elementLift_val (n : Bool × Fin 1024) :
    (elementLift n).val = Pair00Two.normalTable n.2 *
      if n.1 then PureActors.Actor0.perm else 1 := by
  rcases n with ⟨b, n⟩
  cases b
  · change representation (Pair00Two.normalForm n) * 1 = Pair00Two.normalTable n * 1
    rw [Pair00Two.normalTable_eq]
  · change representation (Pair00Two.normalForm n) * PureActors.Actor0.perm =
      Pair00Two.normalTable n * PureActors.Actor0.perm
    rw [Pair00Two.normalTable_eq]

/-- Faithfulness transports checked permutation-normalizer obstructions to the
actual automorphism stabilizer. No realization premise is needed for this direction. -/
theorem outerObstruction_of_lifts (n : Fin 1024)
    (h : elementLift (true, n) ^ 2 ≠ 1 ∨ ∃ k : Fin 5,
      ¬Commute (elementLift (true, n))
        ((testLift k)⁻¹ * elementLift (true, n) * testLift k)) : outerObstruction n := by
  rcases h with hsq | ⟨k, hc⟩
  · left
    intro he
    apply hsq
    apply normalizerAction_injective
    rw [map_pow, map_one, elementLift_action]
    exact congrArg Subtype.val he
  · right
    refine ⟨k, fun he => hc ?_⟩
    apply normalizerAction_injective
    simp only [map_mul, map_inv, elementLift_action, testLift_action]
    exact congrArg Subtype.val he.eq

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
