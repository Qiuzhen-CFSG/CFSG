module
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.LowerBound
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders

/-!
# The order of the concrete pure Held word subgroup

The first seven residual generators are involutions; the last squares to
q₂q₃q₄q₅. Together with the existing triangular conjugation relations,
these identities bound each step in the eight-generator series by two.
The resulting upper bound matches the 256 distinguished words.

Sources: the unchanged ATLAS pair (false,0) and ResidualRoots.Pair00;
GLS3 Table 5.3p, used in Aschbacher--Smith 15.3.41--42.

Extracted from `CFSG/Quasithin/Chapter15/Section03/ComponentUniqueness/RankTwo/NonCharacteristicTwo/SporadicSieve/HeldExclusion/ProperExtensionProfile/Quotients/PureInnerCore/WordOrder.lean`, preserving the literal words,
permutation tables and conjugation convention. Original ATLAS attribution and
license remain in `Theory/SpecificGroups/Held/Model/Source`.

-/

set_option Elab.async false
@[expose] public section
namespace Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.PureCoreCount
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open ResidualRoots.Pair00
attribute [local irreducible] ResidualRoots.generator

def squareWord : Fin 8 → List (Fin 8)
  | 7 => [2, 3, 4, 5]
  | _ => []

private theorem square_0 : ResidualRoots.generator false 0 0 ^ 2 =
    ResidualRoots.product false 0 (squareWord 0) := by
  change ResidualRoots.generator false 0 0 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q0_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_1 : ResidualRoots.generator false 0 1 ^ 2 =
    ResidualRoots.product false 0 (squareWord 1) := by
  change ResidualRoots.generator false 0 1 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_2 : ResidualRoots.generator false 0 2 ^ 2 =
    ResidualRoots.product false 0 (squareWord 2) := by
  change ResidualRoots.generator false 0 2 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_3 : ResidualRoots.generator false 0 3 ^ 2 =
    ResidualRoots.product false 0 (squareWord 3) := by
  change ResidualRoots.generator false 0 3 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_4 : ResidualRoots.generator false 0 4 ^ 2 =
    ResidualRoots.product false 0 (squareWord 4) := by
  change ResidualRoots.generator false 0 4 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q4_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_5 : ResidualRoots.generator false 0 5 ^ 2 =
    ResidualRoots.product false 0 (squareWord 5) := by
  change ResidualRoots.generator false 0 5 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q5_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_6 : ResidualRoots.generator false 0 6 ^ 2 =
    ResidualRoots.product false 0 (squareWord 6) := by
  change ResidualRoots.generator false 0 6 ^ 2 = 1
  apply Held.representation_injective
  simp only [map_pow, map_one, ← q6_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem square_7 : ResidualRoots.generator false 0 7 ^ 2 =
    ResidualRoots.product false 0 (squareWord 7) := by
  change ResidualRoots.generator false 0 7 ^ 2 = ResidualRoots.generator false 0 2 * (ResidualRoots.generator false 0 3 * (ResidualRoots.generator false 0 4 * (ResidualRoots.generator false 0 5 * 1)))
  apply Held.representation_injective
  simp only [map_pow, map_mul, map_one, ← q2_eq, ← q3_eq, ← q4_eq, ← q5_eq, ← q7_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

theorem generator_square (k : Fin 8) : ResidualRoots.generator false 0 k ^ 2 =
    ResidualRoots.product false 0 (squareWord k) := by
  fin_cases k
  · exact square_0
  · exact square_1
  · exact square_2
  · exact square_3
  · exact square_4
  · exact square_5
  · exact square_6
  · exact square_7

private theorem triangular_0 : triangular
    (([0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 0 []
    (by decide) (squareWord 0) (ResidualRoots.internalWord false 0 0) (generator_square 0)
  · intro b hb
    exact False.elim (List.not_mem_nil hb)
  · decide
  · decide
  · trivial

private theorem triangular_1 : triangular
    (([1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 1 [0]
    (by decide) (squareWord 1) (ResidualRoots.internalWord false 0 1) (generator_square 1)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([0] : List (Fin 8)) → b < 1 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_0

private theorem triangular_2 : triangular
    (([2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 2 [1, 0]
    (by decide) (squareWord 2) (ResidualRoots.internalWord false 0 2) (generator_square 2)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([1, 0] : List (Fin 8)) → b < 2 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_1

private theorem triangular_3 : triangular
    (([3, 2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 3 [2, 1, 0]
    (by decide) (squareWord 3) (ResidualRoots.internalWord false 0 3) (generator_square 3)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([2, 1, 0] : List (Fin 8)) → b < 3 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_2

private theorem triangular_4 : triangular
    (([4, 3, 2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 4 [3, 2, 1, 0]
    (by decide) (squareWord 4) (ResidualRoots.internalWord false 0 4) (generator_square 4)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([3, 2, 1, 0] : List (Fin 8)) → b < 4 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_3

private theorem triangular_5 : triangular
    (([5, 4, 3, 2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 5 [4, 3, 2, 1, 0]
    (by decide) (squareWord 5) (ResidualRoots.internalWord false 0 5) (generator_square 5)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([4, 3, 2, 1, 0] : List (Fin 8)) → b < 5 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_4

private theorem triangular_6 : triangular
    (([6, 5, 4, 3, 2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 6 [5, 4, 3, 2, 1, 0]
    (by decide) (squareWord 6) (ResidualRoots.internalWord false 0 6) (generator_square 6)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([5, 4, 3, 2, 1, 0] : List (Fin 8)) → b < 6 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_5

private theorem triangular_7 : triangular
    (([7, 6, 5, 4, 3, 2, 1, 0] : List (Fin 8)).map (fun k => (ResidualRoots.generator false 0 k, 2))) := by
  apply triangular_cons_words (ResidualRoots.generator false 0) (fun _ => 2) 7 [6, 5, 4, 3, 2, 1, 0]
    (by decide) (squareWord 7) (ResidualRoots.internalWord false 0 7) (generator_square 7)
  · intro b hb
    apply ResidualRoots.Pair00.internal
    have : ∀ b : Fin 8, b ∈ ([6, 5, 4, 3, 2, 1, 0] : List (Fin 8)) → b < 7 := by decide
    exact this b hb
  · decide
  · decide
  · exact triangular_6

theorem wordGroup_card_upper : Nat.card (ResidualRoots.group false 0) ≤ 256 := by
  have h := card_le _ triangular_7
  have he : Prod.fst '' {x | x ∈ ([7, 6, 5, 4, 3, 2, 1, 0] : List (Fin 8)).map
      (fun k => (ResidualRoots.generator false 0 k, 2))} =
      Set.range (ResidualRoots.generator false 0) := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨k, _, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨(ResidualRoots.generator false 0 k, 2), ⟨k, ?_, rfl⟩, rfl⟩
      fin_cases k <;> simp
  rw [he] at h
  exact h

end Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.PureCoreCount

namespace Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate

theorem pureWordCore_card : Nat.card pureWordCore = 256 := by
  apply Nat.le_antisymm _ pureWordCore_card_lower
  rw [show Nat.card pureWordCore = Nat.card
      (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.group false 0) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe pureWordGroup_le).toEquiv]
  exact PureCoreCount.wordGroup_card_upper

namespace PureCoreCount

/-- The 256 binary words, regarded as elements of the actual word subgroup. -/
def normalFormElement (v : Fin 256) : pureWordCore :=
  ⟨⟨normalForm v, pureWordGroup_le (normalForm_mem v)⟩, normalForm_mem v⟩

attribute [local irreducible] normalForm normalTable decode

theorem normalFormElement_bijective : Function.Bijective normalFormElement := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by rw [Nat.card_fin, pureWordCore_card]⟩
  intro i j hij
  apply Fin.ext
  rw [← decode_normal i, ← decode_normal j, normalTable_eq, normalTable_eq]
  have he := congrArg (fun x : pureWordCore => ((x : pairGroup) : Held.He)) hij
  change normalForm i = normalForm j at he
  rw [he]

/-- Finite coordinates for the word subgroup, with its literal inclusion in B. -/
noncomputable def normalFormEquiv : Fin 256 ≃ pureWordCore :=
  Equiv.ofBijective normalFormElement normalFormElement_bijective

end PureCoreCount

/-- The order-256 word subgroup is already in the center-action kernel. -/
theorem pureCenterAction_range_card_le : Nat.card pureCenterAction.range ≤ 36 := by
  have hl := Subgroup.card_le_of_le pureWordCore_le_centerAction_kernel
  rw [pureWordCore_card] at hl
  have hk := pureCenterAction.ker.card_mul_index
  rw [Subgroup.index_ker] at hk
  have hB : Nat.card (pairGroup) = 9216 :=
    (Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateOrders false 0).2.2
  rw [hB] at hk
  have h := Nat.mul_le_mul_right (Nat.card pureCenterAction.range) hl
  rw [hk] at h
  omega

end Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate
