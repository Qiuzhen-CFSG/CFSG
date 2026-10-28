module

public import Theory.SpecificGroups.Triality.QuadraticTori.OrthogonalRankOne.Roots

/-!
# The highest-root SL₂ and its commuting three-arm factor

Conjugating the proved central pinned SL₂ by central*arms constructs a
faithful highest-root SL₂ in the actual split Geck group. Its two
transvections are the two canonical highest-root curves. Root induction
extends orthogonality to commutation of entire rank-one images.
The conjugating word is already in the elementary fixed-point group, so
restriction to the base field gives a fixed highest-root factor. It
commutes with the graph-field fixed three-arm diagonal over the cubic field.

Source: the orbit-length field restriction and commuting constituents in
GLS3 §2.6, Proposition 2.6.2(a,b), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.QuadraticTori.OrthogonalRankOne
noncomputable section
local instance : InvolutiveNeg (TypeDRootIndex 4) := (typeDRootPairing 2).indexNeg

/-- The highest-root rank-one map is a conjugate of the central pinned map. -/
def highestSplitMap (P : Parameters) (hp : P.prime = 2) :
    SL(2, ExtensionField P) →* SplitGroup P :=
  (MulAut.conj (wordElement P [1, 0, 2, 3])).toMonoidHom.comp
    ((pinnedRankOneMaps P hp).hom 1)

theorem highestSplitMap_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (highestSplitMap P hp) :=
  (MulAut.conj _).injective.comp ((pinnedRankOneMaps P hp).injective 1)

theorem highestSplitMap_positive (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    highestSplitMap P hp (SpecialLinearGroup.transvection
      (i := (0 : Fin 2)) (j := 1) (by decide) t) = rootElement P 0 t := by
  change wordElement P _ * (pinnedRankOneMaps P hp).hom 1 _ * (wordElement P _)⁻¹ = _
  rw [(pinnedRankOneMaps P hp).positive, ← rootElement_positive,
    wordElement_conjugation P hp]
  rfl

theorem highestSplitMap_negative (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    highestSplitMap P hp (SpecialLinearGroup.transvection
      (i := (1 : Fin 2)) (j := 0) (by decide) t) = rootElement P 3 t := by
  change wordElement P _ * (pinnedRankOneMaps P hp).hom 1 _ * (wordElement P _)⁻¹ = _
  rw [(pinnedRankOneMaps P hp).negative, ← rootElement_negative,
    wordElement_conjugation P hp]
  rfl

/-- Orthogonality of the curves gives commutation of the entire rank-one images. -/
theorem pinned_highest_commute (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (hi : i ≠ 1) (g h : SL(2, ExtensionField P)) :
    Commute ((pinnedRankOneMaps P hp).hom i g) (highestSplitMap P hp h) := by
  let D := pinnedRankOneMaps P hp
  have hc (s : Bool) (t : ExtensionField P) :
      Commute (rootElement P (signedSimple s i) t) (highestSplitMap P hp h) := by
    apply sl2_root_induction (fun h =>
      Commute (rootElement P (signedSimple s i) t) (highestSplitMap P hp h)) ?_ ?_ ?_ h
    · intro u
      rw [highestSplitMap_positive]
      exact arm_highest_commute P hp i hi s true t u
    · intro u
      rw [highestSplitMap_negative]
      exact arm_highest_commute P hp i hi s false t u
    · intro a b ha hb
      simpa only [map_mul] using ha.mul_right hb
  apply sl2_root_induction (fun g => Commute (D.hom i g) (highestSplitMap P hp h)) ?_ ?_ ?_ g
  · intro t
    rw [D.positive]
    simpa only [signedSimple, if_true, rootElement_positive] using hc true t
  · intro t
    rw [D.negative]
    simpa only [signedSimple, Bool.false_eq_true, if_false, rootElement_negative] using hc false t
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_left hb

/-- The highest-root Weyl transport is itself in the actual elementary group. -/
def highestConjugator (P : Parameters) (hp : P.prime = 2) : ElementaryGroup P :=
  ConcreteBruhat.simpleElementary P hp .central * ConcreteBruhat.simpleElementary P hp .arms

theorem highestConjugator_word (P : Parameters) (hp : P.prime = 2) :
    elementaryInclusion P (highestConjugator P hp) = wordElement P [1, 0, 2, 3] := by
  calc
    _ = elementaryInclusion P (ConcreteBruhat.simpleElementary P hp .central) *
        elementaryInclusion P (ConcreteBruhat.simpleElementary P hp .arms) :=
      (elementaryInclusion P).map_mul _ _
    _ = weylWord P 1 1 * (weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1) :=
      congrArg₂ (· * ·) (ConcreteBruhat.elementaryInclusion_simple_central P hp)
        (ConcreteBruhat.elementaryInclusion_simple_arms P hp)
    _ = _ := by simp only [wordElement, mul_one, mul_assoc]

theorem highest_word_fixed (P : Parameters) (hp : P.prime = 2) :
    wordElement P [1, 0, 2, 3] ∈ fixedSubgroup P := by
  rw [← highestConjugator_word P hp]
  exact (highestConjugator P hp).val.property

/-- The highest-root factor restricted to the q-element base field. -/
def highestBaseEmbedding (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* SplitGroup P :=
  (highestSplitMap P hp).comp (sl2BaseEmbedding P)

theorem highestBaseEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (highestBaseEmbedding P hp) :=
  (highestSplitMap_injective P hp).comp (sl2BaseEmbedding_injective P)

theorem highestBaseEmbedding_fixed (P : Parameters) (hp : P.prime = 2)
    (g : SL(2, GaloisField P.prime P.exponent)) :
    highestBaseEmbedding P hp g ∈ fixedSubgroup P := by
  have hg : (pinnedRankOneMaps P hp).centralFixedEmbedding g ∈ fixedSubgroup P :=
    ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨g, rfl⟩).2
  exact (fixedSubgroup P).mul_mem
    ((fixedSubgroup P).mul_mem (highest_word_fixed P hp) hg)
    ((fixedSubgroup P).inv_mem (highest_word_fixed P hp))

/-- The fixed three-arm diagonal commutes with the base-field highest-root factor. -/
theorem arms_highest_commute (P : Parameters) (hp : P.prime = 2)
    (g : SL(2, ExtensionField P)) (h : SL(2, GaloisField P.prime P.exponent)) :
    Commute ((pinnedRankOneMaps P hp).armsFixedEmbedding (armRootCommutation P hp) g)
      (highestBaseEmbedding P hp h) := by
  exact ((pinned_highest_commute P hp 0 (by decide) _ _).mul_left
    (pinned_highest_commute P hp 2 (by decide) _ _)).mul_left
      (pinned_highest_commute P hp 3 (by decide) _ _)
end
end Triality.Standard.QuadraticTori.OrthogonalRankOne
