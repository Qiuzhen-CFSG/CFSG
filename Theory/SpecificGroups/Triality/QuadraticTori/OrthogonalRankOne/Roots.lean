module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.RootCurves
public import Theory.SpecificGroups.Triality.LeviArmCommutation

/-!
# The orthogonal arms and highest root in the actual D₄ group

The highest root is α₀ + 2α₁ + α₂ + α₃, the canonical positive coordinate 11.
The word central*arms takes the central simple root to this highest root,
with the same direct-conjugation convention as the actual Geck Weyl matrices.
For each arm, a short common Weyl word takes a pair of distinct simple arms
to that arm and the highest root. The three possible orthogonal-pair types
use different starting pairs. Transporting the proved simple-arm commutation
along these words proves commutation for all four root-sign combinations.
The finite certificates check only the root indices; all matrix identities
come from the published canonical-root conjugation theorem.

This is the extended-root subsystem A₁⁴ used in GLS3 §2.6, Proposition
2.6.2(a,b), `refs/KGroup/GLS3/chapter2.tex`. Its direct-product property
will follow from characteristic-two centerlessness, rather than the
simple-subset hypothesis of 2.6.2(d).
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

/-- All signed canonical root curves in the genuine split group. -/
def rootElement (P : Parameters) (r : Fin 24) (t : ExtensionField P) : SplitGroup P :=
  ⟨rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
    (rootEnumeration r) t, rootCurveUnit_mem_simpleSubgroup _ _⟩

private theorem enumeration_negative (r : Fin 24) :
    rootEnumeration (negativeIndex r) = -rootEnumeration r := by
  apply (typeDRootPairing 2).root_eq_neg_iff.mp
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_neg, Pi.neg_apply, rootCoords_spec]
  rw [rootCoords_negativeIndex]
  simp

theorem rootElement_positive (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    rootElement P (simpleIndex i) t = positiveRoot P i t := by
  apply Subtype.ext
  dsimp only [rootElement, positiveRoot, RootPairing.SimpleGeckGroup.positive]
  rw [rootEnumeration_simpleIndex, ← typeDRootPairing_baseEquiv_val]
  exact rootCurveUnit_simple _ _

theorem rootElement_negative (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    rootElement P (negativeIndex (simpleIndex i)) t = negativeRoot P i t := by
  apply Subtype.ext
  dsimp only [rootElement, negativeRoot, RootPairing.SimpleGeckGroup.negative]
  rw [enumeration_negative, rootEnumeration_simpleIndex, ← typeDRootPairing_baseEquiv_val]
  exact rootCurveUnit_neg_simple _ _

def signedSimple (s : Bool) (i : Fin 4) : Fin 24 :=
  if s then simpleIndex i else negativeIndex (simpleIndex i)

def signedHighest (s : Bool) : Fin 24 := if s then 0 else 3

/-- The numbered positive curve is precisely the canonical highest-root curve. -/
theorem rootElement_highest (P : Parameters) (t : ExtensionField P) :
    rootElement P 0 t = curve P 11 t := rfl

/-- Root action and group word have the same left-to-right convention. -/
def wordAction : List (Fin 4) → Fin 24 → Fin 24
  | [], r => r
  | i :: w, r => reflectionTable i (wordAction w r)

def wordElement (P : Parameters) : List (Fin 4) → SplitGroup P
  | [] => 1
  | i :: w => weylWord P i 1 * wordElement P w

theorem wordElement_conjugation (P : Parameters) (hp : P.prime = 2)
    (w : List (Fin 4)) (r : Fin 24) (t : ExtensionField P) :
    wordElement P w * rootElement P r t * (wordElement P w)⁻¹ =
      rootElement P (wordAction w r) t := by
  induction w with
  | nil => simp [wordElement, wordAction]
  | cons i w ih =>
    have hs (r : Fin 24) : weylWord P i 1 * rootElement P r t * (weylWord P i 1)⁻¹ =
        rootElement P (reflectionTable i r) t := by
      apply Subtype.ext
      exact (ConcreteBruhat.RootConjugation.weylWord_rootCurveUnit_conjugation P hp
        i (rootEnumeration r) t).trans
          (congrArg (fun a => rootCurveUnit
            (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) a t)
            (rootEnumeration_reflectionTable i r).symm)
    simp only [wordElement, wordAction, _root_.mul_inv_rev]
    calc
      _ = weylWord P i 1 *
          (wordElement P w * rootElement P r t * (wordElement P w)⁻¹) *
          (weylWord P i 1)⁻¹ := by group
      _ = _ := by rw [ih, hs]

/-- The Weyl word central*arms takes both central root signs to the highest root signs. -/
theorem highest_route (s : Bool) :
    wordAction [1, 0, 2, 3] (signedSimple s 1) = signedHighest s := by
  cases s <;> decide +kernel

private def pairWord (i : Fin 4) : List (Fin 4) :=
  if i = 3 then [1, 3, 0, 1] else [1, 2, 0, 1]
private def pairLeft (i : Fin 4) : Fin 4 := if i = 0 then 2 else 0
private def pairRight (i : Fin 4) : Fin 4 := if i = 3 then 2 else 3

private theorem pair_checked (i : Fin 4) (hi : i ≠ 1) (s : Bool) :
    pairLeft i ≠ 1 ∧ pairRight i ≠ 1 ∧ pairLeft i ≠ pairRight i ∧
    wordAction (pairWord i) (signedSimple s (pairLeft i)) = signedSimple s i ∧
    wordAction (pairWord i) (signedSimple s (pairRight i)) = signedHighest s := by
  revert i s
  decide +kernel

private theorem signed_arms_commute (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) (hij : i ≠ j)
    (s v : Bool) (t u : ExtensionField P) :
    Commute (rootElement P (signedSimple s i) t) (rootElement P (signedSimple v j) u) := by
  have C := armRootCommutation P hp
  cases s <;> cases v <;>
    simp only [signedSimple, Bool.false_eq_true, if_false, if_true,
      rootElement_positive, rootElement_negative]
  · exact C.negative_negative i j hi hj hij t u
  · exact (C.positive_negative j i hj hi hij.symm u t).symm
  · exact C.positive_negative i j hi hj hij t u
  · exact C.positive_positive i j hi hj hij t u

/-- All four sign combinations of an arm and the highest root commute. -/
theorem arm_highest_commute (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (hi : i ≠ 1) (s v : Bool) (t u : ExtensionField P) :
    Commute (rootElement P (signedSimple s i) t)
      (rootElement P (signedHighest v) u) := by
  obtain ⟨hl, hr, hne, hs, _⟩ := pair_checked i hi s
  have hv := (pair_checked i hi v).2.2.2.2
  have h := (signed_arms_commute P hp (pairLeft i) (pairRight i) hl hr hne s v t u).map
    (MulAut.conj (wordElement P (pairWord i))).toMonoidHom
  change Commute
    (wordElement P (pairWord i) * rootElement P (signedSimple s (pairLeft i)) t *
      (wordElement P (pairWord i))⁻¹)
    (wordElement P (pairWord i) * rootElement P (signedSimple v (pairRight i)) u *
      (wordElement P (pairWord i))⁻¹) at h
  simpa only [wordElement_conjugation P hp, hs, hv] using h
end
end Triality.Standard.QuadraticTori.OrthogonalRankOne
