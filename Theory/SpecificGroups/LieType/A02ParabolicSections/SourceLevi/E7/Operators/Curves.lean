module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.Operators

/-!
# The twelve simple E7 root matrices over any ring

At parameter one the positive root curve is the sum of the identity, its
linear operator and its single quadratic entry. Root negation exchanges the
positive and negative divided powers. Thus the same integer tables give all
twelve native root curves after scalar extension to any commutative ring.
Source: Geck's integral root curves; GLS3 §1.12 and §2.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.Operators.Curves
open Coordinates
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

def negation (r : Fin 126) : Fin 126 :=
  (#[1, 0, 5, 4, 3, 2, 9, 8, 7, 6, 13, 12, 11, 10, 17, 16, 15, 14, 21, 20, 19, 18, 25, 24, 23, 22, 29, 28, 27, 26, 33, 32, 31, 30, 37, 36, 35, 34, 41, 40, 39, 38, 45, 44, 43, 42, 49, 48, 47, 46, 53, 52, 51, 50, 57, 56, 55, 54, 61, 60, 59, 58, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62] : Array (Fin 126))[r.val]!

def flipIndex (r : Fin 133) : Fin 133 :=
  finSumFinEquiv (Sum.map id negation (finSumFinEquiv.symm r))

def positiveInteger (i : Fin 6) : Matrix (Fin 133) (Fin 133) ℤ :=
  1 + positiveLinear i + positiveQuadratic i

def negativeInteger (i : Fin 6) : Matrix (Fin 133) (Fin 133) ℤ :=
  fun r c => positiveInteger i (flipIndex r) (flipIndex c)

/-- Positive then negative at each of the six native simple nodes. -/
def integerGenerator : Fin 12 → Matrix (Fin 133) (Fin 133) ℤ :=
  ![positiveInteger 0, negativeInteger 0, positiveInteger 1, negativeInteger 1,
    positiveInteger 2, negativeInteger 2, positiveInteger 3, negativeInteger 3,
    positiveInteger 4, negativeInteger 4, positiveInteger 5, negativeInteger 5]

noncomputable section
open scoped Classical
local instance : InvolutiveNeg typeE7Roots := typeE7RootPairing.indexNeg
local instance : Fintype typeE7Roots := Fintype.ofFinite _

private def flip : Basis → Basis
  | .inl i => .inl i
  | .inr r => .inr (-r)

private theorem flip_involutive : Function.Involutive flip := by
  rintro (i | r)
  · rfl
  · change Sum.inr (-(-r)) = Sum.inr r
    rw [neg_neg]

private theorem root_negation (r : Fin 126) : root (negation r) = -root r := by
  apply typeE7RootPairing.root.injective
  rw [RootPairing.indexNeg_neg, typeE7RootPairing.root_reflectionPerm,
    typeE7RootPairing.reflection_apply_self]
  apply Subtype.ext
  funext q
  have hc : ∀ r : Fin 126, coord (negation r) = -coord r := by decide +kernel
  have h := congrFun (hc r) q
  change (coord (negation r) q : ℝ) / 2 = -((coord r q : ℝ) / 2)
  change coord (negation r) q = -coord r q at h
  rw [h, Int.cast_neg]
  ring

private theorem basis_flip (r : Fin 133) : basisEquiv (flipIndex r) = flip (basisEquiv r) := by
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 7) (n := 126)).surjective r
  rcases r with i | r
  · simp [basisEquiv, flipIndex, flip]
  · simpa only [basisEquiv, flipIndex, Equiv.trans_apply, Equiv.symm_apply_apply,
      Sum.map_inr, Equiv.sumCongr_apply, flip, rootEquiv, Equiv.coe_ofBijective]
      using congrArg Sum.inr (root_negation r)

private theorem omega_entry (r c : Basis) :
    omegaMatrix (b := typeE7RootPairing_base) r c = if flip r = c then (1 : ℤ) else 0 := by
  rcases r with r | r <;> rcases c with c | c
  · simp [omegaMatrix, flip, Matrix.one_apply]
  · simp [omegaMatrix, flip]
  · simp [omegaMatrix, flip]
  · have h : flip (Sum.inr r) = Sum.inr c ↔ r = -c := by
      simp only [flip, Sum.inr.injEq, neg_eq_iff_eq_neg]
    simp only [omegaMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, h]

private theorem omega_left (A : Matrix Basis Basis ℤ) (r c : Basis) :
    (omegaMatrix (b := typeE7RootPairing_base) * A) r c = A (flip r) c := by
  simp [Matrix.mul_apply, omega_entry]

private theorem omega_right (A : Matrix Basis Basis ℤ) (r c : Basis) :
    (A * omegaMatrix (b := typeE7RootPairing_base)) r c = A r (flip c) := by
  have h (k : Basis) : flip k = c ↔ k = flip c := by
    constructor
    · intro h; simpa only [flip_involutive k] using congrArg flip h
    · rintro rfl; exact flip_involutive c
  simp [Matrix.mul_apply, omega_entry, h]

private theorem fDividedPower_flip (i : typeE7RootPairing_base.support) (n : ℕ) (r c : Basis) :
    fDividedPower i n r c = eDividedPower i n (flip r) (flip c) := by
  rw [fDividedPower, omega_right, omega_left]

private theorem negativeMatrix_flip {S : Type*} [CommRing S]
    (i : typeE7RootPairing_base.support) (t : S) (r c : Basis) :
    negativeMatrix i t r c = positiveMatrix i t (flip r) (flip c) := by
  simp only [positiveMatrix_formula, negativeMatrix_formula, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, fDividedPower_flip,
    Matrix.one_apply, flip_involutive.injective.eq_iff]

variable {S : Type*} [CommRing S]

/-- Every positive simple curve is the scalar extension of the displayed integer table. -/
theorem positive_one (i : Fin 6) :
    reindex (positiveMatrix (typeE7RootPairing_baseEquiv (node i)) (1 : S)) =
      (positiveInteger i).map (Int.castRingHom S) := by
  rw [positiveMatrix_formula]
  simp only [map_add, map_one, reindex_map, eDividedPower_one,
    positiveLinear_eq, positiveQuadratic_eq, positiveCubic_eq_zero,
    one_pow, one_smul]
  ext r c
  simp [positiveInteger, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]

/-- Root negation gives every negative simple curve in the same native basis. -/
theorem negative_one (i : Fin 6) :
    reindex (negativeMatrix (typeE7RootPairing_baseEquiv (node i)) (1 : S)) =
      (negativeInteger i).map (Int.castRingHom S) := by
  ext r c
  rw [reindex_apply, negativeMatrix_flip, ← basis_flip, ← basis_flip]
  change reindex (positiveMatrix (typeE7RootPairing_baseEquiv (node i)) (1 : S))
      (flipIndex r) (flipIndex c) = _
  rw [positive_one]
  rfl

end
end Theory.SpecificGroups.LieType.SourceLevi.E7.Operators.Curves
