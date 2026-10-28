module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators

/-!
# The twelve simple E8 root matrices over any ring

At parameter one the positive root curve is the sum of the identity, its
linear operator and its single quadratic entry. Root negation exchanges the
positive and negative divided powers. Thus the same integer tables give all
twelve native root curves after scalar extension to any commutative ring.
Source: Geck's integral root curves; GLS3 §1.12 and §2.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Curves
open Coordinates
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

def negation (r : Fin 240) : Fin 240 :=
  (#[3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60, 67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76, 83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92, 99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108, 239, 238, 237, 236, 235, 234, 233, 232, 231, 230, 229, 228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 218, 217, 216, 215, 214, 213, 212, 211, 210, 209, 208, 207, 206, 205, 204, 203, 202, 201, 200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112] : Array (Fin 240))[r.val]!

def flipIndex (r : Fin 248) : Fin 248 :=
  finSumFinEquiv (Sum.map id negation (finSumFinEquiv.symm r))

def positiveInteger (i : Fin 6) : Matrix (Fin 248) (Fin 248) ℤ :=
  1 + positiveLinear i + positiveQuadratic i

def negativeInteger (i : Fin 6) : Matrix (Fin 248) (Fin 248) ℤ :=
  fun r c => positiveInteger i (flipIndex r) (flipIndex c)

/-- Positive then negative at each of the six native simple nodes. -/
def integerGenerator : Fin 12 → Matrix (Fin 248) (Fin 248) ℤ :=
  ![positiveInteger 0, negativeInteger 0, positiveInteger 1, negativeInteger 1,
    positiveInteger 2, negativeInteger 2, positiveInteger 3, negativeInteger 3,
    positiveInteger 4, negativeInteger 4, positiveInteger 5, negativeInteger 5]

noncomputable section
open scoped Classical
local instance : InvolutiveNeg typeE8Roots := typeE8RootPairing.indexNeg
local instance : Fintype typeE8Roots := Fintype.ofFinite _

private def flip : Basis → Basis
  | .inl i => .inl i
  | .inr r => .inr (-r)

private theorem flip_involutive : Function.Involutive flip := by
  rintro (i | r)
  · rfl
  · change Sum.inr (-(-r)) = Sum.inr r
    rw [neg_neg]

private theorem root_negation (r : Fin 240) : root (negation r) = -root r := by
  apply typeE8RootPairing.root.injective
  rw [RootPairing.indexNeg_neg, typeE8RootPairing.root_reflectionPerm,
    typeE8RootPairing.reflection_apply_self]
  funext q
  have hc : ∀ r : Fin 240, coord (negation r) = -coord r := by decide +kernel
  have h := congrFun (hc r) q
  change (coord (negation r) q : ℝ) / 2 = -((coord r q : ℝ) / 2)
  change coord (negation r) q = -coord r q at h
  rw [h, Int.cast_neg]
  ring

private theorem basis_flip (r : Fin 248) : basisEquiv (flipIndex r) = flip (basisEquiv r) := by
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective r
  rcases r with i | r
  · simp [basisEquiv, flipIndex, flip]
  · simpa only [basisEquiv, flipIndex, Equiv.trans_apply, Equiv.symm_apply_apply,
      Sum.map_inr, Equiv.sumCongr_apply, flip, rootEquiv, Equiv.coe_ofBijective]
      using congrArg Sum.inr (root_negation r)

private theorem omega_entry (r c : Basis) :
    omegaMatrix (b := typeE8RootPairing_base) r c = if flip r = c then (1 : ℤ) else 0 := by
  rcases r with r | r <;> rcases c with c | c
  · simp [omegaMatrix, flip, Matrix.one_apply]
  · simp [omegaMatrix, flip]
  · simp [omegaMatrix, flip]
  · have h : flip (Sum.inr r) = Sum.inr c ↔ r = -c := by
      simp only [flip, Sum.inr.injEq, neg_eq_iff_eq_neg]
    simp only [omegaMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, h]

private theorem omega_left (A : Matrix Basis Basis ℤ) (r c : Basis) :
    (omegaMatrix (b := typeE8RootPairing_base) * A) r c = A (flip r) c := by
  simp [Matrix.mul_apply, omega_entry]

private theorem omega_right (A : Matrix Basis Basis ℤ) (r c : Basis) :
    (A * omegaMatrix (b := typeE8RootPairing_base)) r c = A r (flip c) := by
  have h (k : Basis) : flip k = c ↔ k = flip c := by
    constructor
    · intro h; simpa only [flip_involutive k] using congrArg flip h
    · rintro rfl; exact flip_involutive c
  simp [Matrix.mul_apply, omega_entry, h]

private theorem fDividedPower_flip (i : typeE8RootPairing_base.support) (n : ℕ) (r c : Basis) :
    fDividedPower i n r c = eDividedPower i n (flip r) (flip c) := by
  rw [fDividedPower, omega_right, omega_left]

private theorem negativeMatrix_flip {S : Type*} [CommRing S]
    (i : typeE8RootPairing_base.support) (t : S) (r c : Basis) :
    negativeMatrix i t r c = positiveMatrix i t (flip r) (flip c) := by
  simp only [positiveMatrix_formula, negativeMatrix_formula, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, fDividedPower_flip,
    Matrix.one_apply, flip_involutive.injective.eq_iff]

variable {S : Type*} [CommRing S]

/-- Every positive simple curve is the scalar extension of the displayed integer table. -/
theorem positive_one (i : Fin 6) :
    reindex (positiveMatrix (typeE8RootPairing_baseEquiv (node i)) (1 : S)) =
      (positiveInteger i).map (Int.castRingHom S) := by
  rw [positiveMatrix_formula]
  simp only [map_add, map_one, reindex_map, eDividedPower_one,
    positiveLinear_eq, positiveQuadratic_eq, positiveCubic_eq_zero,
    one_pow, one_smul]
  ext r c
  simp [positiveInteger, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]

/-- Root negation gives every negative simple curve in the same native basis. -/
theorem negative_one (i : Fin 6) :
    reindex (negativeMatrix (typeE8RootPairing_baseEquiv (node i)) (1 : S)) =
      (negativeInteger i).map (Int.castRingHom S) := by
  ext r c
  rw [reindex_apply, negativeMatrix_flip, ← basis_flip, ← basis_flip]
  change reindex (positiveMatrix (typeE8RootPairing_baseEquiv (node i)) (1 : S))
      (flipIndex r) (flipIndex c) = _
  rw [positive_one]
  rfl

end
end Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Curves
