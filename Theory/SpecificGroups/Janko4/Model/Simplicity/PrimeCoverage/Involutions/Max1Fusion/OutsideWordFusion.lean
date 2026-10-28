module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideSetup
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations1
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations2
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations3
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations4
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations5
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations6
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations7
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations8
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Relations9
import Mathlib.Tactic.FinCases

/-!
# Fusion of the ten outside-kernel words inside the J₄ model

Let t=(ababb)^5. The nine new certificates show that each candidate r squares
to one and that r*(w*t*w⁻¹) has an odd power equal to one (with target a for
entry 9). The elementary dihedral conjugator, followed by w⁻¹, therefore
conjugates r to its target inside `Model`. Entry 0 was already a conjugate of a.

The local generators come from the literal ATLAS J4G1-max1W1 program in
`Cardinality.Subgroup`; the candidates are precisely `OutsideSetup`'s masks
in the production binary kernel basis. This theorem proves fusion of that
finite list; coverage of outside-kernel involutions is a separate obligation.
-/

public section
namespace Janko4.Simplicity.Max1Fusion
open OutsideWordCertificates
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  outsideRepresentative

private theorem conjugate_square {G : Type*} [Group G] (w t : G) (ht : t ^ 2 = 1) :
    (w * t * w⁻¹) ^ 2 = 1 := by
  calc
    _ = w * t ^ 2 * w⁻¹ := by simp only [pow_two, mul_assoc, inv_mul_cancel_left]
    _ = 1 := by rw [ht, mul_one, mul_inv_cancel]

private theorem fuse_odd_product (z t w : Model) (n : ℕ)
    (hz : z ^ 2 = 1) (ht : t ^ 2 = 1) (hn : Odd n)
    (hp : (z * (w * t * w⁻¹)) ^ n = 1)
    (target : t = a hA ∨ t = word (a hA) (b hB) "ababb" ^ 5) :
    Fuses hA hB z := by
  have ho := hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one hp)
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (isConj_of_involutions_odd_product z (w * t * w⁻¹) hz (conjugate_square w t ht) ho)
  have he : t = (w⁻¹ * g) * z * (w⁻¹ * g)⁻¹ := by
    calc
      t = w⁻¹ * (w * t * w⁻¹) * w := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      _ = w⁻¹ * (g * z * g⁻¹) * w := by rw [hg]
      _ = (w⁻¹ * g) * z * (w⁻¹ * g)⁻¹ := by simp only [mul_inv_rev, inv_inv, mul_assoc]
  obtain ha | ht := target
  · exact ⟨w⁻¹ * g, Or.inl (ha ▸ he)⟩
  · exact ⟨w⁻¹ * g, Or.inr (ht ▸ he)⟩

/-- Every one of the ten concrete outside-kernel words is conjugate, inside
`Model`, to `a` or to `(ababb)^5`. -/
theorem outsideRepresentative_fuses (i : Fin 10) :
    Fuses hA hB (outsideRepresentative hA hB i : Model) := by
  have ha : a hA ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (primeRepresentative (a hA) (b hB) 0)
    rw [involutionRepresentative_zero_orderOf hA hB] at h
    exact h
  have ht : (word (a hA) (b hB) "ababb" ^ 5) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (primeRepresentative (a hA) (b hB) 1)
    rw [involutionRepresentative_one_orderOf hA hB] at h
    exact h
  fin_cases i
  · exact outsideRepresentative_zero_fuses hA hB
  · exact fuse_odd_product hA hB _ _ _ 43 (square_1 hA hB) ht (by decide)
      (odd_product_1 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ _ 15 (square_2 hA hB) ht (by decide)
      (odd_product_2 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ _ 43 (square_3 hA hB) ht (by decide)
      (odd_product_3 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ 1 43 (square_4 hA hB) ht (by decide)
      (by rw [one_mul, inv_one, mul_one]; exact odd_product_4 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ _ 11 (square_5 hA hB) ht (by decide)
      (odd_product_5 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ _ 29 (square_6 hA hB) ht (by decide)
      (odd_product_6 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ 1 31 (square_7 hA hB) ht (by decide)
      (by rw [one_mul, inv_one, mul_one]; exact odd_product_7 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ 1 43 (square_8 hA hB) ht (by decide)
      (by rw [one_mul, inv_one, mul_one]; exact odd_product_8 hA hB) (Or.inr rfl)
  · exact fuse_odd_product hA hB _ _ _ 11 (square_9 hA hB) ha (by decide)
      (odd_product_9 hA hB) (Or.inl rfl)

end Janko4.Simplicity.Max1Fusion
