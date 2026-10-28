module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Geometry.Integral
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts

/-!
# Specializing the integral complementary-root calculation

The coordinate equivalence retains all 28 Geck coordinates. The sparse
certificates specialize along ℤ → F, so both signs and quadratic terms are
preserved in every characteristic. Pinning then identifies the Weyl word and
its scalar square with the literal maps used by the centralizer construction.

Sources: GLS3 §§2.4, 2.6; Aschbacher–Smith A.2.17, printed p.39.
-/
@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
namespace Triality.Standard.OddFundamentalCentralizer.Geometry
open Parabolics Parabolics.RankOneMatrices Integral

local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

def coordinateEquiv : Ix ≃ LatticeIndex :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEnumeration)

def orderedEquiv (i : Fin 4) : FlatIndex ≃ Ix :=
  (Equiv.sumCongr (Equiv.refl _) (rootOrder i)).trans finSumFinEquiv

lemma orderedEquiv_apply (i : Fin 4) (r : FlatIndex) :
    orderedEquiv i r = orderedIndex i r := by
  cases r <;> rfl

lemma coordinateEquiv_orderedIndex (i : Fin 4) (r : FlatIndex) :
    coordinateEquiv (orderedIndex i r) = flatEquiv i r := by
  rw [← orderedEquiv_apply]
  cases r <;> simp [coordinateEquiv, orderedEquiv, flatEquiv]

variable {F : Type*} [CommRing F]

def specialize : Matrix Ix Ix ℤ →+* Matrix Ix Ix F := (Int.castRingHom F).mapMatrix

def curve (i : Fin 4) (b : Bool) (t : F) : Matrix Ix Ix F :=
  1 + t • specialize (matrix (linear i b)) + t ^ 2 • specialize (matrix (quadratic i b))

def highestCurve (b : Bool) (t : F) : Matrix Ix Ix F :=
  1 + t • specialize (matrix (highestLinear b)) +
    t ^ 2 • specialize (matrix (highestQuadratic b))

lemma highest_curve (b : Bool) (t : F) :
    specialize (matrix Integral.highestWeyl) * curve 1 b t =
      highestCurve b t * specialize (matrix Integral.highestWeyl) := by
  have h₁ := congrArg (specialize (F := F)) (highest_linear b)
  have h₂ := congrArg (specialize (F := F)) (highest_quadratic b)
  simp only [map_mul] at h₁ h₂
  simp only [curve, highestCurve, mul_add, add_mul, mul_one, one_mul,
    Matrix.mul_smul, Matrix.smul_mul, h₁, h₂]

lemma highest_curve_commute (i : Fin 4) (hi : i ≠ 1) (b c : Bool) (t u : F) :
    Commute (highestCurve b t) (curve i c u) := by
  have h (d e : Bool) := (highest_coefficient_commute i hi b c d e).map
    (specialize (F := F))
  have hll := h true true
  have hlq := h true false
  have hql := h false true
  have hqq := h false false
  change Commute (specialize (matrix (highestLinear b))) (specialize (matrix (linear i c))) at hll
  change Commute (specialize (matrix (highestLinear b))) (specialize (matrix (quadratic i c))) at hlq
  change Commute (specialize (matrix (highestQuadratic b))) (specialize (matrix (linear i c))) at hql
  change Commute (specialize (matrix (highestQuadratic b))) (specialize (matrix (quadratic i c))) at hqq
  exact ((Commute.one_left _).add_left
    ((Commute.one_right _).add_right ((hll.smul_left t).smul_right u) |>.add_right
      ((hlq.smul_left t).smul_right (u ^ 2)))).add_left
      (((Commute.one_right _).add_right ((hql.smul_left (t ^ 2)).smul_right u)).add_right
        ((hqq.smul_left (t ^ 2)).smul_right (u ^ 2)))

/-- Faithful coordinates on the actual split group, without any quotient. -/
def matrixHom (P : Parameters) : SplitGroup P →* Matrix Ix Ix (ExtensionField P) :=
  (Matrix.reindexRingEquiv (ExtensionField P) coordinateEquiv.symm).toMonoidHom.comp
    ((Units.coeHom _).comp (Subgroup.subtype _))

lemma matrixHom_injective (P : Parameters) : Function.Injective (matrixHom P) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.reindexRingEquiv (ExtensionField P) coordinateEquiv.symm).injective h

lemma matrixHom_positive (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    matrixHom P (positiveRoot P i t) = curve i true t := by
  ext r s
  obtain ⟨r, rfl⟩ := (orderedEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (orderedEquiv i).surjective s
  rw [orderedEquiv_apply, orderedEquiv_apply]
  change positiveMatrix (typeDRootPairing_baseEquiv 2 i) t
    (coordinateEquiv (orderedIndex i r)) (coordinateEquiv (orderedIndex i s)) = _
  rw [coordinateEquiv_orderedIndex, coordinateEquiv_orderedIndex, positiveMatrix_entry]
  have hinj : orderedIndex i r = orderedIndex i s ↔ r = s := by
    simpa only [orderedEquiv_apply] using (orderedEquiv i).injective.eq_iff
  simp only [curve, Matrix.add_apply, Matrix.one_apply, hinj, Matrix.smul_apply,
    smul_eq_mul, specialize, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, linear_entry, quadratic_entry, ↓reduceIte]
  split_ifs <;> simp

lemma matrixHom_negative (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    matrixHom P (negativeRoot P i t) = curve i false t := by
  ext r s
  obtain ⟨r, rfl⟩ := (orderedEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (orderedEquiv i).surjective s
  rw [orderedEquiv_apply, orderedEquiv_apply]
  change negativeMatrix (typeDRootPairing_baseEquiv 2 i) t
    (coordinateEquiv (orderedIndex i r)) (coordinateEquiv (orderedIndex i s)) = _
  rw [coordinateEquiv_orderedIndex, coordinateEquiv_orderedIndex, negativeMatrix_entry]
  have hinj : orderedIndex i r = orderedIndex i s ↔ r = s := by
    simpa only [orderedEquiv_apply] using (orderedEquiv i).injective.eq_iff
  simp only [curve, Matrix.add_apply, Matrix.one_apply, hinj, Matrix.smul_apply,
    smul_eq_mul, specialize, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, linear_entry, quadratic_entry, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> simp

lemma curve_one (i : Fin 4) : curve (F := F) i true 1 = specialize (matrix (upperOne i)) := by
  rw [upperOne_eq]
  simp [curve]

lemma curve_neg_one (i : Fin 4) :
    curve (F := F) i false (-1) = specialize (matrix (lowerMinusOne i)) := by
  rw [lowerMinusOne_eq]
  simp [curve, sub_eq_add_neg]

variable {P : Parameters} (D : PinnedRankOneMaps P)

lemma matrixHom_weyl (i : Fin 4) :
    matrixHom P (D.hom i (weylMatrix _)) = specialize (matrix (weyl i)) := by
  simp only [weylMatrix, map_mul, D.positive, D.negative,
    matrixHom_positive, matrixHom_negative, curve_one, curve_neg_one]
  rw [← map_mul, ← map_mul, weylMiddle_eq, weyl_eq]

lemma map_weyl {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    SpecialLinearGroup.map f (weylMatrix K) = weylMatrix L := by
  have h {i j : Fin 2} (hij : i ≠ j) (t : K) :
      SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij (f t) := by
    ext r s
    simp [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe,
      Matrix.map_apply, Matrix.single_apply, Matrix.one_apply]
    split_ifs <;> simp
  simp only [weylMatrix, map_mul, h, map_one, map_neg]

lemma weyl_square {K : Type*} [Field K] : weylMatrix K * weylMatrix K = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

lemma matrixHom_scalar (i : Fin 4) :
    matrixHom P (D.hom i (-1)) = specialize (matrix (scalar i)) := by
  rw [← weyl_square, map_mul, map_mul, matrixHom_weyl, ← map_mul, weyl_sq]

lemma matrixHom_highest (C : ArmRootCommutation P) :
    matrixHom P (splitHighestWeyl D C) = specialize (matrix Integral.highestWeyl) := by
  have hb : sl2BaseEmbedding P (weylMatrix _) = weylMatrix _ := map_weyl _
  have hf : sl2Frobenius P (weylMatrix _) = weylMatrix _ := map_weyl _
  change matrixHom P (D.hom 1 (sl2BaseEmbedding P (weylMatrix _)) *
    (D.hom 0 (weylMatrix _) * D.hom 2 (sl2Frobenius P (weylMatrix _)) *
      D.hom 3 (sl2Frobenius P (sl2Frobenius P (weylMatrix _))))) = _
  simp only [hb, hf]
  simp only [map_mul, matrixHom_weyl]
  rw [← map_mul, ← map_mul, ← map_mul]
  rw [← mul_assoc, ← mul_assoc, prefixTwo_eq, prefixThree_eq, highestWeyl_eq]

end Triality.Standard.OddFundamentalCentralizer.Geometry
