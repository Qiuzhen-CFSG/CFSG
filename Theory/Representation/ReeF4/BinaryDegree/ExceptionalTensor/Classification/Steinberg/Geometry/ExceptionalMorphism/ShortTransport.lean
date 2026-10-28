module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.AdjointData
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Cartan
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher

/-!
# Adjoint transport over characteristic-two base rings

The fixed integral root operators and simple Cartan commutators intertwine
all matrices in the actual root-generated F4 group, over any commutative
ring of characteristic two. In particular they give the short-ideal
transport needed for exceptional word descent over an algebraic closure.

The positive-simple identity is polynomial in its parameter. Its matrix
coefficients are specializations of integral matrices. The established
coefficient identities over `CoefficientField 0` therefore imply equality
modulo two of each integral entry, and hence the same coefficient identities
over every characteristic-two ring. This transfers individual coefficients,
not polynomial identities inferred from their values on the two-element field.
Opposition gives the negative simple curves; the actual integral Tits routes
and subgroup generation then give all group elements.

The polynomial expansion follows `AdjointEquivariance.PositiveSimple.Coefficients`;
the root and Cartan coefficients use the existing Geck construction without
changing any operator. This supplies the adjoint-transport ingredient for
Steinberg, *Lectures on Chevalley Groups*, Theorem 28
(`refs/KGroup/GLS3/Chapter2St1.tex`) and GLS3, Theorem 1.15.4(b)
(`refs/KGroup/GLS3/Chapter1.tex`). The exceptional morphism and its regularity
are assembled separately.
-/

public section
open scoped Classical Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.WordRelations ReeF4.WordRelations.Faithfulness
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
noncomputable section
variable {K : Type*} [CommRing K]

/-- The actual integral positive divided power after specialization. -/
private def dividedPower (i : typeF4RootPairing_base.support) (n : ℕ) :
    Matrix Coordinate Coordinate K :=
  (eDividedPower (P := typeF4RootPairing) i n).map (Int.castRingHom K)

private lemma cubic_product {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (A U V W E B C : Matrix n n K) (t : K)
    (h1 : U + A * E = E * A)
    (h2 : V + U * E + A * B = B * A)
    (h3 : W + V * E + U * B + A * C = C * A)
    (h4 : W * E + V * B + U * C = 0)
    (h5 : W * B + V * C = 0)
    (h6 : W * C = 0) :
    (A + t • U + t ^ 2 • V + t ^ 3 • W) *
        (1 + t • E + t ^ 2 • B + t ^ 3 • C) =
      (1 + t • E + t ^ 2 • B + t ^ 3 • C) * A := by
  calc
    _ = A + t • (U + A * E) +
        t ^ 2 • (V + U * E + A * B) +
        t ^ 3 • (W + V * E + U * B + A * C) +
        t ^ 4 • (W * E + V * B + U * C) +
        t ^ 5 • (W * B + V * C) + t ^ 6 • (W * C) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        mul_one]
      module
    _ = _ := by
      rw [h1, h2, h3, h4, h5, h6]
      simp only [Matrix.add_mul, Matrix.smul_mul, one_mul, smul_zero, add_zero]

private lemma dividedPower_zero (i : typeF4RootPairing_base.support) :
    dividedPower (K := K) i 0 = 1 := by simp [dividedPower]

private lemma dividedPower_eq_zero (i : typeF4RootPairing_base.support)
    (n : ℕ) (hn : 4 ≤ n) : dividedPower (K := K) i n = 0 := by
  simp [dividedPower, eDividedPower_eq_zero_of_four_le i hn]

/-- The F4 root-length bound kills the cubic divided power already integrally. -/
private lemma dividedPower_three_eq_zero (i : typeF4RootPairing_base.support) :
    dividedPower (K := K) i 3 = 0 := by
  simp [dividedPower, ReeF4.WordRelations.eDividedPower_three]

/-- Apply the fixed adjoint map to a column of a divided power. -/
private def columnImage (i : typeF4RootPairing_base.support) (n : ℕ) (j : Coordinate) :
    Matrix Coordinate Coordinate K :=
  adjointMap (fun k => dividedPower (K := K) i n k j)

private lemma columnImage_three_eq_zero (i : typeF4RootPairing_base.support)
    (j : Coordinate) : columnImage (K := K) i 3 j = 0 := by
  rw [columnImage, dividedPower_three_eq_zero]
  exact map_zero _

/-- Coefficients of `D(X(t) e_j) X(t)`, expanded in increasing degree. -/
private def curveProductCoefficient (i : typeF4RootPairing_base.support)
    (j : Coordinate) : ℕ → Matrix Coordinate Coordinate K
  | 0 => coordinateOperator j
  | 1 => columnImage (K := K) i 1 j + coordinateOperator j * dividedPower (K := K) i 1
  | 2 => columnImage (K := K) i 2 j + columnImage (K := K) i 1 j * dividedPower (K := K) i 1 +
      coordinateOperator j * dividedPower (K := K) i 2
  | 3 => columnImage (K := K) i 3 j + columnImage (K := K) i 2 j * dividedPower (K := K) i 1 +
      columnImage (K := K) i 1 j * dividedPower (K := K) i 2 + coordinateOperator j * dividedPower (K := K) i 3
  | 4 => columnImage (K := K) i 3 j * dividedPower (K := K) i 1 +
      columnImage (K := K) i 2 j * dividedPower (K := K) i 2 + columnImage (K := K) i 1 j * dividedPower (K := K) i 3
  | 5 => columnImage (K := K) i 3 j * dividedPower (K := K) i 2 + columnImage (K := K) i 2 j * dividedPower (K := K) i 3
  | 6 => columnImage (K := K) i 3 j * dividedPower (K := K) i 3
  | _ => 0

/-- Equality of the degree-`d` coefficients in the required adjoint identity. -/
private def CoefficientIdentity (i : typeF4RootPairing_base.support)
    (j : Coordinate) (d : ℕ) : Prop :=
  curveProductCoefficient (K := K) i j d = dividedPower (K := K) i d * coordinateOperator j

private lemma adjointMap_positive_column (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : K) :
    adjointMap (positiveMatrix i t *ᵥ Pi.single j 1) =
      coordinateOperator j + t • columnImage (K := K) i 1 j +
        t ^ 2 • columnImage (K := K) i 2 j + t ^ 3 • columnImage (K := K) i 3 j := by
  rw [positiveMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    map_add, map_smul, adjointMap_single]
  simp only [Matrix.mulVec_single_one]
  rfl

/-- The six explicit coefficient identities imply equivariance on a coordinate. -/
private lemma basis_of_coefficients (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : K)
    (hc : ∀ d, 1 ≤ d → d ≤ 6 → CoefficientIdentity (K := K) i j d) :
    adjointMap (positiveMatrix i t *ᵥ Pi.single j 1) * positiveMatrix i t =
      positiveMatrix i t * adjointMap (Pi.single j 1) := by
  have h1 := hc 1 (by omega) (by omega)
  have h2 := hc 2 (by omega) (by omega)
  have h3 := hc 3 (by omega) (by omega)
  have h4 := hc 4 (by omega) (by omega)
  have h5 := hc 5 (by omega) (by omega)
  have h6 := hc 6 (by omega) (by omega)
  have hz4 := dividedPower_eq_zero (K := K) i 4 (by omega)
  have hz5 := dividedPower_eq_zero (K := K) i 5 (by omega)
  have hz6 := dividedPower_eq_zero (K := K) i 6 (by omega)
  simp only [CoefficientIdentity, curveProductCoefficient] at h1 h2 h3
  simp only [CoefficientIdentity, curveProductCoefficient, hz4, zero_mul] at h4
  simp only [CoefficientIdentity, curveProductCoefficient, hz5, zero_mul] at h5
  simp only [CoefficientIdentity, curveProductCoefficient, hz6, zero_mul] at h6
  rw [adjointMap_positive_column, adjointMap_single, positiveMatrix_formula]
  exact cubic_product _ _ _ _ _ _ _ t h1 h2 h3 h4 h5 h6

/-- With the F4 cubic term zero, four coefficient identities suffice. -/
private lemma basis_of_quadratic_coefficients (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : K)
    (hc : ∀ d, 1 ≤ d → d ≤ 4 → CoefficientIdentity (K := K) i j d) :
    adjointMap (positiveMatrix i t *ᵥ Pi.single j 1) * positiveMatrix i t =
      positiveMatrix i t * adjointMap (Pi.single j 1) := by
  apply basis_of_coefficients i j t
  intro d hd1 hd6
  by_cases hd4 : d ≤ 4
  · exact hc d hd1 hd4
  · have hz := dividedPower_eq_zero (K := K) i d (by omega)
    unfold CoefficientIdentity
    rw [hz, zero_mul]
    interval_cases d <;>
      simp [curveProductCoefficient, columnImage_three_eq_zero, dividedPower_three_eq_zero]


private lemma coordinateOperator_cast (j : Coordinate) :
    (coordinateOperator (K := ℤ) j).map (Int.castRingHom K) = coordinateOperator j := by
  have hcast (A : Matrix Coordinate Coordinate ℤ) :
      (A.map (Int.castRingHom ℤ)).map (Int.castRingHom K) = A.map (Int.castRingHom K) := by
    ext x y
    simp
  cases j <;> simp only [coordinateOperator, Matrix.map_mul, Matrix.map_sub _ (map_sub _), hcast]

private lemma adjointMap_cast (v : Coordinate → ℤ) :
    (adjointMap v).map (Int.castRingHom K) = adjointMap (fun j => (v j : K)) := by
  ext x y
  change ((∑ j, v j • coordinateOperator (K := ℤ) j) x y : K) =
    (∑ j, (v j : K) • coordinateOperator j) x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (congrFun (coordinateOperator_cast (K := K) j) x) y

private lemma dividedPower_cast (i : typeF4RootPairing_base.support) (d : ℕ) :
    (dividedPower (K := ℤ) i d).map (Int.castRingHom K) = dividedPower (K := K) i d := by
  simp [dividedPower]

private lemma columnImage_cast (i : typeF4RootPairing_base.support) (d : ℕ) (j : Coordinate) :
    (columnImage (K := ℤ) i d j).map (Int.castRingHom K) = columnImage (K := K) i d j := by
  rw [columnImage, adjointMap_cast]
  exact congrArg adjointMap (congrArg (fun A : Matrix Coordinate Coordinate K => fun k => A k j)
    (dividedPower_cast i d))

private lemma curveProductCoefficient_cast (i : typeF4RootPairing_base.support)
    (j : Coordinate) (d : ℕ) :
    (curveProductCoefficient (K := ℤ) i j d).map (Int.castRingHom K) =
      curveProductCoefficient (K := K) i j d := by
  rcases d with _ | _ | _ | _ | _ | _ | _ | d <;>
    simp only [curveProductCoefficient, Matrix.map_add _ (map_add _), Matrix.map_mul,
      coordinateOperator_cast, columnImage_cast, dividedPower_cast, Matrix.map_zero _ (map_zero _)]

private lemma cast_matrix_eq [CharP K 2] (A B : Matrix Coordinate Coordinate ℤ)
    (h : A.map (Int.castRingHom (CoefficientField 0)) =
      B.map (Int.castRingHom (CoefficientField 0))) :
    A.map (Int.castRingHom K) = B.map (Int.castRingHom K) := by
  ext i j
  exact (CharP.intCast_eq_intCast K 2).mpr
    ((CharP.intCast_eq_intCast (CoefficientField 0) 2).mp (congrFun (congrFun h i) j))

private lemma coefficientIdentity_cast [CharP K 2] (i : typeF4RootPairing_base.support)
    (j : Coordinate) (d : ℕ)
    (h : Adjoint.PositiveSimple.CoefficientIdentity 0 i j d) : CoefficientIdentity (K := K) i j d := by
  unfold CoefficientIdentity
  rw [← curveProductCoefficient_cast, ← dividedPower_cast, ← coordinateOperator_cast,
    ← Matrix.map_mul]
  apply cast_matrix_eq
  simp only [curveProductCoefficient_cast, Matrix.map_mul, dividedPower_cast,
    coordinateOperator_cast]
  change curveProductCoefficient (K := CoefficientField 0) i j d =
    dividedPower i d * coordinateOperator j at h
  exact h

private lemma coefficients [CharP K 2] (i : typeF4RootPairing_base.support)
    (j : Coordinate) (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    CoefficientIdentity (K := K) i j d := by
  apply coefficientIdentity_cast
  have h1 := Adjoint.PositiveSimple.positive_root_coefficient_one 0 i
  have h24 := Adjoint.PositiveSimple.positive_root_coefficients_two_four 0 i h1
  rcases j with j | r
  · exact Adjoint.PositiveSimple.coefficientIdentity_cartan 0 i j d hd1 hd4
  · interval_cases d
    · exact h1 r
    · exact h24.1 r
    · apply Adjoint.PositiveSimple.coefficientIdentity_three_of_one_two 0 i (Sum.inr r)
        (h1 r)
      rintro (j | s)
      · exact Adjoint.PositiveSimple.coefficientIdentity_cartan 0 i j 2 (by omega) (by omega)
      · exact h24.1 s
    · exact h24.2 r

private lemma positive_equivariant [CharP K 2] (i : typeF4RootPairing_base.support) (t : K) :
    Equivariant adjointMap (positiveUnit i t) := by
  apply (Adjoint.equivariant_iff_basis adjointMap _).mpr
  intro j
  exact basis_of_quadratic_coefficients i j t (coefficients i j)

private lemma omega_equivariant [CharP K 2] :
    Equivariant (adjointMap (K := K)) Adjoint.omegaUnit := by
  apply (Adjoint.equivariant_iff_basis adjointMap _).mpr
  rintro (i | r)
  · rw [Adjoint.omegaUnit_mulVec_cartan, adjointMap_single]
    let O : Matrix Coordinate Coordinate K := Adjoint.omegaUnit (K := K)
    let E := (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K)
    let F := (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K)
    have hE : O * E = F * O := Adjoint.omegaUnit_mul_eMatrix i
    have hF : O * F = E * O := Adjoint.omegaUnit_mul_fMatrix i
    change (E * F - F * E) * O = O * (E * F - F * E)
    rw [Matrix.mul_sub, ← mul_assoc, ← mul_assoc, hE, hF]
    rw [mul_assoc F, mul_assoc E, hF, hE, Matrix.sub_mul]
    ext x y
    simp only [Matrix.sub_apply, CharTwo.sub_eq_add, mul_assoc, add_comm]
  · let := typeF4RootPairing.indexNeg
    rw [Adjoint.omegaUnit_mulVec_root, adjointMap_root_single, adjointMap_root_single]
    rw [← Adjoint.omegaUnit_conj_rootOperator]
    simp only [mul_assoc, Adjoint.omegaUnit_mul_self, mul_one]

private lemma negative_equivariant [CharP K 2] (i : typeF4RootPairing_base.support) (t : K) :
    Equivariant adjointMap (negativeUnit i t) := by
  rw [Adjoint.negativeUnit_eq_omega_conjugate]
  exact Adjoint.equivariant_conjugate adjointMap _ _ omega_equivariant
    (positive_equivariant i t)

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The fixed integral adjoint map intertwines every actual generated F4 matrix. -/
theorem adjointMap_equivariant
    (g : (Matrix Coordinate Coordinate K)ˣ) (hg : g ∈ matrixGroup K) :
    Equivariant adjointMap g := by
  apply equivariant_closure adjointMap _ _ hg
  rintro _ ⟨⟨r, t⟩, rfl⟩
  exact Adjoint.rootCurve_equivariant_of_simple adjointMap
    ShortTransport.positive_equivariant ShortTransport.negative_equivariant r t

/-- Unconditional adjoint transport on the actual short-coordinate ideal,
including over every algebraic closure of a characteristic-two field. -/
theorem hasShortAdjointTransport : HasShortAdjointTransport K := by
  intro g hg v _
  exact adjointMap_equivariant g hg v

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
