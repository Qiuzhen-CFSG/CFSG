module
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.Grading
/-!
# A matrix quotient of the linear Ree radical

The degree-one part of a radical matrix is additive under multiplication:
every product of two strictly degree-raising matrices raises degree by at least
two. It therefore defines a homomorphism from the actual Ree radical to the
additive matrix group, and kills its actual commutator subgroup.

A full Levi matrix has degree zero. Taking degree-one parts in the commutator
equation shows that trivial action on the radical abelianization centralizes
the field span of the degree-one radical matrices. This is a quotient map;
no equality between this matrix layer and the radical abelianization is needed.

The root-curve formulas identify the contribution of each root to this quotient.
The remaining concrete inputs are spanning by fixed radical words and detection
of full Levi elements by the resulting root operators.

Source: the root-defined Levi decomposition and radical centralizer assertion
of GLS3, Theorem 2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection
open Theory.AlgebraicGroup Subgroup Parabolics LargeLocalSeeds
open RootPairing.IntegralGeckConstruction
open scoped commutatorElement
variable {m : ℕ}

/-- The homogeneous part that raises the middle-root degree by exactly one. -/
def degreeOnePart : MatrixCarrier m →ₗ[CoefficientField m] MatrixCarrier m where
  toFun A i j := if basisDegree i = basisDegree j + 1 then A i j else 0
  map_add' A B := by
    ext i j
    change (if basisDegree i = basisDegree j + 1 then A i j + B i j else 0) =
      (if basisDegree i = basisDegree j + 1 then A i j else 0) +
      (if basisDegree i = basisDegree j + 1 then B i j else 0)
    split_ifs <;> simp
  map_smul' t A := by
    ext i j
    change (if basisDegree i = basisDegree j + 1 then t * A i j else 0) =
      t * (if basisDegree i = basisDegree j + 1 then A i j else 0)
    split_ifs <;> simp

@[simp] theorem degreeOnePart_apply (A : MatrixCarrier m) (i j : F4Chevalley.BasisIndex) :
    degreeOnePart A i j = if basisDegree i = basisDegree j + 1 then A i j else 0 := rfl

@[simp] theorem degreeOnePart_one : degreeOnePart (1 : MatrixCarrier m) = 0 := by
  ext i j
  by_cases h : basisDegree i = basisDegree j + 1
  · have hij : i ≠ j := by intro he; subst j; omega
    simp [h, hij]
  · simp [h]

private theorem degreeOnePart_mul_raises {A B : MatrixCarrier m}
    (hA : Raises A) (hB : Raises B) : degreeOnePart (A * B) = 0 := by
  ext i j
  by_cases h : basisDegree i = basisDegree j + 1
  · simp only [degreeOnePart_apply, if_pos h, Matrix.zero_apply, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : basisDegree i ≤ basisDegree k
    · rw [hA i k hik, zero_mul]
    · rw [hB k j (by omega), mul_zero]
  · simp [h]

/-- The degree-one part is additive on matrices that are identity plus a
strictly degree-raising matrix. -/
theorem degreeOnePart_mul_of_raises (A B : MatrixCarrier m)
    (hA : Raises (A - 1)) (hB : Raises (B - 1)) :
    degreeOnePart (A * B) = degreeOnePart A + degreeOnePart B := by
  have he : A * B = A + B - 1 + (A - 1) * (B - 1) := by noncomm_ring
  rw [he, map_add, map_sub, map_add, degreeOnePart_one, sub_zero,
    degreeOnePart_mul_raises hA hB, add_zero]

/-- The same additive formula holds before taking Ree fixed points. -/
theorem degreeOnePart_split_mul (x y : SplitGroup m)
    (hx : x ∈ splitRadical m .linear) (hy : y ∈ splitRadical m .linear) :
    degreeOnePart (x * y).val.val =
      degreeOnePart x.val.val + degreeOnePart y.val.val :=
  degreeOnePart_mul_of_raises _ _ (splitRadical_raises x hx) (splitRadical_raises y hy)

/-- Products in the radical add their actual degree-one matrix parts. -/
theorem degreeOnePart_model_mul (x y : Model m)
    (hx : x ∈ radical m .linear) (hy : y ∈ radical m .linear) :
    degreeOnePart (modelMatrix m (x * y)) =
      degreeOnePart (modelMatrix m x) + degreeOnePart (modelMatrix m y) := by
  rw [modelMatrix_mul]
  exact degreeOnePart_mul_of_raises _ _ (radical_raises x hx) (radical_raises y hy)

/-- An additive quotient of the radical, obtained from its faithful matrices. -/
def radicalDegreeOneHom (m : ℕ) : radical m .linear →* Multiplicative (MatrixCarrier m) where
  toFun x := Multiplicative.ofAdd (degreeOnePart (modelMatrix m x.val))
  map_one' := by change degreeOnePart (modelMatrix m 1) = 0; simp
  map_mul' x y := degreeOnePart_model_mul x.val y.val x.property y.property

/-- The ambient commutator subgroup has zero degree-one part. -/
theorem degreeOnePart_commutator_radical (x : Model m)
    (hx : x ∈ ⁅radical m .linear, radical m .linear⁆) :
    degreeOnePart (modelMatrix m x) = 0 := by
  let R := radical m .linear
  have hle : ⁅R, R⁆ ≤ (radicalDegreeOneHom m).ker.map R.subtype := by
    apply commutator_le.mpr
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : R), (⟨b, hb⟩ : R)⁆, ?_, rfl⟩
    change radicalDegreeOneHom m ⁅(⟨a, ha⟩ : R), (⟨b, hb⟩ : R)⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  obtain ⟨y, hy, he⟩ := hle hx
  change degreeOnePart (modelMatrix m y.val) = 0 at hy
  change y.val = x at he
  rwa [← he]

/-- Degree-zero left multiplication commutes with taking the degree-one part. -/
theorem degreeOnePart_mul_left {A : MatrixCarrier m} (hA : PreservesDegree A)
    (B : MatrixCarrier m) : degreeOnePart (A * B) = A * degreeOnePart B := by
  ext i j
  simp only [degreeOnePart_apply, Matrix.mul_apply]
  split_ifs with hij
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hik : basisDegree i = basisDegree k
    · rw [if_pos (by omega)]
    · rw [hA i k hik, zero_mul, zero_mul]
  · symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : basisDegree i = basisDegree k
    · rw [if_neg (by omega), mul_zero]
    · rw [hA i k hik, zero_mul]

/-- Degree-zero right multiplication commutes with taking the degree-one part. -/
theorem degreeOnePart_mul_right (A : MatrixCarrier m) {B : MatrixCarrier m}
    (hB : PreservesDegree B) : degreeOnePart (A * B) = degreeOnePart A * B := by
  ext i j
  simp only [degreeOnePart_apply, Matrix.mul_apply]
  split_ifs with hij
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : basisDegree k = basisDegree j
    · rw [if_pos (by omega)]
    · rw [hB k j hkj, mul_zero, mul_zero]
  · symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkj : basisDegree k = basisDegree j
    · rw [if_neg (by omega), zero_mul]
    · rw [hB k j hkj, mul_zero]

/-- Trivial action on the true radical abelianization centralizes each
actual degree-one radical matrix. This needs only the quotient map above. -/
theorem commute_degreeOnePart_of_trivial_radical_abelianization
    (l : Model m) (hl : l ∈ fullLevi m)
    (hact : ActsTriviallyOnRadicalAbelianization m l)
    (q : Model m) (hq : q ∈ radical m .linear) :
    Commute (modelMatrix m l) (degreeOnePart (modelMatrix m q)) := by
  have hc := hact q hq
  have hcr : ⁅l, q⁆ ∈ radical m .linear := (commutator_le_self _) hc
  have he : l * q = (⁅l, q⁆ * q) * l := by simp [commutatorElement_def, mul_assoc]
  have hp := congrArg (fun x => degreeOnePart (modelMatrix m x)) he
  rw [modelMatrix_mul, degreeOnePart_mul_left (fullLevi_preservesDegree l hl),
    modelMatrix_mul, degreeOnePart_mul_right _ (fullLevi_preservesDegree l hl),
    degreeOnePart_model_mul _ _ hcr hq, degreeOnePart_commutator_radical _ hc,
    zero_add] at hp
  exact hp

/-- The field span of the degree-one matrices of actual fixed radical elements. -/
def radicalDegreeOneSpan (m : ℕ) : Submodule (CoefficientField m) (MatrixCarrier m) :=
  Submodule.span (CoefficientField m)
    {A | ∃ q ∈ radical m .linear, A = degreeOnePart (modelMatrix m q)}

/-- A Levi element acting trivially on the radical abelianization centralizes
the full field span of its degree-one matrices. -/
theorem commute_of_mem_radicalDegreeOneSpan
    (l : Model m) (hl : l ∈ fullLevi m)
    (hact : ActsTriviallyOnRadicalAbelianization m l)
    (A : MatrixCarrier m) (hA : A ∈ radicalDegreeOneSpan m) :
    Commute (modelMatrix m l) A := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨q, hq, rfl⟩ := hA
    exact commute_degreeOnePart_of_trivial_radical_abelianization l hl hact q hq
  | zero => exact Commute.zero_right _
  | add A B _ _ hA hB => exact hA.add_right hB
  | smul t A _ hA =>
    change modelMatrix m l * (t • A) = (t • A) * modelMatrix m l
    rw [Matrix.mul_smul, Matrix.smul_mul, hA.eq]

/-- The degree-one divided-power operator of a root, on the actual F₄ lattice. -/
def rootOperator (m : ℕ) (r : F4Chevalley.Root) : MatrixCarrier m :=
  specializeMatrix (S := CoefficientField m)
    (F4Chevalley.integralOperators.rootDividedPower r 1)

/-- Homogeneity determines exactly which divided powers survive projection. -/
theorem degreeOnePart_dividedPower (r : F4Chevalley.Root) (n : ℕ) :
    degreeOnePart (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) =
    if (n : ℤ) * rootDegree r = 1 then
      specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n) else 0 := by
  by_cases h : (n : ℤ) * rootDegree r = 1
  · rw [if_pos h]
    ext i j
    by_cases hij : basisDegree i = basisDegree j + 1
    · simp [hij]
    · have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
        by_contra hne
        have hd := dividedPower_degree r n i j hne
        omega
      simp [hij, specializeMatrix, hz]
  · rw [if_neg h]
    ext i j
    by_cases hij : basisDegree i = basisDegree j + 1
    · have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
        by_contra hne
        have hd := dividedPower_degree r n i j hne
        omega
      simp [hij, specializeMatrix, hz]
    · simp [hij]

/-- A degree-one root curve contributes precisely its linear root operator. -/
theorem degreeOnePart_rootGenerator (r : F4Chevalley.Root) (hr : rootDegree r = 1)
    (t : CoefficientField m) :
    degreeOnePart (rootGeneratorInGroup m r t).val.val = t • rootOperator m r := by
  change degreeOnePart (F4Chevalley.rootCurve r t).val = _
  rw [F4Chevalley.rootCurve_matrix_formula]
  simp [map_add, degreeOnePart_dividedPower, hr, rootOperator]

/-- Higher radical root curves do not contribute to the degree-one quotient. -/
theorem degreeOnePart_rootGenerator_of_one_lt (r : F4Chevalley.Root)
    (hr : 1 < rootDegree r) (t : CoefficientField m) :
    degreeOnePart (rootGeneratorInGroup m r t).val.val = 0 := by
  change degreeOnePart (F4Chevalley.rootCurve r t).val = _
  rw [F4Chevalley.rootCurve_matrix_formula]
  have h1 : (1 : ℤ) * rootDegree r ≠ 1 := by omega
  have h2 : (2 : ℤ) * rootDegree r ≠ 1 := by omega
  have h3 : (3 : ℤ) * rootDegree r ≠ 1 := by omega
  simp only [map_add, map_smul, degreeOnePart_one, degreeOnePart_dividedPower,
    Nat.cast_one, Nat.cast_ofNat, if_neg h1, if_neg h2, if_neg h3, smul_zero, add_zero]

end ReeF4.SectionGeometry.LinearRadical.LeviDetection
