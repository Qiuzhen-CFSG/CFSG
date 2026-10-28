module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.DiagonalTorus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Grading

/-!
# Complementary parabolic gradings in the split Ree construction

The sums of the simple-root coefficients outside the two Levi pairs give
nonnegative degrees to their respective seed roots. Homogeneity of the
integral divided powers makes the seed matrices weakly triangular in these
degrees; diagonal torus matrices preserve both degrees. Their sum is total
root height. Thus membership in both parabolics forces height triangularity.

This is a matrix-support calculation for every coefficient field, including
`m = 0`. Recognizing a triangular split matrix as a Borel element is a separate
Bruhat step. The gradings extend the calculation in
`LocalBlockInput/OuterOddSubgroups/PairRigidity/BlockGeometry/ParabolicRecognition/RootIntersection.lean`
without changing that module or its public boundary.

Source: the Chevalley parabolic construction underlying Aschbacher–Smith
F.1.4–5 and F.1.12(I)(5), printed pp.260,263–264 of `refs/quasithin.pdf`;
GLS3 2.3.6–8, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
namespace ReeF4.Parabolics.Overlap
open LargeLocalSeeds
noncomputable section
open scoped Classical
private local instance parabolicGradingIndexNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg
private def gradingCoefficients : Side → Fin 4 → ℤ
  | .linear => ![7, 14, 10, 5]
  | .suzuki => ![4, 7, 5, 3]
private def rootDegree (s : Side) (r : F4Chevalley.Root) : ℤ :=
  gradingCoefficients s 0 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  gradingCoefficients s 1 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  gradingCoefficients s 2 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  gradingCoefficients s 3 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)
private theorem rootDegree_simple (s : Side) (i : Fin 4) :
    rootDegree s (typeF4SimpleRootIndex i) = if i ∈ leviNodes s then 0 else 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootDegree, hp]
  cases s <;> fin_cases i <;>
    norm_num [gradingCoefficients, leviNodes, typeF4CartanMatrix, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three]
private theorem rootDegree_neg (s : Side) (r : F4Chevalley.Root) :
    rootDegree s (-r) = -rootDegree s r := by
  simp only [rootDegree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring
private theorem rootDegree_add (s : Side) {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    rootDegree s k = rootDegree s i + rootDegree s j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [rootDegree, hp]
  ring
private theorem rootDegree_pos_nonneg (s : Side) {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 ≤ rootDegree s r := by
  have hs (i : F4Chevalley.Root) (hi : i ∈ typeF4RootPairing_base.support) :
      0 ≤ rootDegree s i := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, rootDegree_simple]
    split_ifs <;> omega
  apply hr.induction_on_add hs
  intro i j k hk hi hj
  rw [rootDegree_add s hk]
  exact add_nonneg hi (hs j hj)
private theorem rootDegree_seed_nonneg (s : Side) {r : F4Chevalley.Root}
    (hr : IsSeedRoot s r) : 0 ≤ rootDegree s r := by
  rcases hr with hr | ⟨i, hi, rfl⟩
  · exact rootDegree_pos_nonneg s hr
  · rw [rootDegree_neg, rootDegree_simple, if_pos hi]
    omega

private def basisDegree (s : Side) (a : F4Chevalley.BasisIndex) : ℤ :=
  gradingCoefficients s 0 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  gradingCoefficients s 1 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  gradingCoefficients s 2 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  gradingCoefficients s 3 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (s : Side) (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree s i - basisDegree s j = (n : ℤ) * rootDegree s r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination gradingCoefficients s 0 * h0 + gradingCoefficients s 1 * h1 +
    gradingCoefficients s 2 * h2 + gradingCoefficients s 3 * h3

private def Triangular {m : ℕ} (w : F4Chevalley.BasisIndex → ℤ)
    (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField m)) : Prop :=
  ∀ i j, w i < w j → A i j = 0

private theorem triangular_one {m : ℕ} (w : F4Chevalley.BasisIndex → ℤ) :
    Triangular (m := m) w 1 := by
  intro i j hij
  exact Matrix.one_apply_ne (fun h => (ne_of_lt hij) (congrArg w h))
private theorem triangular_mul {m : ℕ} {w : F4Chevalley.BasisIndex → ℤ}
    {A B : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField m)}
    (hA : Triangular w A) (hB : Triangular w B) : Triangular w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i < w k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]
private theorem triangular_inv {m : ℕ} {w : F4Chevalley.BasisIndex → ℤ}
    {x : SplitGroup m} (hx : Triangular w x.val.val) : Triangular w x⁻¹.val.val := by
  have hp (n : ℕ) : Triangular w (x ^ n).val.val := by
    induction n with
    | zero => simpa using triangular_one w
    | succ n ih => simpa only [pow_succ, Subgroup.coe_mul, Units.val_mul] using triangular_mul ih hx
  have he : x⁻¹ = x ^ (orderOf x - 1) := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [he]
  exact hp _
private def triangularSubgroup (m : ℕ) (w : F4Chevalley.BasisIndex → ℤ) :
    Subgroup (SplitGroup m) where
  carrier := {x | Triangular w x.val.val}
  one_mem' := triangular_one w
  mul_mem' := triangular_mul
  inv_mem' := triangular_inv

private theorem rootCurve_triangular (m : ℕ) (s : Side) (r : F4Chevalley.Root)
    (hr : 0 ≤ rootDegree s r) (t : CoefficientField m) :
    Triangular (basisDegree s) (F4Chevalley.rootCurve r t).val := by
  intro i j hij
  have hn : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
  have hz (n : ℕ) : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
    by_contra hne
    have hd := dividedPower_degree s r n i j hne
    have hp := mul_nonneg (Nat.cast_nonneg (α := ℤ) n) hr
    omega
  rw [F4Chevalley.rootCurve_matrix_formula]
  simp [Matrix.add_apply, Matrix.smul_apply, specializeMatrix,
    hz 1, hz 2, hz 3, Matrix.one_apply_ne hn]

private theorem splitSeed_triangular (m : ℕ) (s : Side) :
    splitSeed m s ≤ triangularSubgroup m (basisDegree s) := by
  apply (closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  exact rootCurve_triangular m s r (rootDegree_seed_nonneg s hr) t
private theorem diagonalTorus_triangular (m : ℕ) (s : Side) :
    diagonalTorus m ≤ triangularSubgroup m (basisDegree s) := by
  intro x hx
  change x.val ∈ (diagonalTorusHom m).range at hx
  obtain ⟨u, hu⟩ := hx
  change Triangular (basisDegree s) x.val.val
  rw [← hu]
  change Triangular (basisDegree s) (Matrix.diagonal _)
  intro i j hij
  exact Matrix.diagonal_apply_ne _ (fun h => (ne_of_lt hij) (congrArg (basisDegree s) h))

open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry

/-- Weak height triangularity, with the actual Cartan-plus-root basis and coefficient field. -/
@[expose] def IsHeightTriangular {m : ℕ} (x : SplitGroup m) : Prop :=
  ∀ i j, LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.basisDegree i <
    LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.basisDegree j →
      x.val.val i j = 0

/-- Products preserve weak height triangularity. -/
theorem IsHeightTriangular.mul {m : ℕ} {x y : SplitGroup m}
    (hx : IsHeightTriangular x) (hy : IsHeightTriangular y) :
    IsHeightTriangular (x * y) :=
  triangular_mul hx hy

/-- Inversion preserves weak height triangularity in the finite split carrier. -/
theorem IsHeightTriangular.inv {m : ℕ} {x : SplitGroup m}
    (hx : IsHeightTriangular x) : IsHeightTriangular x⁻¹ :=
  triangular_inv hx

private theorem basisDegree_add (a : F4Chevalley.BasisIndex) :
    basisDegree .suzuki a + basisDegree .linear a =
      LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.basisDegree a := by
  dsimp [basisDegree, gradingCoefficients,
    LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.basisDegree]
  ring

/-- The two complementary parabolic gradings add to total root height. -/
theorem inf_splitParabolic_heightTriangular (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) {x : SplitGroup m}
    (hx : x ∈ splitParabolic m .suzuki ⊓ splitParabolic m .linear) :
    IsHeightTriangular x := by
  have hs (s : Side) : splitParabolic m s ≤ triangularSubgroup m (basisDegree s) :=
    sup_le (splitSeed_triangular m s) (hT.trans (diagonalTorus_triangular m s))
  intro i j hij
  have hi := basisDegree_add i
  have hj := basisDegree_add j
  by_cases ha : basisDegree .suzuki i < basisDegree .suzuki j
  · exact hs .suzuki hx.1 i j ha
  · exact hs .linear hx.2 i j (by omega)

/-- Positive split matrices are weakly triangular for total height. -/
theorem splitUnipotent_heightTriangular {m : ℕ} {x : SplitGroup m}
    (hx : x ∈ splitUnipotent m) : IsHeightTriangular x := by
  intro i j hij
  rw [splitUnipotent_entry hx i j (le_of_lt hij)]
  exact Matrix.one_apply_ne (fun h => (ne_of_lt hij) (congrArg _ h))

end
end ReeF4.Parabolics.Overlap
