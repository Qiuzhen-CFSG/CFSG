module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The grading for linear Ree Levi detection

The coroot combination `(7,14,10,5)` measures the sum of the two middle
simple-root coefficients. The linear radical strictly raises this grading
on the actual 52-dimensional F₄ lattice. The full end-node Levi preserves
every homogeneous summand, including the full complementary torus.

Divided-power homogeneity proves both assertions on root generators; closure
and finite-order inversion extend them to the specified matrix subgroups.
The grading calculation is adapted from `SectionGeometry/CoreFree/Opposition`;
it is repeated here to preserve that independent module's private boundary.
No identification with a radical quotient is asserted.

Source: the root-defined Levi decomposition of GLS3, Theorem 2.6.5(g),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds Parabolics
open LocalBlockInput.PairRigidity
variable {m : ℕ}

def coefficients : Fin 4 → ℤ := ![7, 14, 10, 5]

def rootDegree (r : F4Chevalley.Root) : ℤ :=
  ∑ i : Fin 4, coefficients i *
    typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)

theorem rootDegree_eq (r : F4Chevalley.Root) :
    (rootDegree r : ℝ) =
      typeF4SimpleCoefficient r.val 1 + typeF4SimpleCoefficient r.val 2 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) := by
    exact (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  simp only [rootDegree, Int.cast_sum, Int.cast_mul, hp, typeF4CorootScale_simpleRoot]
  norm_num [coefficients, Fin.sum_univ_four,
      typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector,
      Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem coefficient_nonneg {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (q : Fin 4) :
    0 ≤ typeF4SimpleCoefficient r.val q := by
  have hs (r : F4Chevalley.Root) (hr : r ∈ typeF4RootPairing_base.support) :
      0 ≤ typeF4SimpleCoefficient r.val q := by
    obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have he : typeF4SimpleRootIndex i = r := congrArg Subtype.val hi
    rw [← he]
    fin_cases i <;> fin_cases q <;>
      norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val, typeF4SimpleRoot,
        basisVector, Matrix.cons_val_two, Matrix.cons_val_three]
  apply hr.induction_on_add hs
  intro i j k hk hi hj
  have hj' := hs j hj
  have hv : k.val = i.val + j.val := hk
  have he : typeF4SimpleCoefficient k.val q =
      typeF4SimpleCoefficient i.val q + typeF4SimpleCoefficient j.val q := by
    rw [hv]
    fin_cases q <;> simp [typeF4SimpleCoefficient, Pi.add_apply] <;> ring
  rw [he]
  exact add_nonneg hi hj'

theorem rootDegree_radical {r : F4Chevalley.Root} (hr : IsRadicalRoot .linear r) :
    0 < rootDegree r := by
  have hp (i : Fin 4) := coefficient_nonneg hr.1 i
  have hreal : 0 < (rootDegree r : ℝ) := by
    rw [rootDegree_eq]
    obtain ⟨i, hi, hn⟩ := hr.2
    fin_cases i <;> simp [leviNodes] at hi
    · have := lt_of_le_of_ne (hp 1) (Ne.symm hn)
      linarith [hp 2]
    · have := lt_of_le_of_ne (hp 2) (Ne.symm hn)
      linarith [hp 1]
  exact_mod_cast hreal

def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  ∑ i : Fin 4, coefficients i *
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex i)

@[simp] theorem basisDegree_cartan (j : typeF4RootPairing_base.support) :
    basisDegree (Sum.inl j) = 0 := by simp [basisDegree, chevalleyBasisWeight]

@[simp] theorem basisDegree_root (r : F4Chevalley.Root) :
    basisDegree (Sum.inr r) = rootDegree r := rfl

theorem rootDegree_simple (i : Fin 4) :
    rootDegree (typeF4SimpleRootIndex i) = if i = 0 ∨ i = 3 then 0 else 1 := by
  have h : (rootDegree (typeF4SimpleRootIndex i) : ℝ) =
      if i = 0 ∨ i = 3 then 0 else 1 := by
    rw [rootDegree_eq]
    fin_cases i <;> norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, basisVector, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]
  exact_mod_cast h

theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * rootDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  simp only [basisDegree, rootDegree, Fin.sum_univ_four]
  linear_combination coefficients 0 * h0 + coefficients 1 * h1 +
    coefficients 2 * h2 + coefficients 3 * h3

/-- Strictly degree-raising matrices. -/
def Raises (A : MatrixCarrier m) : Prop :=
  ∀ i j, basisDegree i ≤ basisDegree j → A i j = 0

/-- Matrices preserving each homogeneous summand. -/
def PreservesDegree (A : MatrixCarrier m) : Prop :=
  ∀ i j, basisDegree i ≠ basisDegree j → A i j = 0

private theorem raises_add {A B : MatrixCarrier m} (hA : Raises A) (hB : Raises B) :
    Raises (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem raises_mul {A B : MatrixCarrier m} (hA : Raises A) (hB : Raises B) :
    Raises (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree i ≤ basisDegree k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_unit_mul {x y : SplitGroup m}
    (hx : Raises (x.val.val - 1)) (hy : Raises (y.val.val - 1)) :
    Raises ((x * y).val.val - 1) := by
  have he : (x * y).val.val - 1 = (x.val.val - 1) + (y.val.val - 1) +
      (x.val.val - 1) * (y.val.val - 1) := by
    change x.val.val * y.val.val - 1 = _
    noncomm_ring
  rw [he]
  exact raises_add (raises_add hx hy) (raises_mul hx hy)

private theorem property_inv {p : SplitGroup m → Prop} (hone : p 1)
    (hmul : ∀ x y, p x → p y → p (x * y)) {x : SplitGroup m} (hx : p x) : p x⁻¹ := by
  have hp (n : ℕ) : p (x ^ n) := by
    induction n with
    | zero => simpa only [pow_zero] using hone
    | succ n ih => simpa only [pow_succ] using hmul (x ^ n) x ih hx
  have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [hinv]
  exact hp _

private theorem rootCurve_raises (r : F4Chevalley.Root)
    (hr : 0 < rootDegree r) (t : CoefficientField m) :
    Raises ((F4Chevalley.rootCurve r t).val - 1) := by
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      have hp : 0 < (n : ℤ) * rootDegree r := mul_pos (by omega) hr
      omega
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  have he : (1 + t • specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

/-- Every split radical matrix is identity plus a strictly raising matrix. -/
theorem splitRadical_raises (x : SplitGroup m) (hx : x ∈ splitRadical m .linear) :
    Raises (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises r (rootDegree_radical hr) t
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    exact property_inv (p := fun y => Raises (y.val.val - 1))
      (by intro i j _; simp) (fun _ _ => raises_unit_mul) hx

private theorem preservesDegree_one : PreservesDegree (1 : MatrixCarrier m) := by
  intro i j hij
  have hne : i ≠ j := fun he => hij (congrArg basisDegree he)
  simp [hne]

private theorem preservesDegree_add {A B : MatrixCarrier m}
    (hA : PreservesDegree A) (hB : PreservesDegree B) : PreservesDegree (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem preservesDegree_mul {A B : MatrixCarrier m}
    (hA : PreservesDegree A) (hB : PreservesDegree B) : PreservesDegree (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree i = basisDegree k
  · rw [hB k j (by omega), mul_zero]
  · rw [hA i k hik, zero_mul]

private def degreeSubgroup (m : ℕ) : Subgroup (SplitGroup m) where
  carrier := {x | PreservesDegree x.val.val}
  one_mem' := preservesDegree_one
  mul_mem' := preservesDegree_mul
  inv_mem' := property_inv preservesDegree_one (fun _ _ => preservesDegree_mul)

private theorem rootCurve_preservesDegree (r : F4Chevalley.Root)
    (hr : rootDegree r = 0) (t : CoefficientField m) :
    PreservesDegree (F4Chevalley.rootCurve r t).val := by
  have hs (n : ℕ) (s : CoefficientField m) :
      PreservesDegree (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      rw [hr, mul_zero] at hd
      exact hij (sub_eq_zero.mp hd)
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  exact preservesDegree_add (preservesDegree_add
    (preservesDegree_add preservesDegree_one (hs 1 t)) (hs 2 (t ^ 2))) (hs 3 (t ^ 3))

/-- The entire split Levi, including its complementary torus, has degree zero. -/
theorem splitFullLevi_preservesDegree (x : SplitGroup m) (hx : x ∈ splitFullLevi m) :
    PreservesDegree x.val.val := by
  suffices splitFullLevi m ≤ degreeSubgroup m from this hx
  apply sup_le
  · apply sup_le <;> apply (closure_le _).mpr
    all_goals
      rintro x ⟨r, t, hr, rfl⟩
      apply rootCurve_preservesDegree r ?_ t
      have he : (rootDegree r : ℝ) = 0 := by
        rw [rootDegree_eq, hr.1 1 (by simp [leviNodes]), hr.1 2 (by simp [leviNodes])]
        simp
      exact_mod_cast he
  · rw [splitTorus_eq_diagonalTorus]
    intro x hx
    obtain ⟨u, hu⟩ := hx
    change diagonalTorusHom m u = x.val at hu
    change PreservesDegree x.val.val
    rw [← hu, diagonalTorusHom_apply, F4Chevalley.torusConjugation.torusElement_apply]
    change PreservesDegree (Matrix.diagonal _)
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (fun he => hij (congrArg basisDegree he))

/-- The faithful matrix inclusion of the actual Ree fixed group. -/
def modelMatrix (m : ℕ) (x : Model m) : MatrixCarrier m := (toSplitGroup m x).val.val

@[simp] theorem modelMatrix_one (m : ℕ) : modelMatrix m 1 = 1 := by
  simp [modelMatrix]

@[simp] theorem modelMatrix_mul (m : ℕ) (x y : Model m) :
    modelMatrix m (x * y) = modelMatrix m x * modelMatrix m y := by
  simp [modelMatrix]

theorem radical_raises (x : Model m) (hx : x ∈ radical m .linear) :
    Raises (modelMatrix m x - 1) := splitRadical_raises _ hx

theorem fullLevi_preservesDegree (x : Model m) (hx : x ∈ fullLevi m) :
    PreservesDegree (modelMatrix m x) := splitFullLevi_preservesDegree _ hx

end ReeF4.SectionGeometry.LinearRadical.LeviDetection
