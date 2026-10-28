module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi

/-!
# Separating the full split Levi from the Ree seed radical

Evaluate weights on coroot combinations `(4,7,5,3)` and `(7,14,10,5)`.
The resulting root degree is the sum of the simple-root coefficients outside
the chosen Levi. It vanishes on both complete signed subsystem blocks and is
strictly positive on radical roots. Integral divided-power homogeneity makes
Levi matrices preserve grades and radical matrices equal the identity plus
strictly grade-raising terms. Their intersection is therefore trivial.

This extends the matrix grading argument in the binary Suzuki
`SplitFactorization/Separation.lean` to both full Levis and every coefficient
field, preserving the original module. It includes the nonsimple B₂ roots
and the whole root-generated Levi torus.
Source: the Levi construction underlying Aschbacher–Smith F.1.12, printed
pp.263–264, and GLS3 §§2.3–2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds
variable {m : ℕ} {side : Side}

private def coefficients : Side → Fin 4 → ℤ
  | .suzuki => ![4, 7, 5, 3]
  | .linear => ![7, 14, 10, 5]

private def degree (side : Side) (r : F4Chevalley.Root) : ℤ :=
  ∑ i : Fin 4, coefficients side i *
    typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)

private theorem degree_eq (side : Side) (r : F4Chevalley.Root) :
    (degree side r : ℝ) = match side with
      | .suzuki => typeF4SimpleCoefficient r.val 0 + typeF4SimpleCoefficient r.val 3
      | .linear => typeF4SimpleCoefficient r.val 1 + typeF4SimpleCoefficient r.val 2 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) := by
    exact (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  simp only [degree, Int.cast_sum, Int.cast_mul, hp, typeF4CorootScale_simpleRoot]
  cases side <;>
    norm_num [coefficients, Fin.sum_univ_four,
      typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

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

private theorem degree_radical {r : F4Chevalley.Root} (hr : IsRadicalRoot side r) :
    0 < degree side r := by
  have hp (i : Fin 4) := coefficient_nonneg hr.1 i
  have hreal : 0 < (degree side r : ℝ) := by
    rw [degree_eq]
    obtain ⟨i, hi, hn⟩ := hr.2
    cases side <;> fin_cases i <;> simp [leviNodes] at hi
    all_goals dsimp only
    · have := lt_of_le_of_ne (hp 0) (Ne.symm hn)
      linarith [hp 3]
    · have := lt_of_le_of_ne (hp 3) (Ne.symm hn)
      linarith [hp 0]
    · have := lt_of_le_of_ne (hp 1) (Ne.symm hn)
      linarith [hp 2]
    · have := lt_of_le_of_ne (hp 2) (Ne.symm hn)
      linarith [hp 1]
  exact_mod_cast hreal

private theorem degree_levi {r : F4Chevalley.Root}
    (hr : ∀ i, i ∉ leviNodes side → typeF4SimpleCoefficient r.val i = 0) :
    degree side r = 0 := by
  have hreal : (degree side r : ℝ) = 0 := by
    rw [degree_eq]
    cases side with
    | suzuki =>
      rw [hr 0 (by simp [leviNodes]), hr 3 (by simp [leviNodes]), zero_add]
    | linear =>
      rw [hr 1 (by simp [leviNodes]), hr 2 (by simp [leviNodes]), zero_add]
  exact_mod_cast hreal

private def basisDegree (side : Side) (a : F4Chevalley.BasisIndex) : ℤ :=
  ∑ i : Fin 4, coefficients side i *
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex i)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree side i - basisDegree side j = (n : ℤ) * degree side r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  simp only [basisDegree, degree, Fin.sum_univ_four]
  linear_combination coefficients side 0 * h0 + coefficients side 1 * h1 +
    coefficients side 2 * h2 + coefficients side 3 * h3

private def Raises (side : Side) (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField m)) : Prop :=
  ∀ i j, basisDegree side i ≤ basisDegree side j → A i j = 0

private def Preserves (side : Side) (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField m)) : Prop :=
  ∀ i j, basisDegree side i ≠ basisDegree side j → A i j = 0

private theorem raises_add {A B} (hA : Raises (m := m) side A) (hB : Raises (m := m) side B) : Raises (m := m) side (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem raises_mul {A B} (hA : Raises (m := m) side A) (hB : Raises (m := m) side B) : Raises (m := m) side (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree side i ≤ basisDegree side k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_unit_mul {x y : SplitGroup m}
    (hx : Raises (m := m) side (x.val.val - 1)) (hy : Raises (m := m) side (y.val.val - 1)) :
    Raises (m := m) side ((x * y).val.val - 1) := by
  have he : (x * y).val.val - 1 = (x.val.val - 1) + (y.val.val - 1) +
      (x.val.val - 1) * (y.val.val - 1) := by
    change x.val.val * y.val.val - 1 = _
    noncomm_ring
  rw [he]
  exact raises_add (raises_add hx hy) (raises_mul hx hy)

private theorem preserves_one : Preserves (m := m) side 1 := by
  intro i j hij
  have hne : i ≠ j := fun he => hij (congrArg (basisDegree side) he)
  simp [hne]

private theorem preserves_add {A B} (hA : Preserves (m := m) side A) (hB : Preserves (m := m) side B) :
    Preserves (m := m) side (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem preserves_mul {A B} (hA : Preserves (m := m) side A) (hB : Preserves (m := m) side B) :
    Preserves (m := m) side (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree side i = basisDegree side k
  · rw [hB k j (by omega), mul_zero]
  · rw [hA i k hik, zero_mul]

private theorem property_inv {p : SplitGroup m → Prop} (hone : p 1)
    (hmul : ∀ x y, p x → p y → p (x * y)) {x : SplitGroup m} (hx : p x) : p x⁻¹ := by
  have hp (n : ℕ) : p (x ^ n) := by
    induction n with
    | zero => simpa only [pow_zero] using hone
    | succ n ih => simpa only [pow_succ] using hmul (x ^ n) x ih hx
  obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
  have hinv : x⁻¹ = x ^ (n - 1) := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hn, he]
  rw [hinv]
  exact hp _

private theorem rootCurve_preserves (r : F4Chevalley.Root)
    {p : Bool} (hr : IsSimpleBlockRoot side p r) (t : CoefficientField m) :
    Preserves (m := m) side (F4Chevalley.rootCurve r t).val := by
  have hs (n : ℕ) (s : CoefficientField m) :
      Preserves (m := m) side (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree (side := side) r n i j hne
      rw [degree_levi hr.1, mul_zero] at hd
      exact hij (sub_eq_zero.mp hd)
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  exact preserves_add (preserves_add (preserves_add preserves_one (hs 1 t))
    (hs 2 (t ^ 2))) (hs 3 (t ^ 3))

private theorem rootCurve_raises (r : F4Chevalley.Root)
    (hr : IsRadicalRoot side r) (t : CoefficientField m) :
    Raises (m := m) side ((F4Chevalley.rootCurve r t).val - 1) := by
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises (m := m) side (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree (side := side) r n i j hne
      have hp : 0 < (n : ℤ) * degree side r :=
        mul_pos (by exact_mod_cast hn) (degree_radical hr)
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

private theorem splitLevi_preserves (x : SplitGroup m) (hx : x ∈ splitLevi m side) :
    Preserves (m := m) side x.val.val := by
  rw [splitLevi, splitSimpleBlock, splitSimpleBlock, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    all_goals
      obtain ⟨r, t, hr, rfl⟩ := hx
      exact rootCurve_preserves r hr t
  | one => exact preserves_one
  | mul x y _ _ hx hy => exact preserves_mul hx hy
  | inv x _ hx =>
    exact property_inv (p := fun x => Preserves (m := m) side x.val.val)
      preserves_one (fun _ _ => preserves_mul) hx

private theorem splitRadical_raises (x : SplitGroup m) (hx : x ∈ splitRadical m side) :
    Raises (m := m) side (x.val.val - 1) := by
  have hone : Raises (m := m) side ((1 : SplitGroup m).val.val - 1) := by intro i j _; simp
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises r hr t
  | one => exact hone
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    exact property_inv (p := fun x => Raises (m := m) side (x.val.val - 1))
      hone (fun _ _ => raises_unit_mul) hx

/-- The full signed subsystem Levi and the positive radical intersect trivially
for either side and every coefficient field. -/
theorem splitLevi_disjoint_splitRadical (m : ℕ) (side : Side) :
    Disjoint (splitLevi m side) (splitRadical m side) := by
  apply disjoint_def.mpr
  intro x hxL hxR
  have hL := splitLevi_preserves x hxL
  have hR := splitRadical_raises x hxR
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : basisDegree side i = basisDegree side j
  · exact sub_eq_zero.mp (hR i j (le_of_eq hij))
  · have hne : i ≠ j := fun he => hij (congrArg (basisDegree side) he)
    rw [hL i j hij]
    simp [hne]

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
