module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.Levi
public import Mathlib.GroupTheory.Complement

/-!
# Separating the binary middle-node Levi from its radical

Evaluate Chevalley weights on the coroot combination `(4, 7, 5, 3)`.
On roots this is the sum of the two outer simple-root coefficients. It is
zero on the signed middle simple roots and strictly positive on every root
of the specified Suzuki-side radical. Homogeneity of the integral divided
powers therefore makes Levi matrices preserve each grade, while radical
matrices are identity plus a strictly grade-raising matrix. Their intersection
is trivial, proving uniqueness of Levi–radical expressions in the split seed.

This argument concerns the actual split F₄ matrices at `m = 0`; it does not
require ordered root coordinates or identify the fixed Levi. Existence of
factorizations and normality remain separate root calculations.
Source: the parabolic Levi construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction

namespace ReeF4.Parabolics.BinarySuzuki
open LargeLocalSeeds Subgroup
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def outerDegree (r : F4Chevalley.Root) : ℤ :=
  4 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  7 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  5 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  3 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem outerDegree_eq (r : F4Chevalley.Root) :
    (outerDegree r : ℝ) = typeF4SimpleCoefficient r.val 0 + typeF4SimpleCoefficient r.val 3 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) := by
    exact (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  simp only [outerDegree, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hp,
    typeF4CorootScale_simpleRoot]
  norm_num [typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem simpleCoefficient_nonneg {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (q : Fin 4) :
    0 ≤ typeF4SimpleCoefficient r.val q := by
  have hs (r : F4Chevalley.Root) (hr : r ∈ typeF4RootPairing_base.support) :
      0 ≤ typeF4SimpleCoefficient r.val q := by
    obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have he : typeF4SimpleRootIndex i = r := congrArg Subtype.val hi
    rw [← he]
    fin_cases i <;> fin_cases q <;>
      norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val, typeF4SimpleRoot, basisVector, Matrix.cons_val_two, Matrix.cons_val_three]
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

private theorem outerDegree_radical {r : F4Chevalley.Root} (hr : IsRadicalRoot .suzuki r) :
    0 < outerDegree r := by
  have h0 := simpleCoefficient_nonneg hr.1 0
  have h3 := simpleCoefficient_nonneg hr.1 3
  have hreal : 0 < (outerDegree r : ℝ) := by
    rw [outerDegree_eq]
    obtain ⟨i, hi, hn⟩ := hr.2
    fin_cases i <;> simp [leviNodes] at hi
    · have := lt_of_le_of_ne h0 (Ne.symm hn)
      linarith
    · have := lt_of_le_of_ne h3 (Ne.symm hn)
      linarith
  exact_mod_cast hreal

private theorem outerDegree_levi {r : F4Chevalley.Root} (hr : IsLeviGeneratorRoot r) :
    outerDegree r = 0 := by
  have hp (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  obtain ⟨i, hi, h⟩ := hr
  fin_cases i <;> simp [leviNodes] at hi
  all_goals rcases h with rfl | rfl
  all_goals
    simp only [outerDegree, RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left, hp]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]

private def basisOuterDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  4 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  7 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  5 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  3 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisOuterDegree i - basisOuterDegree j = (n : ℤ) * outerDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisOuterDegree, outerDegree]
  linear_combination 4 * h0 + 7 * h1 + 5 * h2 + 3 * h3

private def Raises (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)) : Prop :=
  ∀ i j, basisOuterDegree i ≤ basisOuterDegree j → A i j = 0

private def Preserves (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)) : Prop :=
  ∀ i j, basisOuterDegree i ≠ basisOuterDegree j → A i j = 0

private theorem raises_add {A B} (hA : Raises A) (hB : Raises B) : Raises (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem raises_mul {A B} (hA : Raises A) (hB : Raises B) : Raises (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisOuterDegree i ≤ basisOuterDegree k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_unit_mul {x y : SplitGroup 0}
    (hx : Raises (x.val.val - 1)) (hy : Raises (y.val.val - 1)) :
    Raises ((x * y).val.val - 1) := by
  have he : (x * y).val.val - 1 = (x.val.val - 1) + (y.val.val - 1) +
      (x.val.val - 1) * (y.val.val - 1) := by
    change x.val.val * y.val.val - 1 = _
    noncomm_ring
  rw [he]
  exact raises_add (raises_add hx hy) (raises_mul hx hy)

private theorem preserves_one : Preserves 1 := by
  intro i j hij
  have hne : i ≠ j := fun he => hij (congrArg basisOuterDegree he)
  simp [hne]

private theorem preserves_add {A B} (hA : Preserves A) (hB : Preserves B) :
    Preserves (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem preserves_mul {A B} (hA : Preserves A) (hB : Preserves B) :
    Preserves (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisOuterDegree i = basisOuterDegree k
  · rw [hB k j (by omega), mul_zero]
  · rw [hA i k hik, zero_mul]

private theorem property_inv {p : SplitGroup 0 → Prop} (hone : p 1)
    (hmul : ∀ x y, p x → p y → p (x * y)) {x : SplitGroup 0} (hx : p x) : p x⁻¹ := by
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
    (hr : IsLeviGeneratorRoot r) (t : CoefficientField 0) :
    Preserves (F4Chevalley.rootCurve r t).val := by
  have hs (n : ℕ) (s : CoefficientField 0) :
      Preserves (s • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      rw [outerDegree_levi hr, mul_zero] at hd
      exact hij (sub_eq_zero.mp hd)
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  exact preserves_add (preserves_add (preserves_add preserves_one (hs 1 t))
    (hs 2 (t ^ 2))) (hs 3 (t ^ 3))

private theorem rootCurve_raises (r : F4Chevalley.Root)
    (hr : IsRadicalRoot .suzuki r) (t : CoefficientField 0) :
    Raises ((F4Chevalley.rootCurve r t).val - 1) := by
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField 0) :
      Raises (s • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      have hp : 0 < (n : ℤ) * outerDegree r :=
        mul_pos (by exact_mod_cast hn) (outerDegree_radical hr)
      omega
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  have he : (1 + t • specializeMatrix (S := CoefficientField 0)
      (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private theorem splitLevi_preserves (x : SplitGroup 0) (hx : x ∈ splitLevi) :
    Preserves x.val.val := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_preserves r hr t
  | one => exact preserves_one
  | mul x y _ _ hx hy => exact preserves_mul hx hy
  | inv x _ hx =>
    exact property_inv (p := fun x => Preserves x.val.val)
      preserves_one (fun _ _ => preserves_mul) hx

private theorem splitRadical_raises (x : SplitGroup 0) (hx : x ∈ splitRadical 0 .suzuki) :
    Raises (x.val.val - 1) := by
  have hone : Raises ((1 : SplitGroup 0).val.val - 1) := by intro i j _; simp
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises r hr t
  | one => exact hone
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    exact property_inv (p := fun x => Raises (x.val.val - 1))
      hone (fun _ _ => raises_unit_mul) hx

/-- The actual middle-node Levi and positive radical intersect trivially. -/
theorem splitLevi_disjoint_splitRadical : Disjoint splitLevi (splitRadical 0 .suzuki) := by
  apply disjoint_def.mpr
  intro x hxL hxR
  have hL := splitLevi_preserves x hxL
  have hR := splitRadical_raises x hxR
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : basisOuterDegree i = basisOuterDegree j
  · exact sub_eq_zero.mp (hR i j (le_of_eq hij))
  · have hne : i ≠ j := fun he => hij (congrArg basisOuterDegree he)
    rw [hL i j hij]
    simp [hne]

/-- Trivial intersection remains true relative to the specified split seed. -/
theorem splitLeviInSeed_disjoint_splitRadicalInSeed :
    Disjoint splitLeviInSeed splitRadicalInSeed := by
  apply disjoint_def.mpr
  intro x hxL hxR
  apply Subtype.ext
  exact disjoint_def.mp splitLevi_disjoint_splitRadical hxL hxR

/-- There is at most one Levi–radical expression for any element of the split seed. -/
theorem splitLeviRadical_mul_injective : Function.Injective
    (fun p : splitLeviInSeed × splitRadicalInSeed => p.1.val * p.2.val) :=
  mul_injective_of_disjoint splitLeviInSeed_disjoint_splitRadicalInSeed

end
end ReeF4.Parabolics.BinarySuzuki
