module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.RootSubgroups
public import Mathlib.GroupTheory.Sylow

/-!
# Positive two-subgroups in the Ree F₄ construction

The integral Cartan-plus-root basis has a grading obtained by evaluating the
simple-coroot coordinates with coefficients `(11, 21, 15, 8)`. Every simple
root has degree one, hence every positive root has positive degree. The checked
homogeneity of the integral divided powers shows that each positive root curve
is one plus a strictly grading-raising matrix. Such matrices form a group, and
in characteristic two a sufficiently large power of two is the identity.
Consequently both the concrete split positive subgroup and its actual fixed
subgroup are two-groups. No claim of Sylow maximality is made here.

This is the unitriangular part of the standard Chevalley construction used by
Steinberg, *Lectures on Chevalley Groups*. It supplies the positive-subgroup
calculation for Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`; odd index and fixed-point generation remain separate.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix

namespace ReeF4.LargeLocalSeeds

section GradedMatrices
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

private def Raises (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0

omit [Fintype ι] [DecidableEq ι] in
private theorem raises_add {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

omit [DecidableEq ι] in
private theorem raises_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i ≤ w k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_pow_entry {w : ι → ℤ} {A : Matrix ι ι K}
    (hA : Raises w A) (n : ℕ) (i j : ι) (hij : w i < w j + n) :
    (A ^ n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hne : i ≠ j := by rintro rfl; omega
    simp [hne]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : w i < w k + n
    · rw [ih i k hik, zero_mul]
    · rw [hA k j (by omega), mul_zero]

private theorem two_power_eq_one_of_raises [Nonempty ι] [CharP K 2]
    {w : ι → ℤ} {A : Matrix ι ι K} (hA : Raises w (A - 1)) :
    ∃ n : ℕ, A ^ (2 ^ n) = 1 := by
  obtain ⟨a, ha⟩ := Finite.bddAbove_range w
  obtain ⟨b, hb⟩ := Finite.bddBelow_range w
  let n := (a - b).toNat + 1
  have hn : (n : ℤ) < (2 ^ n : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := n))
  have hn' : a - b < (n : ℤ) := by dsimp [n]; omega
  have hzero : (A - 1) ^ (2 ^ n) = 0 := by
    ext i j
    apply raises_pow_entry hA
    have hi := ha (Set.mem_range_self i)
    have hj := hb (Set.mem_range_self j)
    omega
  refine ⟨n, ?_⟩
  let : CharP (Matrix ι ι K) 2 :=
    charP_of_injective_ringHom (algebraMap K (Matrix ι ι K)).injective 2
  have he := add_pow_char_pow_of_commute 2 n (Commute.one_right (A - 1))
  simpa only [sub_add_cancel, hzero, one_pow, zero_add] using he

private theorem raises_unit_mul {w : ι → ℤ} {A B : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (hB : Raises w (B.val - 1)) :
    Raises w ((A * B).val - 1) := by
  have he : (A * B).val - 1 = (A.val - 1) + (B.val - 1) +
      (A.val - 1) * (B.val - 1) := by simp only [Units.val_mul]; noncomm_ring
  rw [he]
  exact raises_add (raises_add hA hB) (raises_mul hA hB)

private theorem raises_unit_pow {w : ι → ℤ} {A : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (n : ℕ) : Raises w ((A ^ n).val - 1) := by
  induction n with
  | zero => intro i j _; simp
  | succ n ih => rw [pow_succ]; exact raises_unit_mul ih hA

private theorem raises_unit_inv [Nonempty ι] [CharP K 2] {w : ι → ℤ} {A : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) : Raises w (A⁻¹.val - 1) := by
  obtain ⟨n, hn⟩ := two_power_eq_one_of_raises hA
  have hnU : A ^ (2 ^ n) = 1 := Units.ext hn
  have he : A⁻¹ = A ^ (2 ^ n - 1) := by
    apply mul_left_cancel (a := A)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow n 2 (by decide)), hnU]
  rw [he]
  exact raises_unit_pow hA _

end GradedMatrices

private noncomputable def rootDegree (r : F4Chevalley.Root) : ℤ :=
  11 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  21 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  15 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  8 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem rootDegree_simple (i : Fin 4) : rootDegree (typeF4SimpleRootIndex i) = 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootDegree, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem rootDegree_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    rootDegree k = rootDegree i + rootDegree j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [rootDegree, hp]
  ring

private theorem rootDegree_pos {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 < rootDegree r := by
  apply hr.induction_on_add
  · intro i hi
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, rootDegree_simple]
    omega
  · intro i j k hk hi hj
    obtain ⟨l, hl⟩ := typeF4RootPairing_baseEquiv.surjective ⟨j, hj⟩
    have he : typeF4SimpleRootIndex l = j := congrArg Subtype.val hl
    rw [rootDegree_add hk, ← he, rootDegree_simple]
    omega


noncomputable local instance : Nonempty F4Chevalley.BasisIndex :=
  ⟨Sum.inl (typeF4RootPairing_baseEquiv 0)⟩

private noncomputable def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  11 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  21 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  15 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  8 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * rootDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination 11 * h0 + 21 * h1 + 15 * h2 + 8 * h3

private theorem dividedPower_raises (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n) :
    Raises basisDegree (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hp : 0 < (n : ℤ) * rootDegree r :=
    mul_pos (by exact_mod_cast hn) (rootDegree_pos hr)
  omega

private theorem rootCurve_raises (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    Raises basisDegree ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises basisDegree (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul, dividedPower_raises m r hr n hn i j hij,
      mul_zero]
  have he : (1 + t • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m) (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private theorem splitUnipotent_raises (m : ℕ) (x : SplitGroup m)
    (hx : x ∈ splitUnipotent m) :
    Raises basisDegree (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises m r hr t
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx => exact raises_unit_inv hx

/-- Positive F₄ root matrices are unitriangular in the integral root grading;
therefore their subgroup in characteristic two is a two-group. -/
theorem splitUnipotent_isPGroup (m : ℕ) : IsPGroup 2 (splitUnipotent m) := by
  intro x
  obtain ⟨n, hn⟩ := two_power_eq_one_of_raises (splitUnipotent_raises m x.val x.property)
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext hn

/-- The actual fixed positive subgroup inherits the two-group property. -/
theorem standardUnipotent_isPGroup {m : ℕ} (d : LocalBlockInput m) :
    IsPGroup 2 (standardUnipotent d) :=
  (splitUnipotent_isPGroup m).comap_of_injective d.fixedGroup.subtype Subtype.val_injective

end ReeF4.LargeLocalSeeds

end
