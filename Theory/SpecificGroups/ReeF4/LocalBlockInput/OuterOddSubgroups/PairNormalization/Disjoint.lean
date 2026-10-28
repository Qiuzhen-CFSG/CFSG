module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair

/-!
# Trivial intersection of the actual positive and negative Ree subgroups

The Cartan-plus-root basis is graded by the linear combination of simple
coroot coordinates with coefficients `(11, 21, 15, 8)`. Positive roots strictly
raise this grading, while negative roots strictly lower it. A matrix in both
root-generated subgroups must therefore be the identity. Restriction to the
supplied twist-fixed subgroup gives the required opposition intersection.

The grading calculation extends the one used in `PositiveTwoGroup.lean` to
both signs without changing that shared module. No Bruhat decomposition,
automorphism classification, or existence of a fixed Weyl representative is
used here.

Source: GLS3, Theorem 2.3.8(c), in `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.LocalBlockInput.PairNormalization

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


noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem rootDegree_neg (r : F4Chevalley.Root) : rootDegree (-r) = -rootDegree r := by
  simp only [rootDegree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring

private theorem rootDegree_neg_of_not_pos {r : F4Chevalley.Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) : rootDegree r < 0 := by
  have h := rootDegree_pos ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr)
  rw [rootDegree_neg] at h
  omega

private theorem dividedPower_raises (m : ℕ) (r : F4Chevalley.Root)
    (c : ℤ) (hc : 0 < c * rootDegree r) (n : ℕ) (hn : 0 < n) :
    Raises (fun i => c * basisDegree i) (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := congrArg (c * ·) (dividedPower_degree r n i j hint)
  have hp : 0 < (n : ℤ) * (c * rootDegree r) :=
    mul_pos (by exact_mod_cast hn) hc
  nlinarith

private theorem rootCurve_raises (m : ℕ) (r : F4Chevalley.Root)
    (c : ℤ) (hc : 0 < c * rootDegree r) (t : CoefficientField m) :
    Raises (fun i => c * basisDegree i) ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises (fun i => c * basisDegree i) (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul,
      dividedPower_raises m r c hc n hn i j hij, mul_zero]
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

private theorem closure_raises {m : ℕ} (w : F4Chevalley.BasisIndex → ℤ)
    (S : Set (SplitGroup m)) (hS : ∀ x ∈ S, Raises w (x.val.val - 1))
    (x : SplitGroup m) (hx : x ∈ closure S) : Raises w (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    have he : x⁻¹ = x ^ (orderOf x - 1) := by
      apply mul_left_cancel (a := x)
      rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [he]
    exact raises_unit_pow hx _

/-- The split positive and negative root closures have trivial intersection. -/
theorem splitUnipotent_disjoint_negative (m : ℕ) :
    Disjoint (LargeLocalSeeds.splitUnipotent m) (splitNegativeUnipotent m) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  have hp : Raises basisDegree (x.val.val - 1) := by
    apply closure_raises _ _ ?_ x hx
    rintro y ⟨r, t, hr, rfl⟩
    simpa only [rootGeneratorInGroup_coe, one_mul] using rootCurve_raises m r 1 (by simpa using rootDegree_pos hr) t
  have hn : Raises (fun i => -basisDegree i) (x.val.val - 1) := by
    apply closure_raises _ _ ?_ x hy
    rintro y ⟨r, t, hr, rfl⟩
    simpa only [rootGeneratorInGroup_coe, neg_one_mul] using
      rootCurve_raises m r (-1) (by simpa using rootDegree_neg_of_not_pos hr) t
  apply Subtype.ext
  apply Units.ext
  apply sub_eq_zero.mp
  ext i j
  rcases le_total (basisDegree i) (basisDegree j) with hij | hji
  · exact hp i j hij
  · exact hn i j (neg_le_neg hji)

/-- The specified actual fixed positive and negative subgroups are disjoint,
for every supplied construction input, including the binary endpoint. -/
theorem standardUnipotent_disjoint_opposite {m : ℕ} (d : LocalBlockInput m) :
    Disjoint (LargeLocalSeeds.standardUnipotent d) (oppositeUnipotent d) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  apply Subtype.ext
  exact (Subgroup.disjoint_def.mp (splitUnipotent_disjoint_negative m)) hx hy

end ReeF4.LocalBlockInput.PairNormalization
end
