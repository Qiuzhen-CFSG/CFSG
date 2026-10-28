module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.RootBorel

/-!
# Recovering a negative simple block from the positive root parabolic

Grade the Cartan-plus-root basis by the sum of the simple-root coefficients
outside the chosen Levi nodes. The coroot combinations `(7, 14, 10, 5)` and
`(4, 7, 5, 3)` give these gradings on the linear and Suzuki sides. Positive
root matrices weakly raise the grade, diagonal torus matrices preserve it,
and every root supported on the Levi nodes preserves it. In particular this
includes the nonsimple roots in the Suzuki side's B₂ subsystem.

Negative root matrices weakly lower the grade. Taking the degree-zero matrix
blocks respects products of such matrices; on their generators it retains
exactly the roots supported on the Levi nodes. An element in the intersection
of the negative unipotent and positive root parabolic preserves grades in both
directions, so it equals its degree-zero projection and lies in the negative
simple block. Finiteness handles inversion in the generated subgroups.

Restriction to the exceptional fixed group uses only containment of the join
of the fixed subgroups in the split parabolic. It does not require fixed points
to preserve joins. The only extra input is that the split coroot torus lies in
the diagonal torus; simplicity, perfectness, the parameter bound and a Sylow
index hypothesis are unnecessary for this intersection calculation.

Source: the root-subsystem and parabolic geometry of GLS3, 2.3.6–8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`. The grading calculations extend the private
linear and Suzuki Levi-separation arguments in `ParabolicAmalgam/BinaryLocals`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.LocalBlockInput.PairRigidity
open LargeLocalSeeds
noncomputable section
local instance rootIntersectionInvolutiveNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

private def gradingCoefficients : Side → Fin 4 → ℤ
  | .linear => ![7, 14, 10, 5]
  | .suzuki => ![4, 7, 5, 3]

private def rootDegree (s : Side) (r : F4Chevalley.Root) : ℤ :=
  gradingCoefficients s 0 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  gradingCoefficients s 1 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  gradingCoefficients s 2 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  gradingCoefficients s 3 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem rootDegree_eq (s : Side) (r : F4Chevalley.Root) :
    (rootDegree s r : ℝ) = match s with
      | .linear => typeF4SimpleCoefficient r.val 1 + typeF4SimpleCoefficient r.val 2
      | .suzuki => typeF4SimpleCoefficient r.val 0 + typeF4SimpleCoefficient r.val 3 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) :=
    (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  cases s <;>
    simp only [rootDegree, gradingCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, hp, typeF4CorootScale_simpleRoot]
  all_goals
    norm_num [typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector,
      Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
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
      norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, basisVector, Matrix.cons_val_two, Matrix.cons_val_three]
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

private theorem coefficient_neg (r : F4Chevalley.Root) (i : Fin 4) :
    typeF4SimpleCoefficient (-r).val i = -typeF4SimpleCoefficient r.val i := by
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hv]
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

private theorem simpleCoefficient_nonpos {r : F4Chevalley.Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) (i : Fin 4) :
    typeF4SimpleCoefficient r.val i ≤ 0 := by
  have h := simpleCoefficient_nonneg
    ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr) i
  rw [coefficient_neg] at h
  linarith

private theorem rootDegree_nonneg (s : Side) {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 ≤ rootDegree s r := by
  have h : (0 : ℝ) ≤ rootDegree s r := by
    rw [rootDegree_eq]
    cases s <;> exact add_nonneg (simpleCoefficient_nonneg hr _) (simpleCoefficient_nonneg hr _)
  exact_mod_cast h

private theorem rootDegree_nonpos (s : Side) {r : F4Chevalley.Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) : rootDegree s r ≤ 0 := by
  have h : (rootDegree s r : ℝ) ≤ 0 := by
    rw [rootDegree_eq]
    cases s <;> exact add_nonpos (simpleCoefficient_nonpos hr _) (simpleCoefficient_nonpos hr _)
  exact_mod_cast h

private theorem rootDegree_zero_of_support (s : Side) {r : F4Chevalley.Root}
    (hr : ∀ i, i ∉ leviNodes s → typeF4SimpleCoefficient r.val i = 0) :
    rootDegree s r = 0 := by
  have h : (rootDegree s r : ℝ) = 0 := by
    rw [rootDegree_eq]
    cases s with
    | linear =>
      change typeF4SimpleCoefficient r.val 1 + typeF4SimpleCoefficient r.val 2 = 0
      rw [hr 1 (by simp [leviNodes]), hr 2 (by simp [leviNodes]), zero_add]
    | suzuki =>
      change typeF4SimpleCoefficient r.val 0 + typeF4SimpleCoefficient r.val 3 = 0
      rw [hr 0 (by simp [leviNodes]), hr 3 (by simp [leviNodes]), zero_add]
  exact_mod_cast h

private theorem support_of_rootDegree_zero (s : Side) {r : F4Chevalley.Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) (hz : rootDegree s r = 0) :
    ∀ i, i ∉ leviNodes s → typeF4SimpleCoefficient r.val i = 0 := by
  have h : (rootDegree s r : ℝ) = 0 := by rw [hz]; norm_num
  rw [rootDegree_eq] at h
  have h0 := simpleCoefficient_nonpos hr 0
  have h1 := simpleCoefficient_nonpos hr 1
  have h2 := simpleCoefficient_nonpos hr 2
  have h3 := simpleCoefficient_nonpos hr 3
  cases s with
  | linear =>
    have ha : typeF4SimpleCoefficient r.val 1 = 0 := by dsimp only at h; linarith
    have hb : typeF4SimpleCoefficient r.val 2 = 0 := by dsimp only at h; linarith
    intro i hi
    fin_cases i <;> simp [leviNodes] at hi
    · exact ha
    · exact hb
  | suzuki =>
    have ha : typeF4SimpleCoefficient r.val 0 = 0 := by dsimp only at h; linarith
    have hb : typeF4SimpleCoefficient r.val 3 = 0 := by dsimp only at h; linarith
    intro i hi
    fin_cases i <;> simp [leviNodes] at hi
    · exact ha
    · exact hb

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

section Matrices
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

private def Triangular (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i < w j → A i j = 0

private def degreeZero (w : ι → ℤ) (A : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if w i = w j then A i j else 0

omit [Fintype ι] in
private theorem triangular_one (w : ι → ℤ) : Triangular w (1 : Matrix ι ι K) := by
  intro i j hij
  exact Matrix.one_apply_ne (fun h => (ne_of_lt hij) (congrArg w h))

omit [DecidableEq ι] in
private theorem triangular_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Triangular w A) (hB : Triangular w B) : Triangular w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i < w k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

omit [Fintype ι] in
private theorem degreeZero_one (w : ι → ℤ) :
    degreeZero w (1 : Matrix ι ι K) = 1 := by
  ext i j
  by_cases h : w i = w j
  · simp [degreeZero, h]
  · have hn : i ≠ j := fun he => h (congrArg w he)
    simp [degreeZero, h, hn]

omit [DecidableEq ι] in
private theorem degreeZero_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Triangular w A) (hB : Triangular w B) :
    degreeZero w (A * B) = degreeZero w A * degreeZero w B := by
  ext i j
  change (if w i = w j then (A * B) i j else 0) = _
  by_cases hij : w i = w j
  · rw [if_pos hij, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    change A i k * B k j = (if w i = w k then A i k else 0) *
      (if w k = w j then B k j else 0)
    by_cases hik : w i = w k
    · rw [if_pos hik, if_pos (hik.symm.trans hij)]
    · rw [if_neg hik, zero_mul]
      by_cases hlt : w i < w k
      · rw [hA i k hlt, zero_mul]
      · rw [hB k j (by omega), mul_zero]
  · rw [if_neg hij, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    change (if w i = w k then A i k else 0) * (if w k = w j then B k j else 0) = 0
    by_cases hik : w i = w k
    · rw [if_neg (show w k ≠ w j by omega), mul_zero]
    · rw [if_neg hik, zero_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem degreeZero_eq_of_both {w : ι → ℤ} {A : Matrix ι ι K}
    (hA : Triangular w A) (hB : Triangular (fun i => -w i) A) :
    degreeZero w A = A := by
  ext i j
  by_cases hij : w i = w j
  · simp [degreeZero, hij]
  · simp only [degreeZero, if_neg hij]
    by_cases hlt : w i < w j
    · exact (hA i j hlt).symm
    · exact (hB i j (by dsimp only; omega)).symm

end Matrices

private theorem property_inv {G : Type*} [Group G] [Finite G]
    {p : G → Prop} (hone : p 1) (hmul : ∀ x y, p x → p y → p (x * y))
    {x : G} (hx : p x) : p x⁻¹ := by
  have hp (n : ℕ) : p (x ^ n) := by
    induction n with
    | zero => simpa only [pow_zero] using hone
    | succ n ih => simpa only [pow_succ] using hmul (x ^ n) x ih hx
  have he : x⁻¹ = x ^ (orderOf x - 1) := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [he]
  exact hp _

private theorem rootCurve_entry_of_degree_ne (m : ℕ) (s : Side) (r : F4Chevalley.Root)
    (t : CoefficientField m) (i j : F4Chevalley.BasisIndex)
    (h : ∀ n : ℕ, 0 < n → basisDegree s i - basisDegree s j ≠ (n : ℤ) * rootDegree s r) :
    (F4Chevalley.rootCurve r t).val i j = (1 : Matrix _ _ (CoefficientField m)) i j := by
  have hz (n : ℕ) (hn : 0 < n) :
      F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
    by_contra hne
    exact h n hn (dividedPower_degree s r n i j hne)
  rw [F4Chevalley.rootCurve_matrix_formula]
  simp [Matrix.add_apply, Matrix.smul_apply, specializeMatrix,
    hz 1 (by decide), hz 2 (by decide), hz 3 (by decide)]

private theorem rootCurve_triangular (m : ℕ) (s : Side) (r : F4Chevalley.Root)
    (c : ℤ) (hc : 0 ≤ c * rootDegree s r) (t : CoefficientField m) :
    Triangular (fun i => c * basisDegree s i) (F4Chevalley.rootCurve r t).val := by
  intro i j hij
  have hn : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
  rw [rootCurve_entry_of_degree_ne m s r t i j, Matrix.one_apply_ne hn]
  intro n _ he
  have hd := congrArg (c * ·) he
  have hp : 0 ≤ (n : ℤ) * (c * rootDegree s r) := mul_nonneg (Nat.cast_nonneg n) hc
  nlinarith

private theorem rootCurve_degreeZero_of_zero (m : ℕ) (s : Side) (r : F4Chevalley.Root)
    (hz : rootDegree s r = 0) (t : CoefficientField m) :
    degreeZero (fun i => -basisDegree s i) (F4Chevalley.rootCurve r t).val =
      (F4Chevalley.rootCurve r t).val := by
  ext i j
  by_cases hij : -basisDegree s i = -basisDegree s j
  · simp [degreeZero, hij]
  · simp only [degreeZero, if_neg hij]
    have hn : i ≠ j := fun he => hij (congrArg (fun i => -basisDegree s i) he)
    rw [rootCurve_entry_of_degree_ne m s r t i j, Matrix.one_apply_ne hn]
    intro n _ he
    rw [hz, mul_zero] at he
    apply hij
    exact congrArg Neg.neg (sub_eq_zero.mp he)

private theorem rootCurve_degreeZero_of_ne (m : ℕ) (s : Side) (r : F4Chevalley.Root)
    (hr : rootDegree s r ≠ 0) (t : CoefficientField m) :
    degreeZero (fun i => -basisDegree s i) (F4Chevalley.rootCurve r t).val = 1 := by
  ext i j
  by_cases hij : -basisDegree s i = -basisDegree s j
  · simp only [degreeZero, if_pos hij]
    apply rootCurve_entry_of_degree_ne
    intro n hn he
    have hd : basisDegree s i = basisDegree s j := by omega
    rw [hd, sub_self] at he
    exact hr ((mul_eq_zero.mp he.symm).resolve_left (by omega))
  · have hn : i ≠ j := fun he => hij (congrArg (fun i => -basisDegree s i) he)
    simp [degreeZero, hij, Matrix.one_apply_ne hn]

private def triangularSubgroup (m : ℕ) (w : F4Chevalley.BasisIndex → ℤ) :
    Subgroup (SplitGroup m) where
  carrier := {x | Triangular w x.val.val}
  one_mem' := triangular_one w
  mul_mem' := fun hx hy => triangular_mul hx hy
  inv_mem' := property_inv (p := fun x : SplitGroup m => Triangular w x.val.val)
    (triangular_one w) (fun _ _ => triangular_mul)

private theorem splitUnipotent_triangular (m : ℕ) (s : Side) :
    splitUnipotent m ≤ triangularSubgroup m (basisDegree s) := by
  apply (closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  change Triangular (basisDegree s) (rootGeneratorInGroup m r t).val.val
  simpa only [rootGeneratorInGroup_coe, one_mul] using rootCurve_triangular m s r 1
    (by simpa only [one_mul] using rootDegree_nonneg s hr) t

private theorem negativeBlock_triangular (m : ℕ) (s : Side) :
    splitSimpleBlock m s false ≤ triangularSubgroup m (basisDegree s) := by
  apply (closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  change Triangular (basisDegree s) (rootGeneratorInGroup m r t).val.val
  simpa only [rootGeneratorInGroup_coe, one_mul] using rootCurve_triangular m s r 1
    (by rw [rootDegree_zero_of_support s hr.1, mul_zero]) t

private theorem diagonalTorus_triangular (m : ℕ) (s : Side) :
    Parabolics.diagonalTorus m ≤ triangularSubgroup m (basisDegree s) := by
  intro x hx
  change x.val ∈ (Parabolics.diagonalTorusHom m).range at hx
  obtain ⟨u, hu⟩ := hx
  change Triangular (basisDegree s) x.val.val
  rw [← hu]
  change Triangular (basisDegree s) (Matrix.diagonal _)
  intro i j hij
  exact Matrix.diagonal_apply_ne _ (fun h => (ne_of_lt hij) (congrArg (basisDegree s) h))

private theorem negativeUnipotent_degreeZero (m : ℕ) (s : Side)
    (x : SplitGroup m) (hx : x ∈ splitNegativeUnipotent m) :
    Triangular (fun i => -basisDegree s i) x.val.val ∧
      ∃ y ∈ splitSimpleBlock m s false,
        degreeZero (fun i => -basisDegree s i) x.val.val = y.val.val := by
  let p (x : SplitGroup m) : Prop :=
    Triangular (fun i => -basisDegree s i) x.val.val ∧
      ∃ y ∈ splitSimpleBlock m s false,
        degreeZero (fun i => -basisDegree s i) x.val.val = y.val.val
  have hone : p 1 := ⟨triangular_one _, 1, one_mem _, degreeZero_one _⟩
  have hmul (x y : SplitGroup m) (hx : p x) (hy : p y) : p (x * y) := by
    obtain ⟨hxT, a, ha, hea⟩ := hx
    obtain ⟨hyT, b, hb, heb⟩ := hy
    refine ⟨triangular_mul hxT hyT, a * b, mul_mem ha hb, ?_⟩
    change degreeZero _ (x.val.val * y.val.val) = a.val.val * b.val.val
    rw [degreeZero_mul hxT hyT, hea, heb]
  change p x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · simpa only [rootGeneratorInGroup_coe, neg_one_mul] using rootCurve_triangular m s r (-1)
        (by have h := rootDegree_nonpos s hr; omega) t
    · by_cases hz : rootDegree s r = 0
      · exact ⟨rootGeneratorInGroup m r t,
          subset_closure ⟨r, t, ⟨support_of_rootDegree_zero s hr hz, hr⟩, rfl⟩,
          rootCurve_degreeZero_of_zero m s r hz t⟩
      · exact ⟨1, one_mem _, rootCurve_degreeZero_of_ne m s r hz t⟩
  | one => exact hone
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact property_inv hone hmul hx

/-- In the split matrix group, adjoining a negative simple block to the positive
Borel recovers precisely that block on intersection with the negative unipotent. -/
theorem splitNegativeUnipotent_inf_borel_sup_simpleBlock (m : ℕ)
    (hT : Parabolics.splitTorus m ≤ Parabolics.diagonalTorus m) (s : Side) :
    splitNegativeUnipotent m ⊓
      ((splitUnipotent m ⊔ Parabolics.splitTorus m) ⊔ splitSimpleBlock m s false) =
        splitSimpleBlock m s false := by
  apply le_antisymm
  · intro x hx
    have hp : (splitUnipotent m ⊔ Parabolics.splitTorus m) ⊔ splitSimpleBlock m s false ≤
        triangularSubgroup m (basisDegree s) :=
      sup_le (sup_le (splitUnipotent_triangular m s)
        (hT.trans (diagonalTorus_triangular m s))) (negativeBlock_triangular m s)
    obtain ⟨hn, y, hy, he⟩ := negativeUnipotent_degreeZero m s x hx.1
    have hz : degreeZero (fun i => -basisDegree s i) x.val.val = x.val.val := by
      apply degreeZero_eq_of_both hn
      have hpx : Triangular (basisDegree s) x.val.val := hp hx.2
      simpa only [neg_neg] using hpx
    rw [hz] at he
    have hxy : x = y := Subtype.ext (Units.ext he)
    exact hxy ▸ hy
  · refine le_inf ?_ le_sup_right
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    exact subset_closure ⟨r, t, hr.2, rfl⟩

/-- The fixed-point root intersection follows by containment in the split
parabolic; no equality between a fixed join and a join of fixed groups is used. -/
theorem oppositeUnipotent_inf_rootBorel_sup_simpleBlock {m : ℕ} (d : LocalBlockInput m)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) :
    ∀ s, oppositeUnipotent d ⊓ (rootBorel d ⊔ simpleBlock d s false) =
      simpleBlock d s false := by
  intro s
  apply le_antisymm
  · intro x hx
    have hp : rootBorel d ⊔ simpleBlock d s false ≤
        (Parabolics.splitBorel m ⊔ splitSimpleBlock m s false).subgroupOf d.fixedGroup :=
      sup_le (fun _ h => (le_sup_left : Parabolics.splitBorel m ≤
        Parabolics.splitBorel m ⊔ splitSimpleBlock m s false) h)
        (fun _ h => (le_sup_right : splitSimpleBlock m s false ≤
          Parabolics.splitBorel m ⊔ splitSimpleBlock m s false) h)
    have hs : x.val ∈ splitNegativeUnipotent m ⊓
        ((splitUnipotent m ⊔ Parabolics.splitTorus m) ⊔ splitSimpleBlock m s false) :=
      ⟨hx.1, hp hx.2⟩
    rw [splitNegativeUnipotent_inf_borel_sup_simpleBlock m hT.le s] at hs
    exact hs
  · exact le_inf (simpleBlock_negative_le d s) le_sup_right

end
end ReeF4.LocalBlockInput.PairRigidity
