module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# Elementary specializations of the polynomial simple F4 action

The explicit `simpleSL2Matrix` sends the upper and lower elementary matrices to
Geck's literal positive and negative simple-root curves with the same parameter.
These polynomial identities hold over any commutative ring, hence in particular
over fields of characteristic two, independently of the multiplicative law.

For ordinary root columns, root-string positions turn the divided-power entries
into binomial coefficients, and the string degree bound gives the cubic root
curve formulas. The two opposite-root columns are checked separately using
reducedness; the Cartan columns retain their integral coefficients throughout.

Source: GLS3, Chapter 1, the parametrizations of Theorem 1.12.1 and Remark 1.12.10;
the integral root-string action is proved in `IntegralGeckConstruction.lean`.
-/

public section

open scoped BigOperators
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

noncomputable section

namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts

local instance simpleMorphismsElementaryCurvesNeg : InvolutiveNeg Root :=
  typeF4RootPairing.indexNeg

/- Root displacements agree with positions counted from the bottom of the string. -/
private lemma bot_shift {i : typeF4RootPairing_base.support} {j r : Root} {a : ℕ}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (hr : typeF4RootPairing.root r = typeF4RootPairing.root j + a • typeF4RootPairing.root i) :
    typeF4RootPairing.chainBotCoeff i r = typeF4RootPairing.chainBotCoeff i j + a := by
  induction a generalizing r with
  | zero =>
    have : r = j := typeF4RootPairing.root.injective (by simpa using hr)
    subst r
    simp
  | succ a ih =>
    have hamem : typeF4RootPairing.root j + a • typeF4RootPairing.root i ∈ Set.range typeF4RootPairing.root := by
      apply (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).2
      have := (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).1 ⟨r, hr⟩
      omega
    obtain ⟨l, hl⟩ := hamem
    have hlinl : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root l] := by
      rw [hl, add_comm, ← natCast_zsmul, LinearIndependent.pair_add_smul_right_iff]
      exact hlin
    have hrl : typeF4RootPairing.root r = typeF4RootPairing.root l + typeF4RootPairing.root i := by rw [hr, hl]; module
    rw [typeF4RootPairing.chainBotCoeff_of_add hlinl hrl, ih hl]
    omega

private lemma string_upper_iff {i : typeF4RootPairing_base.support} {j r : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) (a : ℕ) :
    typeF4RootPairing.root r = typeF4RootPairing.root j + a • typeF4RootPairing.root i ↔
      (typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i =
        typeF4RootPairing.root j + typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i) ∧
      typeF4RootPairing.chainBotCoeff i r = typeF4RootPairing.chainBotCoeff i j + a := by
  constructor
  · intro h
    have hb := bot_shift hlin h
    refine ⟨?_, hb⟩
    rw [h, hb]
    module
  · rintro ⟨h, hb⟩
    rw [hb, add_nsmul] at h
    apply add_right_cancel (b := typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i)
    calc
      _ = typeF4RootPairing.root j + (typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i + a • typeF4RootPairing.root i) := h
      _ = _ := by abel

private lemma string_lower_iff {i : typeF4RootPairing_base.support} {j r : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) (a : ℕ) :
    typeF4RootPairing.root r = typeF4RootPairing.root j - a • typeF4RootPairing.root i ↔
      (typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i =
        typeF4RootPairing.root j + typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i) ∧
      typeF4RootPairing.chainBotCoeff i r + a = typeF4RootPairing.chainBotCoeff i j := by
  constructor
  · intro h
    have hlinr : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root r] := by
      rw [h, sub_eq_add_neg, ← natCast_zsmul, ← neg_smul, add_comm,
        LinearIndependent.pair_add_smul_right_iff]
      exact hlin
    have hback : typeF4RootPairing.root j = typeF4RootPairing.root r + a • typeF4RootPairing.root i := by rw [h]; abel
    have hb := bot_shift hlinr hback
    refine ⟨?_, hb.symm⟩
    rw [hb, hback]
    module
  · rintro ⟨h, hb⟩
    rw [← hb, add_nsmul] at h
    apply (eq_sub_iff_add_eq).2
    apply add_right_cancel (b := typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i)
    calc
      _ = typeF4RootPairing.root r + (typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i + a • typeF4RootPairing.root i) := by abel
      _ = _ := h

private lemma string_bound {i : typeF4RootPairing_base.support} {j r : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (h : typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i =
        typeF4RootPairing.root j + typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i) :
    typeF4RootPairing.chainBotCoeff i r ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j := by
  have hr : typeF4RootPairing.root r = typeF4RootPairing.root j +
      ((typeF4RootPairing.chainBotCoeff i r : ℤ) - typeF4RootPairing.chainBotCoeff i j) • typeF4RootPairing.root i := by
    rw [eq_sub_of_add_eq h]
    simp only [sub_smul, natCast_zsmul]
    abel
  have hmem := (typeF4RootPairing.root_add_zsmul_mem_range_iff hlin).1 ⟨r, hr⟩
  simp only [Set.mem_Icc] at hmem
  omega

/- Recover the negative divided-power entries from their integral column actions. -/
private lemma negative_power_formula (i : typeF4RootPairing_base.support) (a : ℕ) :
    fDividedPower i (a + 2) = Matrix.of (fun row col : BasisIndex =>
      match row, col with
      | Sum.inr r, Sum.inr j =>
        if typeF4RootPairing.root r = typeF4RootPairing.root j -
            (a + 2) • typeF4RootPairing.root i then
          ((typeF4RootPairing.chainTopCoeff i j + a + 2).choose (a + 2) : ℤ)
        else 0
      | _, _ => 0) := by
  classical
  ext row col
  cases col with
  | inl j =>
    have h := congrFun (fDividedPower_add_two_mulVec_u i j a) row
    simpa [u] using h
  | inr j =>
    by_cases hmem : typeF4RootPairing.root j - (a + 2) • typeF4RootPairing.root i ∈
        Set.range typeF4RootPairing.root
    · obtain ⟨l, hl⟩ := hmem
      have h := congrFun (fDividedPower_add_two_mulVec_v a hl) row
      cases row with
      | inl r => simpa [v, Pi.single_apply] using h
      | inr r =>
        have heq : typeF4RootPairing.root r =
            typeF4RootPairing.root j - (a + 2) • typeF4RootPairing.root i ↔ r = l := by
          rw [← hl, EmbeddingLike.apply_eq_iff_eq]
        simp only [Matrix.of_apply, heq]
        simpa [v, Pi.single_apply] using h
    · have h := congrFun (fDividedPower_add_two_mulVec_v_zero i j a hmem) row
      cases row with
      | inl r => simpa [v] using h
      | inr r =>
        have hne : typeF4RootPairing.root r ≠ typeF4RootPairing.root j -
            (a + 2) • typeF4RootPairing.root i := fun hr => hmem ⟨r, hr⟩
        simp only [Matrix.of_apply, if_neg hne]
        simpa [v] using h
/- On a transvection the double sum has just one potentially nonzero term. -/
private lemma upper_entry {S : Type*} [CommRing S] (n q r : ℕ)
    (hr : r ≤ n) (t : S) :
    dividedStringEntry n q r (Matrix.transvection (0 : Fin 2) 1 t) =
      if q ≤ r then (r.choose q : S) * t ^ (r - q) else 0 := by
  classical
  unfold dividedStringEntry
  rw [Finset.sum_eq_single q]
  · by_cases hqr : q ≤ r
    · rw [Finset.sum_eq_single (r - q)]
      · simp [Matrix.transvection, Matrix.single, hqr]
      · intro b hb hne
        have hne' : q + b ≠ r := by omega
        simp [hne']
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · apply Eq.trans (Finset.sum_eq_zero ?_) (if_neg hqr).symm
      intro b hb
      have hne : q + b ≠ r := by omega
      simp [hne]
  · intro a ha hne
    have hqa : q - a ≠ 0 := by have := Finset.mem_range.mp ha; omega
    apply Finset.sum_eq_zero
    intro b hb
    simp [Matrix.transvection, Matrix.single, zero_pow hqa]
  · simp

private lemma lower_entry {S : Type*} [CommRing S] (n q r : ℕ) (t : S) :
    dividedStringEntry n q r (Matrix.transvection (1 : Fin 2) 0 t) =
      if r ≤ q then ((n-r).choose (q-r) : S) * t ^ (q-r) else 0 := by
  classical
  unfold dividedStringEntry
  have inner (a : ℕ) :
      (∑ b ∈ Finset.range (n - q + 1),
        if a + b = r then
          (r.choose a : S) * ((n - r).choose (q - a) : S) *
            (Matrix.transvection (1 : Fin 2) 0 t) 0 0 ^ a *
            (Matrix.transvection (1 : Fin 2) 0 t) 1 0 ^ (q - a) *
            (Matrix.transvection (1 : Fin 2) 0 t) 0 1 ^ b *
            (Matrix.transvection (1 : Fin 2) 0 t) 1 1 ^ (n - q - b)
        else 0) =
      if a = r then ((n-r).choose (q-a) : S) * t ^ (q-a) else 0 := by
    rw [Finset.sum_eq_single 0]
    · by_cases har : a = r <;>
        simp [har, Matrix.transvection, Matrix.single]
    · intro b hb hne
      simp [Matrix.transvection, Matrix.single, zero_pow hne]
    · simp
  simp_rw [inner]
  by_cases hrq : r ≤ q
  · rw [Finset.sum_eq_single r]
    · simp [hrq]
    · intro a ha hne
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hrq]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : a ≠ r := by have := Finset.mem_range.mp ha; omega
    simp [hne]

/- The uniform root-string degree bound truncates these entries at degree three. -/
private lemma upper_cubic {S : Type*} [CommRing S] (q p s : ℕ)
    (hqp : q + p ≤ 3) (hs : s ≤ q + p) (t : S) :
    dividedStringEntry (q + p) q s (Matrix.transvection (0 : Fin 2) 1 t) =
      (if s = q then 1 else 0) +
      t * (if s = q + 1 then (q + 1 : S) else 0) +
      t ^ 2 * (if s = q + 2 then ((q + 2).choose 2 : S) else 0) +
      t ^ 3 * (if s = q + 3 then ((q + 3).choose 3 : S) else 0) := by
  rw [upper_entry _ _ _ hs]
  by_cases hqs : q ≤ s
  · have hcases : s = q ∨ s = q + 1 ∨ s = q + 2 ∨ s = q + 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simp [mul_comm]
    all_goals rw [Nat.choose_symm_add]
  · have h0 : s ≠ q := by omega
    have h1 : s ≠ q + 1 := by omega
    have h2 : s ≠ q + 2 := by omega
    have h3 : s ≠ q + 3 := by omega
    simp [hqs, h0, h1, h2, h3]

private lemma lower_cubic {S : Type*} [CommRing S] (q p s : ℕ)
    (hqp : q + p ≤ 3) (hs : s ≤ q + p) (t : S) :
    dividedStringEntry (q + p) q s (Matrix.transvection (1 : Fin 2) 0 t) =
      (if s = q then 1 else 0) +
      t * (if s + 1 = q then (p + 1 : S) else 0) +
      t ^ 2 * (if s + 2 = q then ((p + 2).choose 2 : S) else 0) +
      t ^ 3 * (if s + 3 = q then ((p + 3).choose 3 : S) else 0) := by
  rw [lower_entry]
  by_cases hsq : s ≤ q
  · have hcases : q = s ∨ q = s + 1 ∨ q = s + 2 ∨ q = s + 3 := by omega
    have hsub (a : ℕ) : s + a + p - s = p + a := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simp [hsub, mul_comm]
  · have h0 : s ≠ q := by omega
    have h1 : s + 1 ≠ q := by omega
    have h2 : s + 2 ≠ q := by omega
    have h3 : s + 3 ≠ q := by omega
    simp [hsq, h0, h1, h2, h3]

/- Compare ordinary root columns using their positions, without multiplying matrices. -/
private lemma upper_root_entry {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (j r : Root)
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (t : S) :
    (if typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j •
          typeF4RootPairing.root i = typeF4RootPairing.root j +
          typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i then
      dividedStringEntry
        (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j)
        (typeF4RootPairing.chainBotCoeff i j) (typeF4RootPairing.chainBotCoeff i r)
        (Matrix.transvection (0 : Fin 2) 1 t) else 0) =
      (if r = j then 1 else 0) +
      t * (if typeF4RootPairing.root r = typeF4RootPairing.root i +
          typeF4RootPairing.root j then (typeF4RootPairing.chainBotCoeff i j + 1 : S) else 0) +
      t ^ 2 * (if typeF4RootPairing.root r = typeF4RootPairing.root j +
          2 • typeF4RootPairing.root i then
          ((typeF4RootPairing.chainBotCoeff i j + 2).choose 2 : S) else 0) +
      t ^ 3 * (if typeF4RootPairing.root r = typeF4RootPairing.root j +
          3 • typeF4RootPairing.root i then
          ((typeF4RootPairing.chainBotCoeff i j + 3).choose 3 : S) else 0) := by
  classical
  have h0 := string_upper_iff (r := r) hlin 0
  have h1 := string_upper_iff (r := r) hlin 1
  simp only [zero_smul, add_zero, EmbeddingLike.apply_eq_iff_eq] at h0
  simp only [one_smul] at h1
  rw [add_comm (typeF4RootPairing.root j) (typeF4RootPairing.root i)] at h1
  simp only [h0, h1, string_upper_iff hlin 2, string_upper_iff hlin 3]
  by_cases h : typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j •
      typeF4RootPairing.root i = typeF4RootPairing.root j +
      typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i
  · simp only [h, ite_true, true_and]
    exact upper_cubic _ _ _ typeF4RootPairing.chainBotCoeff_add_chainTopCoeff_le_three
      (string_bound hlin h) t
  · simp only [h, false_and, ite_false, mul_zero, add_zero]

private lemma lower_root_entry {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (j r : Root)
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (t : S) :
    (if typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j •
          typeF4RootPairing.root i = typeF4RootPairing.root j +
          typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i then
      dividedStringEntry
        (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j)
        (typeF4RootPairing.chainBotCoeff i j) (typeF4RootPairing.chainBotCoeff i r)
        (Matrix.transvection (1 : Fin 2) 0 t) else 0) =
      (if r = j then 1 else 0) +
      t * (if typeF4RootPairing.root r = typeF4RootPairing.root j -
          typeF4RootPairing.root i then (typeF4RootPairing.chainTopCoeff i j + 1 : S) else 0) +
      t ^ 2 * (if typeF4RootPairing.root r = typeF4RootPairing.root j -
          2 • typeF4RootPairing.root i then
          ((typeF4RootPairing.chainTopCoeff i j + 2).choose 2 : S) else 0) +
      t ^ 3 * (if typeF4RootPairing.root r = typeF4RootPairing.root j -
          3 • typeF4RootPairing.root i then
          ((typeF4RootPairing.chainTopCoeff i j + 3).choose 3 : S) else 0) := by
  classical
  have h0 := string_lower_iff (r := r) hlin 0
  have h1 := string_lower_iff (r := r) hlin 1
  simp only [zero_smul, sub_zero, add_zero, EmbeddingLike.apply_eq_iff_eq] at h0
  simp only [one_smul] at h1
  simp only [h0, h1, string_lower_iff hlin 2, string_lower_iff hlin 3]
  by_cases h : typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j •
      typeF4RootPairing.root i = typeF4RootPairing.root j +
      typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i
  · simp only [h, ite_true, true_and]
    exact lower_cubic _ _ _ typeF4RootPairing.chainBotCoeff_add_chainTopCoeff_le_three
      (string_bound hlin h) t
  · simp only [h, false_and, ite_false, mul_zero, add_zero]
private lemma root_ne_nsmul (i r : Root) (a : ℕ) [a.AtLeastTwo] :
    typeF4RootPairing.root r ≠ a • typeF4RootPairing.root i :=
  fun h => typeF4RootPairing.nsmul_notMem_range_root ⟨r, h⟩

private lemma root_ne_neg_nsmul (i r : Root) (a : ℕ) [a.AtLeastTwo] :
    typeF4RootPairing.root r ≠ -(a • typeF4RootPairing.root i) := by
  simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, smul_neg] using root_ne_nsmul (-i) r a

/-- The upper elementary matrix has exactly the positive simple-root parametrization.
The equality holds over every commutative coefficient ring. -/
lemma simpleSL2Matrix_upper {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (t : S) :
    simpleSL2Matrix i (Matrix.transvection (0 : Fin 2) 1 t) =
      RootPairing.SimpleGeckGroup.positiveMatrix i t := by
  classical
  ext (r | r) (j | j)
  · simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix,
    RootPairing.SimpleGeckGroup.positiveMatrix_formula,
      eDividedPower, eMatrix, Matrix.transvection, Matrix.single, Matrix.one_apply]
  · by_cases hr : r = i <;>
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix,
        RootPairing.SimpleGeckGroup.positiveMatrix_formula,
        eDividedPower, eMatrix, Matrix.transvection, Matrix.single, hr, mul_ite]
  · simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix,
    RootPairing.SimpleGeckGroup.positiveMatrix_formula,
      eDividedPower, eMatrix, Matrix.transvection, Matrix.single, mul_ite, mul_comm]
  · by_cases hj : j = (i : Root)
    · subst j
      have h2 : typeF4RootPairing.root i + 2 • typeF4RootPairing.root i =
          3 • typeF4RootPairing.root i := by module
      have h3 : typeF4RootPairing.root i + 3 • typeF4RootPairing.root i =
          4 • typeF4RootPairing.root i := by module
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix,
        RootPairing.SimpleGeckGroup.positiveMatrix_formula,
        eDividedPower, eMatrix, Matrix.transvection, Matrix.single, Matrix.one_apply,
        h2, h3, ← two_nsmul, root_ne_nsmul]
    by_cases hjn : j = typeF4RootPairing.reflectionPerm i i
    · subst j
      have h2 : -typeF4RootPairing.root i + 2 • typeF4RootPairing.root i =
          typeF4RootPairing.root i := by module
      have h3 : -typeF4RootPairing.root i + 3 • typeF4RootPairing.root i =
          2 • typeF4RootPairing.root i := by module
      have hb : typeF4RootPairing.chainTopCoeff i i = 0 :=
        typeF4RootPairing.chainTopCoeff_of_not_linearIndependent (by
          intro h
          have heq : (0 : Fin 2) = 1 := h.injective (by simp)
          exact zero_ne_one heq)
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix,
        RootPairing.SimpleGeckGroup.positiveMatrix_formula,
        eDividedPower, eMatrix, Matrix.transvection, Matrix.single, Matrix.one_apply,
        hj, h2, h3, hb, root_ne_nsmul, typeF4RootPairing.ne_zero, mul_ite]
      ring
    have hlin : LinearIndependent ℝ
        ![typeF4RootPairing.root i, typeF4RootPairing.root j] := by
      apply RootPairing.IsReduced.linearIndependent typeF4RootPairing (Ne.symm hj)
      intro h
      apply hjn
      exact (typeF4RootPairing.root_eq_neg_iff).mp (neg_eq_iff_eq_neg.mpr h).symm
    simpa [-typeF4RootPairing_root, -nsmul_eq_mul, Int.cast_ite, Nat.add_assoc, simpleSL2Matrix,
      RootPairing.SimpleGeckGroup.positiveMatrix_formula,
      eDividedPower, eMatrix, Matrix.transvection, Matrix.single, Matrix.one_apply,
      hj, hjn] using upper_root_entry i j r hlin t

/-- The lower elementary matrix has exactly the negative simple-root parametrization.
In particular, characteristic two requires no division or change of parameter. -/
lemma simpleSL2Matrix_lower {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (t : S) :
    simpleSL2Matrix i (Matrix.transvection (1 : Fin 2) 0 t) =
      RootPairing.SimpleGeckGroup.negativeMatrix i t := by
  classical
  have hf2 := negative_power_formula i 0
  have hf3 := negative_power_formula i 1
  simp only [RootPairing.SimpleGeckGroup.negativeMatrix_formula,
    fDividedPower_one, hf2, hf3]
  ext (r | r) (j | j)
  · simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix, fMatrix, Matrix.transvection,
    Matrix.single, Matrix.one_apply]
  · by_cases hr : r = i <;>
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix, fMatrix, Matrix.transvection,
        Matrix.single, hr, mul_ite]
  · simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix, fMatrix, Matrix.transvection,
    Matrix.single,
      mul_ite, mul_comm]
  · by_cases hj : j = (i : Root)
    · subst j
      have h2 : typeF4RootPairing.root i - 2 • typeF4RootPairing.root i =
          -typeF4RootPairing.root i := by module
      have h3 : typeF4RootPairing.root i - 3 • typeF4RootPairing.root i =
          -(2 • typeF4RootPairing.root i) := by module
      have hp : typeF4RootPairing.chainTopCoeff i i = 0 :=
        typeF4RootPairing.chainTopCoeff_of_not_linearIndependent (by
          intro h
          have heq : (0 : Fin 2) = 1 := h.injective (by simp)
          exact zero_ne_one heq)
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix, fMatrix, Matrix.transvection,
        Matrix.single,
        Matrix.one_apply, h2, h3, hp, root_ne_neg_nsmul, typeF4RootPairing.ne_zero,
        mul_ite]
    by_cases hjn : j = typeF4RootPairing.reflectionPerm i i
    · subst j
      have h1 : -typeF4RootPairing.root i - typeF4RootPairing.root i =
          -(2 • typeF4RootPairing.root i) := by module
      have h2 : -typeF4RootPairing.root i - 2 • typeF4RootPairing.root i =
          -(3 • typeF4RootPairing.root i) := by module
      have h3 : -typeF4RootPairing.root i - 3 • typeF4RootPairing.root i =
          -(4 • typeF4RootPairing.root i) := by module
      simp [-typeF4RootPairing_root, -nsmul_eq_mul, simpleSL2Matrix, fMatrix, Matrix.transvection,
        Matrix.single,
        Matrix.one_apply, hj, h1, h2, h3, root_ne_neg_nsmul]
    have hlin : LinearIndependent ℝ
        ![typeF4RootPairing.root i, typeF4RootPairing.root j] := by
      apply RootPairing.IsReduced.linearIndependent typeF4RootPairing (Ne.symm hj)
      intro h
      apply hjn
      exact (typeF4RootPairing.root_eq_neg_iff).mp (neg_eq_iff_eq_neg.mpr h).symm
    simpa [-typeF4RootPairing_root, -nsmul_eq_mul, Int.cast_ite, Nat.add_assoc, simpleSL2Matrix,
      fMatrix, Matrix.transvection, Matrix.single,
      Matrix.one_apply, hj, hjn]
      using lower_root_entry i j r hlin t

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
