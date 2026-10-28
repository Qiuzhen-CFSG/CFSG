module

public import Theory.SpecificGroups.HigherLinear.SylowPointwiseInner.Actions
public import Mathlib.Algebra.CharP.Two

/-!
# Positive-root fixers among standard projective linear automorphisms

In every dimension at least three over a characteristic-two field, a standard
matrix automorphism fixing the positive roots pointwise is conjugation by a
highest-root element. The coefficient automorphism is trivial; inverse
transpose is excluded by two adjacent roots, which would force a zero row.

The quotient step uses uniqueness of involution lifts through the scalar
center in characteristic two. In particular it does not use trace one, which
would fail in even dimensions. Commuting with the positive matrix units then
forces the linear factor to be scalar plus the highest matrix unit.

This is the coordinate part of the Sylow-centralizer argument used in
Aschbacher–Smith B.1.13, printed p.74; standard actions follow GLS III,
Theorem 2.5.1 and §2.7. Coverage of arbitrary automorphisms remains a separate
input and is not asserted here.
-/

public section
open scoped MatrixGroups
open Matrix
namespace Matrix.HigherLinear.SylowPointwiseInner
variable {d : ℕ} {F : Type*} [Field F]
private theorem transvection_sq [CharP F 2] {i j : Fin d} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ^ 2 = 1 := by
  rw [pow_two, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

/-- Involutions have unique lifts through the actual scalar quotient in characteristic two. -/
theorem involution_eq_of_projective_eq [CharP F 2] [NeZero d] (x y : SL(d,F))
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (h : (QuotientGroup.mk x : PSL(d,F)) = QuotientGroup.mk y) : x = y := by
  have hc : y⁻¹ * x ∈ Subgroup.center SL(d,F) := QuotientGroup.eq.mp h.symm
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hv : x.val = r • y.val := by
    calc
      x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
      _ = y.val * Matrix.scalar (Fin d) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
      _ = r • y.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have hs : (1 : Matrix (Fin d) (Fin d) F) = (r * r) • 1 := by
    calc
      (1 : Matrix (Fin d) (Fin d) F) = (x * x).val := by rw [← pow_two, hx]; rfl
      _ = (r * r) • (y * y).val := by
        simp only [SpecialLinearGroup.coe_mul, hv, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul]
      _ = (r * r) • 1 := congrArg (fun z : SL(d,F) => (r * r) • z.val)
        (show y * y = 1 by simpa only [pow_two] using hy)
  have hr2 : r * r = 1 := by simpa using (congrArg (fun M => M 0 0) hs).symm
  have hr1 : r = 1 := by
    have he : (r + 1) * (r + 1) = 0 := by
      calc
        (r + 1) * (r + 1) = r * r + 1 + (r + r) := by ring
        _ = 0 := by rw [hr2, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have he' : r + 1 = 0 := (mul_self_eq_zero.mp he)
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he'
  apply Subtype.ext
  simpa [hr1] using hv


variable {n : ℕ}
private theorem centralizer_positive_shape (M : Matrix (Fin (n+2)) (Fin (n+2)) F)
    (h : ∀ i j : Fin (n+2), i < j → M * single i j 1 = single i j 1 * M) :
    M = M 0 0 • 1 + single 0 (Fin.last (n+1)) (M 0 (Fin.last (n+1))) := by
  have hcol (i j : Fin (n+2)) (hij : i < j) (a : Fin (n+2)) (hai : a ≠ i) :
      M a i = 0 := by
    have hh := congrArg (fun N => N a j) (h i j hij)
    simpa [single_mul_apply_of_ne, hai] using hh
  have hrow (i j : Fin (n+2)) (hij : i < j) (b : Fin (n+2)) (hbj : b ≠ j) :
      M j b = 0 := by
    have hh := congrArg (fun N => N i b) (h i j hij)
    simpa [mul_single_apply_of_ne, hbj] using hh.symm
  have hdiag (i : Fin (n+2)) : M i i = M 0 0 := by
    by_cases hi : i = 0
    · subst i; rfl
    have hh := congrArg (fun N => N 0 i) (h 0 i (Fin.pos_iff_ne_zero.mpr hi))
    simpa using hh.symm
  have hoff (i j : Fin (n+2)) (hij : i ≠ j)
      (hcorner : ¬ (i = 0 ∧ j = Fin.last (n+1))) : M i j = 0 := by
    by_cases hj : j = Fin.last (n+1)
    · have hi : i ≠ 0 := fun hi => hcorner ⟨hi, hj⟩
      exact hrow 0 i (Fin.pos_iff_ne_zero.mpr hi) j hij.symm
    · let k : Fin (n+2) := ⟨j.val + 1, by
        have : j.val < n+1 := Fin.val_lt_last hj
        omega⟩
      exact hcol j k (by change j.val < j.val + 1; omega) i hij
  have h0last : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  ext i j
  by_cases hij : i = j
  · subst j
    rw [hdiag]
    simp [Matrix.single_apply]
    aesop
  · by_cases hc : i = 0 ∧ j = Fin.last (n+1)
    · rcases hc with ⟨rfl, rfl⟩
      simp [h0last]
    · rw [hoff i j hij hc]
      have hc' : ¬ (0 = i ∧ Fin.last (n+1) = j) := by simpa only [eq_comm] using hc
      simp [hij, hc']


theorem fieldAction_root (σ : F ≃+* F) {i j : Fin d} (hij : i ≠ j) (c : F) :
    fieldAction d F σ (root d F hij c) = root d F hij (σ c) := by
  rw [root, fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext k l
  change σ ((1 + single i j c) k l) = (1 + single i j (σ c)) k l
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp

theorem graph_root {i j : Fin d} (hij : i ≠ j) (a : F) :
    graph d F (root d F hij a) = root d F hij.symm (-a) := by
  rw [root, graph_mk]
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_single]
  rw [h, SpecialLinearGroup.transvection_inv]
  rfl

/-- Projective conjugacy between roots gives the literal matrix-unit equation. -/
theorem conjugate_root_eq [CharP F 2] [NeZero d]
    (m : GL (Fin d) F) {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (a b : F) (h : linearConj d F m (root d F hij a) = root d F hkl b) :
    m.val * single i j a = single k l b * m.val := by
  have he : linearConjSL d F m (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hkl b := by
    apply involution_eq_of_projective_eq
    · rw [← map_pow, transvection_sq, map_one]
    · exact transvection_sq hkl b
    · exact h
  have hv (x : SL(d,F)) : (linearConjSL d F m x).val = m.val * x.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL d F m x)
  have he' := congrArg (fun x : SL(d,F) => x.val * m.val) he
  simpa only [hv, Matrix.mul_assoc, m.inv_val, mul_one,
    SpecialLinearGroup.transvection_coe, mul_add, add_mul, one_mul,
    add_right_inj] using he'

private theorem not_transpose_positive (m : GL (Fin (n+3)) F)
    (h : ∀ i j : Fin (n+3), i < j → m.val * single j i 1 = single i j 1 * m.val) :
    False := by
  let i : Fin (n+3) := ⟨0, by omega⟩
  let j : Fin (n+3) := ⟨1, by omega⟩
  let k : Fin (n+3) := ⟨2, by omega⟩
  have hij : i < j := by change (0:ℕ) < 1; omega
  have hjk : j < k := by change (1:ℕ) < 2; omega
  have hki : k ≠ i := by intro he; have := congrArg Fin.val he; change (2:ℕ) = 0 at this; omega
  have hrow (b : Fin (n+3)) : m.val k b = 0 := by
    by_cases hb : b = j
    · subst b
      have hh := congrArg (fun N => N k i) (h i j hij)
      simpa [single_mul_apply_of_ne, hki] using hh
    · have hh := congrArg (fun N => N j b) (h j k hjk)
      simpa [mul_single_apply_of_ne, hb] using hh.symm
  have hh := congrArg (fun N : Matrix (Fin (n+3)) (Fin (n+3)) F => N k k) m.val_inv
  simp [Matrix.mul_apply, hrow] at hh

private theorem linearConj_eq_of_scalar (m : GL (Fin d) F) (u : SL(d,F))
    (c : F) (hm : m.val = c • u.val) :
    linearConj d F m = MulAut.conj (QuotientGroup.mk u) := by
  ext x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(d,F)) x
  change QuotientGroup.mk (linearConjSL d F m y) =
    (QuotientGroup.mk (u * y * u⁻¹) : PSL(d,F))
  congr 1
  apply Subtype.ext
  have hv : (linearConjSL d F m y).val = m.val * y.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL d F m y)
  rw [hv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  apply (Units.mul_left_inj m).mp
  rw [Matrix.mul_assoc, m.inv_val, mul_one]
  rw [hm]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hi : u⁻¹.val * u.val = 1 := congrArg Subtype.val (inv_mul_cancel u)
  rw [hi, mul_one]

private theorem linear_field_fixer [CharP F 2] (m : GL (Fin (n+3)) F) (σ : F ≃+* F)
    (hfix : ∀ x ∈ upperRoots (n+3) F,
      (linearConj (n+3) F m * fieldAction (n+3) F σ) x = x) :
    ∃ z ∈ upperRoots (n+3) F,
      linearConj (n+3) F m * fieldAction (n+3) F σ = MulAut.conj z := by
  have hroot (i j : Fin (n+3)) (hij : i < j) (c : F) :
      m.val * single i j (σ c) = single i j c * m.val := by
    apply conjugate_root_eq m (ne_of_lt hij) (ne_of_lt hij)
    simpa only [MulAut.mul_apply, fieldAction_root] using
      hfix _ (root_mem_upperRoots (n+3) F hij c)
  have hshape := centralizer_positive_shape m.val (fun i j hij => by
    simpa only [map_one] using hroot i j hij 1)
  have hl0 : (Fin.last (n+2) : Fin (n+3)) ≠ 0 := by
    intro he
    have hh := congrArg Fin.val he
    simp at hh
  have ha : m.val 0 0 ≠ 0 := by
    intro ha
    have hrow (b : Fin (n+3)) : m.val (Fin.last (n+2)) b = 0 := by
      have hh := congrArg (fun M => M (Fin.last (n+2)) b) hshape
      simpa [ha, Matrix.single_apply, hl0.symm] using hh
    have hh := congrArg (fun M : Matrix (Fin (n+3)) (Fin (n+3)) F =>
      M (Fin.last (n+2)) (Fin.last (n+2))) m.val_inv
    simp [Matrix.mul_apply, hrow] at hh
  let j : Fin (n+3) := ⟨1, by omega⟩
  have h0j : (0 : Fin (n+3)) < j := by change (0:ℕ) < 1; omega
  have hj0 : j ≠ 0 := ne_of_gt h0j
  have hdiag : m.val j j = m.val 0 0 := by
    have hh := congrArg (fun M => M j j) hshape
    simpa [Matrix.single_apply, hj0.symm] using hh
  have hsigma : σ = 1 := by
    ext c
    have hh := congrArg (fun M => M 0 j) (hroot 0 j h0j c)
    simp only [mul_single_apply_same, single_mul_apply_same, hdiag] at hh
    change σ c = c
    exact mul_left_cancel₀ ha (hh.trans (mul_comm c (m.val 0 0)))
  let u := SpecialLinearGroup.transvection hl0.symm
    ((m.val 0 0)⁻¹ * m.val 0 (Fin.last (n+2)))
  have hm : m.val = m.val 0 0 • u.val := by
    calc
      m.val = m.val 0 0 • 1 + single 0 (Fin.last (n+2))
          (m.val 0 (Fin.last (n+2))) := hshape
      _ = m.val 0 0 • u.val := by
        simp [u, SpecialLinearGroup.transvection_coe, smul_add, Matrix.smul_single,
          smul_eq_mul, ha]
  refine ⟨QuotientGroup.mk u, ?_, ?_⟩
  · exact root_mem_upperRoots (n+3) F (Fin.pos_iff_ne_zero.mpr hl0) _
  · rw [hsigma, map_one, mul_one]
    exact linearConj_eq_of_scalar m u _ hm

private theorem not_graph_field_fixer [CharP F 2]
    (m : GL (Fin (n+3)) F) (σ : F ≃+* F)
    (hfix : ∀ x ∈ upperRoots (n+3) F,
      (linearConj (n+3) F m * fieldAction (n+3) F σ * graph (n+3) F) x = x) :
    False := by
  apply not_transpose_positive m
  intro i j hij
  apply conjugate_root_eq m (ne_of_lt hij).symm (ne_of_lt hij) 1 1
  simpa only [MulAut.mul_apply, graph_root, fieldAction_root, CharTwo.neg_eq, map_one]
    using hfix _ (root_mem_upperRoots (n+3) F hij 1)

/-- The exact coordinate fixer theorem, conditional only on a standard matrix form. -/
theorem standard_fixes_upperRoots_inner [CharP F 2] (hd : 3 ≤ d)
    (a : MulAut PSL(d,F)) (ha : HasStandardForm d F a)
    (hfix : ∀ x ∈ upperRoots d F, a x = x) :
    ∃ z ∈ upperRoots d F, a = MulAut.conj z := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n+3 := ⟨d-3, by omega⟩
  obtain ⟨m, σ, he | he⟩ := ha
  · subst a
    exact linear_field_fixer m σ hfix
  · subst a
    exact False.elim (not_graph_field_fixer m σ hfix)

end Matrix.HigherLinear.SylowPointwiseInner
