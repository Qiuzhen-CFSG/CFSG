module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic


/-!
# Root-monomial matrices and triangular separation

A root-monomial matrix permutes the root lines with nonzero scalars and
preserves the Cartan subspace. This property is closed under multiplication
and, over finite fields, inversion. If `A * N = N' * B`, with `A` and `B`
unitriangular for a grading whose Cartan degree is zero, then `N = N'`.
Comparing root columns forces the relative permutation to increase every
height weakly. Summing the heights rules out strict increases; diagonal
entries then identify the scalars. Finally the degree-zero Cartan blocks agree.

This extends the binary argument in
`ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitSeparation`
by retaining the nonzero root-column scalars. It is the linear-algebra step
for uniqueness of the actual Bruhat middle matrix, including its torus part.
Source: GLS3 1.11.5 and 2.3.5, `refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`.
-/

@[expose] public section
open scoped Matrix
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry

/-- A matrix permutes root columns up to units and preserves the Cartan subspace. -/
def RootMonomial {C R K : Type*} [DecidableEq C] [DecidableEq R] [CommRing K]
    (A : Matrix (C ⊕ R) (C ⊕ R) K) (e : Equiv.Perm R) (s : R → Kˣ) : Prop :=
  (∀ i r, A i (.inr r) = if i = .inr (e r) then (s r : K) else 0) ∧
  (∀ r c, A (.inr r) (.inl c) = 0)

section Matrices
variable {C R K : Type*} [Fintype C] [Fintype R] [DecidableEq C] [DecidableEq R]
  [Field K]

omit [Fintype C] [Fintype R] in
theorem rootMonomial_one :
    RootMonomial (1 : Matrix (C ⊕ R) (C ⊕ R) K) (Equiv.refl R) (fun _ => 1) := by
  constructor
  · intro i r
    simp only [Matrix.one_apply, Equiv.refl_apply, Units.val_one]
    congr 1
  · intro r c; simp

theorem rootMonomial_mul {A B : Matrix (C ⊕ R) (C ⊕ R) K}
    {e f : Equiv.Perm R} {s t : R → Kˣ}
    (hA : RootMonomial A e s) (hB : RootMonomial B f t) :
    RootMonomial (A * B) (e * f) (fun r => s (f r) * t r) := by
  constructor
  · intro i r
    simp [Matrix.mul_apply, hB.1, hA.1, Equiv.Perm.mul_apply, mul_ite, ite_mul]
    congr 1
  · intro r c
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hA.2, hB.2]

omit [Fintype C] [Fintype R] in
theorem rootMonomial_row {A : Matrix (C ⊕ R) (C ⊕ R) K}
    {e : Equiv.Perm R} {s : R → Kˣ} (hA : RootMonomial A e s)
    (r : R) (j : C ⊕ R) :
    A (.inr r) j = if j = .inr (e.symm r) then (s (e.symm r) : K) else 0 := by
  cases j with
  | inl c => simp [hA.2]
  | inr q =>
    by_cases hq : q = e.symm r
    · subst q; simp [hA.1]
    · have h : r ≠ e q := by
        intro hh
        apply hq
        exact (e.symm_apply_eq.mpr hh).symm
      simp [hA.1, hq, h]

/-- The matrix condition, without a chosen permutation or scaling. -/
def IsRootMonomial (A : Matrix (C ⊕ R) (C ⊕ R) K) : Prop :=
  ∃ e s, RootMonomial A e s

omit [Fintype C] [Fintype R] in
theorem isRootMonomial_one :
    IsRootMonomial (1 : Matrix (C ⊕ R) (C ⊕ R) K) :=
  ⟨_, _, rootMonomial_one⟩

theorem IsRootMonomial.mul {A B : Matrix (C ⊕ R) (C ⊕ R) K}
    (hA : IsRootMonomial A) (hB : IsRootMonomial B) : IsRootMonomial (A * B) := by
  obtain ⟨e, s, he⟩ := hA
  obtain ⟨f, t, hf⟩ := hB
  exact ⟨_, _, rootMonomial_mul he hf⟩

theorem IsRootMonomial.pow {A : Matrix (C ⊕ R) (C ⊕ R) K}
    (hA : IsRootMonomial A) (k : ℕ) : IsRootMonomial (A ^ k) := by
  induction k with
  | zero => simpa using isRootMonomial_one (C := C) (R := R) (K := K)
  | succ k ih => simpa only [pow_succ] using ih.mul hA

/-- Over a finite field the same matrix condition is preserved by inverses. -/
theorem IsRootMonomial.inv [Finite K] {A : (Matrix (C ⊕ R) (C ⊕ R) K)ˣ}
    (hA : IsRootMonomial A.val) : IsRootMonomial A⁻¹.val := by
  have he : A⁻¹ = A ^ (orderOf A - 1) := by
    apply mul_left_cancel (a := A)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos A), pow_orderOf_eq_one]
  rw [he, Units.val_pow_eq_pow_val]
  exact hA.pow _

/-- Unitriangular factors cannot change a matrix with nonzero monomial root columns. -/
theorem rootMonomial_eq_of_triangular
    {A B N N' : Matrix (C ⊕ R) (C ⊕ R) K} {e f : Equiv.Perm R} {s t : R → Kˣ}
    (w : C ⊕ R → ℤ) (hw : ∀ c, w (.inl c) = 0)
    (hA : ∀ i j, w i ≤ w j → A i j = (1 : Matrix (C ⊕ R) (C ⊕ R) K) i j)
    (hB : ∀ i j, w i ≤ w j → B i j = (1 : Matrix (C ⊕ R) (C ⊕ R) K) i j)
    (hN : RootMonomial N e s) (hN' : RootMonomial N' f t)
    (he : A * N = N' * B) : N = N' := by
  let p : Equiv.Perm R := f.symm * e
  have hentry (r : R) : (s r : K) = (t (p r) : K) * B (.inr (p r)) (.inr r) := by
    have hh := congrFun (congrFun he (.inr (e r))) (.inr r)
    have hdiag := hA (.inr (e r)) (.inr (e r)) le_rfl
    simp only [Matrix.one_apply_eq] at hdiag
    simpa [Matrix.mul_apply, hN.1, rootMonomial_row hN', hdiag, p,
      mul_ite, ite_mul] using hh
  have hstrict (r : R) (hr : p r ≠ r) : w (.inr r) < w (.inr (p r)) := by
    by_contra hle
    have hz := hB (.inr (p r)) (.inr r) (by omega)
    simp only [Matrix.one_apply, Sum.inr.injEq, if_neg hr] at hz
    have hnz := hentry r
    rw [hz, mul_zero] at hnz
    exact Units.ne_zero _ hnz
  have hle (r : R) : w (.inr r) ≤ w (.inr (p r)) := by
    by_cases hr : p r = r
    · rw [hr]
    · exact le_of_lt (hstrict r hr)
  have hp (r : R) : p r = r := by
    by_contra hr
    have hsum := Finset.sum_lt_sum (fun q (_ : q ∈ Finset.univ) => hle q)
      ⟨r, Finset.mem_univ r, hstrict r hr⟩
    rw [Equiv.sum_comp p (fun q => w (.inr q))] at hsum
    exact lt_irrefl _ hsum
  have hef : e = f := by
    ext r
    have hh := congrArg f (hp r)
    simpa [p] using hh
  have hst (r : R) : (s r : K) = (t r : K) := by
    simpa only [hp r, hB _ _ le_rfl, Matrix.one_apply_eq, mul_one] using hentry r
  subst f
  have hAc (c d : C) : A (.inl c) (.inl d) = if c = d then 1 else 0 := by
    simpa [Matrix.one_apply] using hA (.inl c) (.inl d) (by simp [hw])
  have hBc (c d : C) : B (.inl c) (.inl d) = if c = d then 1 else 0 := by
    simpa [Matrix.one_apply] using hB (.inl c) (.inl d) (by simp [hw])
  ext i j
  cases j with
  | inr r => rw [hN.1, hN'.1, hst]
  | inl d =>
    cases i with
    | inr r => rw [hN.2, hN'.2]
    | inl c =>
      have hh := congrFun (congrFun he (.inl c)) (.inl d)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, hN.2, hN'.1, hAc, hBc] using hh
end Matrices
end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
