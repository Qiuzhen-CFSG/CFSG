module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitSeparation.Grading

/-!
# Uniqueness of the binary split Bruhat middle representative

The actual simple Tits matrices permute root basis vectors in characteristic
two and preserve the Cartan subspace. The same holds for their generated
subgroup. Positive root matrices are unitriangular for the height grading.

In an equality `a * n = n' * b` with `a, b ∈ U`, a root-column comparison
forces the permutation `n'⁻¹ n` to weakly increase every root height. Summing
heights over the finite root set rules out a strict increase, and the identity
entries at equal heights force this permutation to be trivial. Comparing the
degree-zero Cartan blocks then gives equality of the entire matrices.
Consequently distinct actual Weyl representatives have disjoint `U` double
cosets. Restricting the right factors to `U ∩ n⁻¹U⁻n` gives the required
middle-representative uniqueness for split Bruhat descent.

The characteristic-two root-vector calculation eliminates the signs directly;
it is compatible with the trivial binary split torus of
`RootData.splitTorus_zero` and does not require a torus quotient argument.

Source: GLS3, Bruhat normal forms 1.11.5 and 2.3.5,
`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open ReeF4.LargeLocalSeeds SplitSeparation
noncomputable section

/-- Root columns are a permutation matrix, and Cartan columns stay in the Cartan block. -/
private def RootMonomial {C R K : Type*} [DecidableEq C] [DecidableEq R] [Zero K] [One K]
    (A : Matrix (C ⊕ R) (C ⊕ R) K) (e : Equiv.Perm R) : Prop :=
  (∀ i r, A i (.inr r) = if i = .inr (e r) then 1 else 0) ∧
  (∀ r c, A (.inr r) (.inl c) = 0)

section Matrices
variable {C R K : Type*} [Fintype C] [Fintype R] [DecidableEq C] [DecidableEq R]
  [Field K]

omit [Fintype C] [Fintype R] in
private theorem rootMonomial_one :
    RootMonomial (1 : Matrix (C ⊕ R) (C ⊕ R) K) (Equiv.refl R) := by
  constructor
  · intro i r
    simp only [Matrix.one_apply, Equiv.refl_apply]
    congr 1
  · intro r c; simp

private theorem rootMonomial_mul {A B : Matrix (C ⊕ R) (C ⊕ R) K}
    {e f : Equiv.Perm R} (hA : RootMonomial A e) (hB : RootMonomial B f) :
    RootMonomial (A * B) (e * f) := by
  constructor
  · intro i r
    simp [Matrix.mul_apply, hB.1, hA.1, Equiv.Perm.mul_apply]
    congr 1
  · intro r c
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hA.2, hB.2]

omit [Fintype C] [Fintype R] in
private theorem rootMonomial_row {A : Matrix (C ⊕ R) (C ⊕ R) K}
    {e : Equiv.Perm R} (hA : RootMonomial A e) (r : R) (j : C ⊕ R) :
    A (.inr r) j = if j = .inr (e.symm r) then 1 else 0 := by
  cases j with
  | inl c => simp [hA.2]
  | inr s => simp [hA.1, Equiv.eq_symm_apply, eq_comm]

private theorem rootMonomial_eq_of_triangular
    {A B N N' : Matrix (C ⊕ R) (C ⊕ R) K} {e f : Equiv.Perm R}
    (w : C ⊕ R → ℤ) (hw : ∀ c, w (.inl c) = 0)
    (hA : ∀ i j, w i ≤ w j → A i j = (1 : Matrix (C ⊕ R) (C ⊕ R) K) i j)
    (hB : ∀ i j, w i ≤ w j → B i j = (1 : Matrix (C ⊕ R) (C ⊕ R) K) i j)
    (hN : RootMonomial N e) (hN' : RootMonomial N' f)
    (he : A * N = N' * B) : N = N' := by
  let p : Equiv.Perm R := f.symm * e
  -- The diagonal entry in a root column is unchanged by the left factor.
  have hentry (r : R) : B (.inr (p r)) (.inr r) = 1 := by
    have hh := congrFun (congrFun he (.inr (e r))) (.inr r)
    have hdiag := hA (.inr (e r)) (.inr (e r)) le_rfl
    simp only [Matrix.one_apply_eq] at hdiag
    simpa [Matrix.mul_apply, hN.1, rootMonomial_row hN', hdiag, p] using hh.symm
  have hstrict (r : R) (hr : p r ≠ r) : w (.inr r) < w (.inr (p r)) := by
    by_contra hle
    have hz := hB (.inr (p r)) (.inr r) (by omega)
    simp only [Matrix.one_apply, Sum.inr.injEq, if_neg hr, hentry] at hz
    exact one_ne_zero hz
  have hle (r : R) : w (.inr r) ≤ w (.inr (p r)) := by
    by_cases hr : p r = r
    · rw [hr]
    · exact le_of_lt (hstrict r hr)
  -- A permutation cannot strictly increase one height while decreasing none.
  have hp (r : R) : p r = r := by
    by_contra hr
    have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hle s)
      ⟨r, Finset.mem_univ r, hstrict r hr⟩
    rw [Equiv.sum_comp p (fun s => w (.inr s))] at hsum
    exact lt_irrefl _ hsum
  have hef : e = f := by
    ext r
    have hh := congrArg f (hp r)
    simpa [p] using hh
  subst f
  -- The Cartan block has degree zero and is unchanged on both sides.
  have hAc (c d : C) : A (.inl c) (.inl d) = if c = d then 1 else 0 := by
    simpa [Matrix.one_apply] using hA (.inl c) (.inl d) (by simp [hw])
  have hBc (c d : C) : B (.inl c) (.inl d) = if c = d then 1 else 0 := by
    simpa [Matrix.one_apply] using hB (.inl c) (.inl d) (by simp [hw])
  ext i j
  cases j with
  | inr r => rw [hN.1, hN'.1]
  | inl d =>
    cases i with
    | inr r => rw [hN.2, hN'.2]
    | inl c =>
      have hh := congrFun (congrFun he (.inl c)) (.inl d)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, hN.2, hN'.1, hAc, hBc] using hh

end Matrices

private theorem simpleWord_matrix (i : Fin 4) :
    (simpleWord 0 [i]).val.val =
      specializeMatrix (titsLift (typeF4RootPairing_baseEquiv i)) := by
  have h := congrArg Units.val (simpleWord_coe 0 [i])
  simpa [rootCurveTitsWord, titsWord] using h

private theorem simpleWord_rootMonomial (i : Fin 4) :
    RootMonomial (simpleWord 0 [i]).val.val
      (typeF4RootPairing.reflectionPerm (typeF4RootPairing_baseEquiv i)) := by
  classical
  rw [simpleWord_matrix]
  constructor
  · intro a r
    have h := congrFun (titsLift_mulVec_v (typeF4RootPairing_baseEquiv i) r) a
    have hc : titsLift (typeF4RootPairing_baseEquiv i) a (.inr r) =
        if a = .inr (typeF4RootPairing.reflectionPerm
            (typeF4RootPairing_baseEquiv i) r) then
          (-1 : ℤ) ^ typeF4RootPairing.chainBotCoeff (typeF4RootPairing_baseEquiv i) r
        else 0 := by
      simp [v, Pi.single_apply] at h
      convert h using 1
      congr 1
    simp only [specializeMatrix, Matrix.map_apply, hc]
    split_ifs <;> simp [CharTwo.neg_eq]
  · intro r c
    have h := congrFun (titsLift_mulVec_u (typeF4RootPairing_baseEquiv i) c) (.inr r)
    have hc : titsLift (typeF4RootPairing_baseEquiv i) (.inr r) (.inl c) = 0 := by
      simpa [u, Pi.single_apply] using h
    simp [specializeMatrix, hc]

private theorem splitWeyl_rootMonomial {n : SplitGroup 0}
    (hn : n ∈ splitWeylSubgroup) : ∃ e, RootMonomial n.val.val e := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨i, rfl⟩ := hn
    exact ⟨_, simpleWord_rootMonomial i⟩
  | one => exact ⟨_, rootMonomial_one⟩
  | mul n m _ _ hn hm =>
    obtain ⟨e, he⟩ := hn
    obtain ⟨f, hf⟩ := hm
    exact ⟨e * f, rootMonomial_mul he hf⟩
  | inv n _ hn =>
    obtain ⟨e, he⟩ := hn
    have hpow (k : ℕ) : ∃ f, RootMonomial (n ^ k).val.val f := by
      induction k with
      | zero => exact ⟨_, rootMonomial_one⟩
      | succ k ih =>
        obtain ⟨f, hf⟩ := ih
        rw [pow_succ]
        exact ⟨f * e, rootMonomial_mul hf he⟩
    have heq : n⁻¹ = n ^ (orderOf n - 1) := by
      apply mul_left_cancel (a := n)
      rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos n), pow_orderOf_eq_one]
    rw [heq]
    exact hpow _

/-- Unitriangular multiplication on either side cannot change a binary split Weyl matrix. -/
theorem splitWeyl_eq_of_unipotent_mul {a n n' b : SplitGroup 0}
    (ha : a ∈ splitUnipotent 0) (hn : n ∈ splitWeylSubgroup)
    (hn' : n' ∈ splitWeylSubgroup) (hb : b ∈ splitUnipotent 0)
    (he : a * n = n' * b) : n = n' := by
  obtain ⟨e, hN⟩ := splitWeyl_rootMonomial hn
  obtain ⟨f, hN'⟩ := splitWeyl_rootMonomial hn'
  have hm : a.val.val * n.val.val = n'.val.val * b.val.val :=
    congrArg (fun x : SplitGroup 0 => x.val.val) he
  have h := rootMonomial_eq_of_triangular basisDegree basisDegree_cartan
    (splitUnipotent_entry ha) (splitUnipotent_entry hb) hN hN' hm
  exact Subtype.ext (Units.ext h)

/-- Distinct actual Weyl representatives have disjoint positive-unipotent double cosets. -/
theorem middle_representative_unique_of_unipotent {u n v u' n' v' : SplitGroup 0}
    (hu : u ∈ splitUnipotent 0) (hn : n ∈ splitWeylSubgroup)
    (hv : v ∈ splitUnipotent 0) (hu' : u' ∈ splitUnipotent 0)
    (hn' : n' ∈ splitWeylSubgroup) (hv' : v' ∈ splitUnipotent 0)
    (he : u * n * v = u' * n' * v') : n = n' := by
  apply splitWeyl_eq_of_unipotent_mul
    ((splitUnipotent 0).mul_mem ((splitUnipotent 0).inv_mem hu') hu) hn hn'
    ((splitUnipotent 0).mul_mem hv' ((splitUnipotent 0).inv_mem hv))
  calc
    (u'⁻¹ * u) * n = u'⁻¹ * (u * n * v) * v⁻¹ := by group
    _ = n' * (v' * v⁻¹) := by rw [he]; group

/-- Uniqueness of the middle matrix in the binary split Bruhat normal form.
The right factors use precisely `U ∩ n⁻¹U⁻n`, as in GLS3 1.11.5 and 2.3.5. -/
theorem middle_representative_unique {u n v u' n' v' : SplitGroup 0}
    (hu : u ∈ splitUnipotent 0) (hn : n ∈ splitWeylSubgroup)
    (hv : v ∈ rightUnipotent n) (hu' : u' ∈ splitUnipotent 0)
    (hn' : n' ∈ splitWeylSubgroup) (hv' : v' ∈ rightUnipotent n')
    (he : u * n * v = u' * n' * v') : n = n' :=
  middle_representative_unique_of_unipotent hu hn hv.1 hu' hn' hv'.1 he

end
end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
