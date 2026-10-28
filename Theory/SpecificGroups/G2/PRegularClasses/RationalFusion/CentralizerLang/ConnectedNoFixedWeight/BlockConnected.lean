module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockModel
public import Theory.AlgebraicGroup.Instance.SLConnected

/-!
# Connectedness of diagonal centralizers in SL₃

Over an algebraically closed field, the centralizer of every determinant-one
nonzero diagonal matrix in SL₃ is connected. All weight multiplicities are
included, with no characteristic restriction.

For three distinct weights the centralizer is the determinant-one diagonal
torus. For a repeated pair, write a centralizing matrix as `diag(B,c)`.
The determinant identity puts `B * diag(c,1)` in SL₂, giving a factorization
into an embedded SL₂ matrix and `diag(c⁻¹,1,c)`. Both factors lie in the
identity component, by explicit polynomial maps from SL₂ and a diagonal
torus. Coordinate permutations transport this argument to any repeated pair.
For scalar diagonals, a polynomial surjection from SL₃ proves connectedness.

This is the linear-group prerequisite in the octonion realization of the G₂
case of Steinberg 8.5 and 12.5, `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
noncomputable section
set_option linter.unusedSimpArgs false
variable {K : Type*} [Field K] [IsAlgClosed K]

private def blockPoint (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (A : Matrix.SpecialLinearGroup (Fin 3) K)
    (hA : ∀ i j, (d i : K) * A.1 i j = (d j : K) * A.1 i j) :
    Variety.Point (blockVariety d hd) :=
  (blockPointEquiv d hd).symm ⟨A, (mem_diagonalSL_centralizer_iff d hd A).mpr hA⟩

private lemma blockPoint_entry (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (A : Matrix.SpecialLinearGroup (Fin 3) K) (hA) (i j : Fin 3) :
    (blockPoint d hd A hA).val (ULift.up (i,j)) = A.1 i j := rfl

omit [IsAlgClosed K] in
private lemma point_mem_component {V : Variety K} (hV : Variety.IsConnected V)
    {G : Variety K} [AlgebraicGroup G] (f : Variety.Morphism V G)
    (a : Variety.Point V) (ha : f.toFun a = 1) (x : Variety.Point V) :
    f.toFun x ∈ Theory.AlgebraicGroup.identityComponent G := by
  have hrange : _root_.IsConnected (Set.range f.toFun) := by
    simpa only [Set.image_univ] using hV.image f.toFun f.continuous.continuousOn
  exact hrange.subset_connectedComponent ⟨a, ha⟩ ⟨x, rfl⟩

private lemma scalar_connected (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (heq : ∀ i, d i = d 0) : Variety.IsConnected (blockVariety d hd) := by
  let f : Variety.Morphism (slVariety K 3) (blockVariety d hd) :=
    { toFun := fun x => blockPoint d hd (slPointEquiv 3 x) (by
        intro i j
        rw [heq i, heq j])
      regular := fun i => ⟨MvPolynomial.X i, fun x => by
        cases i with | up p =>
          rcases p with ⟨r,s⟩
          rw [blockPoint_entry]
          change x.val (ULift.up (r,s)) = _
          simp [evalPolynomial]⟩ }
  have hsurj : Function.Surjective f.toFun := by
    intro x
    refine ⟨(slPointEquiv 3).symm (blockPointEquiv d hd x).val, ?_⟩
    apply (blockPointEquiv d hd).injective
    apply Subtype.ext
    simpa only [f, blockPoint, MulEquiv.apply_symm_apply] using
      (slPointEquiv 3).apply_symm_apply (blockPointEquiv d hd x).val
  have hc := (slVariety_isConnected (k := K) 3).image f.toFun f.continuous.continuousOn
  unfold Variety.IsConnected
  simpa only [Set.image_univ, hsurj.range_eq] using hc

private def torusWeights (z : Fin 2 → Kˣ) : Fin 3 → Kˣ := ![z 0, z 1, (z 0 * z 1)⁻¹]

omit [IsAlgClosed K] in
private lemma torusWeights_prod (z : Fin 2 → Kˣ) : ∏ i, torusWeights z i = 1 := by
  simp [torusWeights, Fin.prod_univ_three, mul_assoc]

private def diagonalPoint (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (z : Fin 2 → Kˣ) : Variety.Point (blockVariety d hd) :=
  blockPoint d hd (diagonalSL (torusWeights z) (torusWeights_prod z)) (by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [diagonalSL, Matrix.diagonal_apply, h])

private def diagonalMap (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) :
    Variety.Morphism (dVariety K 2) (blockVariety d hd) where
  toFun z := diagonalPoint d hd (dPointEquiv 2 z)
  regular := by
    rintro ⟨⟨i,j⟩⟩
    let X (i : Fin 2) : MvPolynomial (dVariety K 2).Coordinates K :=
      MvPolynomial.X (Sum.inl (ULift.up i))
    let Y (i : Fin 2) : MvPolynomial (dVariety K 2).Coordinates K :=
      MvPolynomial.X (Sum.inr (ULift.up i))
    refine ⟨(Matrix.diagonal ![X 0, X 1, Y 0 * Y 1]) i j, ?_⟩
    intro z
    change (diagonalSL (torusWeights (dPointEquiv 2 z)) (torusWeights_prod _)).1 i j = _
    fin_cases i <;> fin_cases j <;>
      simp [diagonalSL, torusWeights, X, Y, evalPolynomial, dPointEquiv,
        dPointEntry, dPointEntryInv, dPoint_entry_inv]
    exact mul_comm _ _

private lemma diagonal_mem (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (z : Fin 2 → Kˣ) : diagonalPoint d hd z ∈
      Theory.AlgebraicGroup.identityComponent (blockVariety d hd) := by
  have hone : (diagonalMap d hd).toFun ((dPointEquiv 2).symm 1) = 1 := by
    apply (blockPointEquiv d hd).injective
    apply Subtype.ext
    ext i j
    change (Matrix.diagonal (fun i => ((torusWeights (1 : Fin 2 → Kˣ) i) : K))) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j
    fin_cases i <;> fin_cases j <;> simp [torusWeights, Matrix.diagonal_apply]
  simpa only [diagonalMap, Equiv.apply_symm_apply] using
    point_mem_component (dVariety_isConnected 2) (diagonalMap d hd)
      ((dPointEquiv 2).symm 1) hone ((dPointEquiv 2).symm z)

private lemma entry_zero (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (p : Variety.Point (blockVariety d hd)) (i j : Fin 3) (hij : d i ≠ d j) :
    (blockPointEquiv d hd p).val.val i j = 0 := by
  have h := (mem_diagonalSL_centralizer_iff d hd _).mp
    (blockPointEquiv d hd p).property i j
  by_contra hn
  exact hij (Units.ext (mul_right_cancel₀ hn h))

private lemma distinct_connected (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (hne : Function.Injective d) : Variety.IsConnected (blockVariety d hd) := by
  apply (identityComponent_eq_univ_iff_isConnected _).mp
  apply Set.eq_univ_of_univ_subset
  intro p _
  let A := (blockPointEquiv d hd p).val
  have hz (i j : Fin 3) (h : i ≠ j) : A.val i j = 0 :=
    entry_zero d hd p i j (fun h' => h (hne h'))
  have hdet : A.val 0 0 * A.val 1 1 * A.val 2 2 = 1 := by
    have h : A.val.det = 1 := A.property
    rw [Matrix.det_fin_three] at h
    simpa [ hz 0 1 (by decide), hz 0 2 (by decide),
      hz 1 0 (by decide), hz 1 2 (by decide), hz 2 0 (by decide), hz 2 1 (by decide)] using h
  have h0 : A.val 0 0 ≠ 0 := by intro h; simp [h] at hdet
  have h1 : A.val 1 1 ≠ 0 := by intro h; simp [h] at hdet
  let z : Fin 2 → Kˣ := ![Units.mk0 (A.val 0 0) h0, Units.mk0 (A.val 1 1) h1]
  have hp : p = diagonalPoint d hd z := by
    apply Variety.Point.ext
    funext ⟨i,j⟩
    change A.val i j = (Matrix.diagonal (fun i => (torusWeights z i : K))) i j
    fin_cases i <;> fin_cases j <;>
      simp [torusWeights, z, hz 0 1 (by decide), hz 0 2 (by decide),
        hz 1 0 (by decide), hz 1 2 (by decide), hz 2 0 (by decide), hz 2 1 (by decide)]
    field_simp
    linear_combination hdet
  rw [hp]
  exact diagonal_mem d hd z

private def embedSL2 (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![B.val 0 0, B.val 0 1, 0; B.val 1 0, B.val 1 1, 0; 0, 0, 1], by
    have h : B.val.det = 1 := B.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩

private def pairPoint (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (heq : d 0 = d 1) (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Variety.Point (blockVariety d hd) :=
  blockPoint d hd (embedSL2 B) (by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [embedSL2, heq])

private def pairMap (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) (heq : d 0 = d 1) :
    Variety.Morphism (slVariety K 2) (blockVariety d hd) where
  toFun z := pairPoint d hd heq (slPointEquiv 2 z)
  regular := by
    rintro ⟨⟨i,j⟩⟩
    let X (i j : Fin 2) : MvPolynomial (slVariety K 2).Coordinates K :=
      MvPolynomial.X (ULift.up (i,j))
    refine ⟨!![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1] i j, ?_⟩
    intro z
    change (embedSL2 (slPointEquiv 2 z)).val i j = _
    fin_cases i <;> fin_cases j <;> simp [embedSL2, X, evalPolynomial] <;> rfl

private lemma pair_mem (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (heq : d 0 = d 1) (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    pairPoint d hd heq B ∈ Theory.AlgebraicGroup.identityComponent (blockVariety d hd) := by
  have hone : (pairMap d hd heq).toFun ((slPointEquiv 2).symm 1) = 1 := by
    apply (blockPointEquiv d hd).injective
    apply Subtype.ext
    ext i j
    change (embedSL2 ((slPointEquiv 2) ((slPointEquiv 2).symm 1))).val i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j
    rw [Equiv.apply_symm_apply]
    fin_cases i <;> fin_cases j <;> simp [embedSL2]
  simpa only [pairMap, Equiv.apply_symm_apply] using
    point_mem_component (slVariety_isConnected 2) (pairMap d hd heq)
      ((slPointEquiv 2).symm 1) hone ((slPointEquiv 2).symm B)

private lemma pair_connected (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (heq : d 0 = d 1) (hne : d 0 ≠ d 2) :
    Variety.IsConnected (blockVariety d hd) := by
  apply (identityComponent_eq_univ_iff_isConnected _).mp
  apply Set.eq_univ_of_univ_subset
  intro p _
  let A := (blockPointEquiv d hd p).val
  have h12 : d 1 ≠ d 2 := by rwa [← heq]
  have h02 : A.val 0 2 = 0 := entry_zero d hd p 0 2 hne
  have h20 : A.val 2 0 = 0 := entry_zero d hd p 2 0 hne.symm
  have h12' : A.val 1 2 = 0 := entry_zero d hd p 1 2 h12
  have h21 : A.val 2 1 = 0 := entry_zero d hd p 2 1 h12.symm
  have hdet : A.val 0 0 * A.val 1 1 * A.val 2 2 -
      A.val 0 1 * A.val 1 0 * A.val 2 2 = 1 := by
    have h : A.val.det = 1 := A.property
    rw [Matrix.det_fin_three] at h
    simpa [h02, h20, h12', h21] using h
  have h2 : A.val 2 2 ≠ 0 := by intro h; simp [h] at hdet
  let B : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![A.val 0 0 * A.val 2 2, A.val 0 1; A.val 1 0 * A.val 2 2, A.val 1 1], by
      rw [Matrix.det_fin_two]
      change (A.val 0 0 * A.val 2 2) * A.val 1 1 -
        A.val 0 1 * (A.val 1 0 * A.val 2 2) = 1
      linear_combination hdet⟩
  let z : Fin 2 → Kˣ := ![(Units.mk0 (A.val 2 2) h2)⁻¹, 1]
  have hp : p = pairPoint d hd heq B * diagonalPoint d hd z := by
    apply (blockPointEquiv d hd).injective
    rw [map_mul]
    apply Subtype.ext
    ext i j
    change A.val i j = ((embedSL2 B).val *
      Matrix.diagonal (fun i => (torusWeights z i : K))) i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;>
      simp [embedSL2, B, torusWeights, z, h02, h20, h12', h21, h2]
  rw [hp]
  exact (Theory.AlgebraicGroup.identityComponentSubgroup _).mul_mem
    (pair_mem d hd heq B) (diagonal_mem d hd z)

private lemma permuted_connected (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (e : Equiv.Perm (Fin 3))
    (hc : Variety.IsConnected (blockVariety (fun i => d (e i))
      ((Equiv.prod_comp e d).trans hd))) :
    Variety.IsConnected (blockVariety d hd) := by
  let d' : Fin 3 → Kˣ := fun i => d (e i)
  have hd' : ∏ i, d' i = 1 := (Equiv.prod_comp e d).trans hd
  let f : Variety.Morphism (blockVariety d' hd') (blockVariety d hd) :=
    { toFun := fun x => blockPoint d hd
        ⟨(blockPointEquiv d' hd' x).val.val.submatrix e.symm e.symm, by
          rw [Matrix.det_submatrix_equiv_self]
          exact (blockPointEquiv d' hd' x).val.property⟩ (by
            intro i j
            have h := (mem_diagonalSL_centralizer_iff d' hd' _).mp
              (blockPointEquiv d' hd' x).property (e.symm i) (e.symm j)
            simpa only [d', Equiv.apply_symm_apply, Matrix.submatrix_apply] using h)
      regular := by
        rintro ⟨⟨i,j⟩⟩
        refine ⟨MvPolynomial.X (ULift.up (e.symm i, e.symm j)), ?_⟩
        intro x
        change x.val (ULift.up (e.symm i, e.symm j)) = _
        simp [evalPolynomial] }
  have hsurj : Function.Surjective f.toFun := by
    intro y
    let A : Matrix.SpecialLinearGroup (Fin 3) K :=
      ⟨(blockPointEquiv d hd y).val.val.submatrix e e, by
        rw [Matrix.det_submatrix_equiv_self]
        exact (blockPointEquiv d hd y).val.property⟩
    have hA : ∀ i j, (d' i : K) * A.val i j = (d' j : K) * A.val i j := by
      intro i j
      exact (mem_diagonalSL_centralizer_iff d hd _).mp
        (blockPointEquiv d hd y).property (e i) (e j)
    refine ⟨blockPoint d' hd' A hA, ?_⟩
    apply Variety.Point.ext
    funext ⟨i,j⟩
    change (blockPointEquiv d hd y).val.val (e (e.symm i)) (e (e.symm j)) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, blockPointEquiv_entry]
  have h := hc.image f.toFun f.continuous.continuousOn
  unfold Variety.IsConnected
  simpa only [Set.image_univ, hsurj.range_eq] using h

/-- Every diagonal centralizer in SL₃ is connected, including scalar diagonals. -/
public theorem blockVariety_isConnected (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) :
    Variety.IsConnected (blockVariety d hd) := by
  by_cases h01 : d 0 = d 1
  · by_cases h02 : d 0 = d 2
    · apply scalar_connected d hd
      intro i
      fin_cases i
      · rfl
      · exact h01.symm
      · exact h02.symm
    · exact pair_connected d hd h01 h02
  · by_cases h02 : d 0 = d 2
    · apply permuted_connected d hd (Equiv.swap 1 2)
      apply pair_connected
      · simpa [Equiv.swap_apply_def] using h02
      · simpa [Equiv.swap_apply_def] using h01
    · by_cases h12 : d 1 = d 2
      · apply permuted_connected d hd (Equiv.swap 0 2)
        apply pair_connected
        · simpa [Equiv.swap_apply_def] using h12.symm
        · simpa [Equiv.swap_apply_def] using (Ne.symm h02)
      · apply distinct_connected d hd
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
