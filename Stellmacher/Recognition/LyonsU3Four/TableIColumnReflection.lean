module
public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData

/-!
# Reflection of the nonprincipal Table I columns

Swapping columns 1 with 2 and 3 with 4 fixes the distinguished column and
inverts the Galois four-cycle. It therefore preserves the numerical pattern,
signed degree, order and prime constraints used in Lyons's Table I elimination.
The proofs transport the Galois action by its inverse and reindex the column sums.

This is a numerical normalization. It does not assert that the section identity
with a fixed fifth-root basis is preserved. Character conclusions must be pulled
back to the original rows after the numerical elimination.
Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), §3,
Table I and the two orientations in Case 3 on p. 378.
-/

@[expose] public section

open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

def columnReflection : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] theorem columnReflection_twice (i : Fin 5) :
    columnReflection (columnReflection i) = i := by fin_cases i <;> rfl

@[simp] theorem columnReflection_zero : columnReflection 0 = 0 := rfl

theorem columnReflection_galois (i : Fin 5) :
    galoisColumn (columnReflection (galoisColumn i)) = columnReflection i := by
  fin_cases i <;> rfl

def reflectColumns {I : Type*} (d : GeneralizedDecompositionData I) :
    GeneralizedDecompositionData I where
  dT := d.dT
  iDz i := d.iDz (columnReflection i)

variable {I : Type*} (d : GeneralizedDecompositionData I)

@[simp] theorem reflectColumns_dT : d.reflectColumns.dT = d.dT := rfl
@[simp] theorem reflectColumns_iDz (i : Fin 5) :
    d.reflectColumns.iDz i = d.iDz (columnReflection i) := rfl

@[simp] theorem reflectColumns_twice : d.reflectColumns.reflectColumns = d := by
  cases d
  simp [reflectColumns]

@[simp] theorem reflectColumns_zValue (j : I) : d.reflectColumns.zValue j = d.zValue j := by
  exact Fintype.sum_equiv columnReflection _ _ (fun _ => rfl)

theorem reflectColumns_contribution (j : I) :
    d.reflectColumns.contribution j = d.contribution j := by
  have hIio (i : Fin 5) : Finset.Iio i = Finset.univ.filter (fun k => k < i) := by
    ext k
    simp
  simp only [contribution, hIio, Finset.sum_filter]
  simp only [Fin.sum_univ_succ]
  norm_num [reflectColumns, columnReflection, Fin.lt_def, Fin.reduceFinMk, Matrix.cons_val]
  simp only [show (![0, 2, 1, 4, 3] : Fin 5 → Fin 5) 2 = 1 from rfl,
    show (![2, 1, 4, 3] : Fin 4 → Fin 5) 2 = 4 from rfl,
    show (![1, 4, 3] : Fin 3 → Fin 5) 2 = 3 from rfl,
    show (Fin.succ (2 : Fin 4)) = (3 : Fin 5) from rfl,
    show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl,
    show (Fin.succ (3 : Fin 4)) = (4 : Fin 5) from rfl]
  ring

theorem GaloisSymmetry.reflectColumns (h : d.GaloisSymmetry) :
    d.reflectColumns.GaloisSymmetry := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, ?_⟩
  intro j
  constructor
  · have ht := (hσ (σ.symm j)).1
    simpa only [reflectColumns_dT, Equiv.apply_symm_apply] using ht.symm
  · intro i
    have hi := (hσ (σ.symm j)).2 (columnReflection (galoisColumn i))
    simpa only [reflectColumns_iDz, columnReflection_galois,
      Equiv.apply_symm_apply] using hi.symm

theorem SignedGaloisSymmetry.reflectColumns {r : I → ℤ}
    (h : d.SignedGaloisSymmetry r) : d.reflectColumns.SignedGaloisSymmetry r := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, ?_⟩
  intro j
  obtain ⟨ε, hε, hr, ht, hz⟩ := hσ (σ.symm j)
  simp only [Equiv.apply_symm_apply] at hr ht hz
  have reverse {x y : ℤ} (he : x = ε * y) : y = ε * x := by
    rw [he, ← mul_assoc, ← pow_two, hε, one_mul]
  refine ⟨ε, hε, reverse hr, reverse ht, ?_⟩
  intro i
  have hi := hz (columnReflection (galoisColumn i))
  rw [columnReflection_galois] at hi
  exact reverse hi

variable [Fintype I]

theorem TableIPatternHypotheses.reflectColumns {principal : I}
    (h : d.TableIPatternHypotheses principal) :
    d.reflectColumns.TableIPatternHypotheses principal := by
  refine ⟨?_, ?_, ?_, h.galois_symmetry.reflectColumns d, h.principal_dT, ?_, ?_⟩
  · refine ⟨h.equation_3_2.tt, fun i => h.equation_3_2.tz (columnReflection i), ?_⟩
    intro i k
    simpa only [reflectColumns_iDz, columnReflection.injective.eq_iff] using
      h.equation_3_2.zz (columnReflection i) (columnReflection k)
  · intro j
    rw [reflectColumns_contribution]
    exact h.equation_3_3 j
  · intro j
    simpa only [reflectColumns_dT, reflectColumns_zValue] using h.equation_3_4 j
  · intro i
    rw [reflectColumns_iDz, h.principal_iDz]
    congr 1
    apply propext
    change columnReflection i = columnReflection 0 ↔ i = 0
    exact columnReflection.injective.eq_iff
  · simpa only [reflectColumns_zValue] using h.z_nonzero

theorem DegreeConstraints.reflectColumns {principal : I} {r : I → ℤ}
    (h : d.DegreeConstraints principal r) :
    d.reflectColumns.DegreeConstraints principal r := by
  refine ⟨h.principal_degree, h.degree_nonzero, h.degree_lower, ?_, ?_,
    h.orthogonal_t, fun i => h.orthogonal_z (columnReflection i),
    h.galois_symmetry.reflectColumns d⟩
  · simpa only [reflectColumns_zValue, reflectColumns_dT] using h.multiplicity_integral
  · simpa only [reflectColumns_zValue, reflectColumns_dT] using h.multiplicity_nonneg

theorem reflectColumns_weightedColumn (r a : I → ℤ) :
    d.reflectColumns.weightedColumn r a = d.weightedColumn r a := by
  simp only [weightedColumn, reflectColumns_zValue]

theorem OrderConstraints.reflectColumns {r : I → ℤ} {g c e : ℕ}
    (h : d.OrderConstraints r g c e) : d.reflectColumns.OrderConstraints r g c e := by
  refine ⟨h.group_pos, h.centralizer_pos, h.center_centralizer_pos, ?_, ?_, ?_⟩
  · simpa only [reflectColumns_dT, reflectColumns_weightedColumn] using h.zero_t
  · intro i
    simpa only [reflectColumns_weightedColumn, reflectColumns_iDz,
      columnReflection_zero] using h.equal_z (columnReflection i)
  · simpa only [reflectColumns_weightedColumn, reflectColumns_iDz,
      columnReflection_zero] using h.centralizer_identity

omit [Fintype I] in
theorem reflectColumns_rowSeparated_iff (r : I → ℤ) (j : I) :
    d.reflectColumns.RowSeparated r j ↔ d.RowSeparated r j := by
  constructor
  · intro h k ε hε hr ht hz
    exact h k ε hε hr ht (fun i => hz (columnReflection i))
  · intro h k ε hε hr ht hz
    apply h k ε hε hr ht
    intro i
    simpa only [reflectColumns_iDz, columnReflection_twice] using hz (columnReflection i)

omit [Fintype I] in
theorem PrimeConstraints.reflectColumns {r : I → ℤ} {g : ℕ}
    (h : d.PrimeConstraints r g) : d.reflectColumns.PrimeConstraints r g := by
  refine ⟨h.degree_dvd, ?_⟩
  intro j hj hsep
  exact h.prime_bound j hj ((d.reflectColumns_rowSeparated_iff r j).mp hsep)

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
