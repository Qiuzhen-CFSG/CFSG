module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# Coordinates and transport for binary four-dimensional flags

The standard full-flag stabilizer is exactly the upper triangular subgroup.
Over the binary field all its diagonal entries are one. Cayley--Hamilton
therefore gives exponent dividing eight, proving it is a two-group.
For every partial flag, its geometric stabilizer is characterized by the
matrix entries below its cuts. Conjugation transports the actual basis and
all of its flag spaces, so standard-coordinate results apply to actual
embedded subgroups.

The Cayley--Hamilton proof follows the narrow matrix argument in
`Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.FixedSpace`.
The intended application is Aschbacher--Smith, combined manuscript of
1 March 2004, A.3.12, printed pp.47--48, and 1.3.9, printed p.514.
Sylow maximality and exhaustion of overgroups are separate assertions.
Adapted from this repository’s degree-five `FiveFlagGeometry.SylowOvergroups.Coordinates`
proof, specialized to the degree-four branch of 15.3.49(l).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
open Chapter2.ComponentRefinement.LieType.Binary
/-- The standard coordinate basis of the actual binary four-space. -/
noncomputable def standardBasis : Basis 3 := Pi.basisFun (ZMod 2) (Fin 4)
/-- The stabilizer of the complete standard flag. -/
noncomputable def standardBorel : Subgroup (BinaryLinear.GL (Vector 4)) :=
  cutStabilizer standardBasis Set.univ

theorem mem_standard_cutSpace_iff (i : Fin 3) (v : Vector 4) :
    v ∈ cutSpace standardBasis i ↔ ∀ j : Fin 4, i.val < j.val → v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 4, v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

theorem cutSpace_map (b : Basis 3) (g : BinaryLinear.GL (Vector 4)) (i : Fin 3) :
    cutSpace (b.map g) i = (cutSpace b i).map g.toLinearMap := by
  rw [cutSpace, cutSpace, Submodule.map_span]
  congr 1
  ext v
  simp

theorem cutStabilizer_map_conj (b : Basis 3) (cuts : Set (Fin 3))
    (g : BinaryLinear.GL (Vector 4)) :
    (cutStabilizer b cuts).map (MulAut.conj g).toMonoidHom =
      cutStabilizer (b.map g) cuts := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  simp_rw [cutSpace_map, Submodule.mem_map_equiv]
  constructor
  · intro hx i hi v
    have h := hx i hi (g.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hx i hi v
    have h := hx i hi (g v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

theorem cutStabilizer_antitone (b : Basis 3) : Antitone (cutStabilizer b) := by
  intro s t hst
  exact (cutStabilizer_le_iff _ _ _).mpr hst

/-- The actual matrix of a linear automorphism, using the binary SL comparison. -/
noncomputable def matrix (g : BinaryLinear.GL (Vector 4)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ((slEquivLinear 4).symm g).val

theorem matrix_mulVec (g : BinaryLinear.GL (Vector 4)) (v : Vector 4) :
    (matrix g).mulVec v = g v := by
  rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]

theorem matrix_apply (g : BinaryLinear.GL (Vector 4)) (i j : Fin 4) :
    matrix g i j = g (standardBasis j) i := by
  have h := congrFun (matrix_mulVec g (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, standardBasis, Pi.basisFun_apply] using h

/-- One-sided preservation suffices because the subspace and group are finite. -/
theorem mem_cutStabilizer_maps (b : Basis 3) (cuts : Set (Fin 3))
    (g : BinaryLinear.GL (Vector 4)) :
    g ∈ cutStabilizer b cuts ↔
      ∀ i ∈ cuts, ∀ v ∈ cutSpace b i, g v ∈ cutSpace b i := by
  rw [mem_cutStabilizer]
  constructor
  · exact fun h i hi v hv => (h i hi v).mpr hv
  · intro h i hi v
    refine ⟨?_, h i hi v⟩
    intro hv
    let f : cutSpace b i → cutSpace b i := fun w => ⟨g w, h i hi w w.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hf) ⟨g v, hv⟩
    have hwv : (w : Vector 4) = v := g.injective (congrArg Subtype.val hw)
    exact hwv ▸ w.property

theorem mem_standard_cutStabilizer_iff (cuts : Set (Fin 3)) (g : BinaryLinear.GL (Vector 4)) :
    g ∈ cutStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i j : Fin 4, k.val < i.val → j.val ≤ k.val → matrix g i j = 0 := by
  rw [mem_cutStabilizer_maps]
  constructor
  · intro h k hk i j hi hj
    rw [matrix_apply]
    exact (mem_standard_cutSpace_iff k _).mp
      (h k hk _ ((basis_mem_cutSpace standardBasis k j).mpr hj)) i hi
  · intro h k hk v hv
    apply (mem_standard_cutSpace_iff k _).mpr
    intro i hi
    rw [← matrix_mulVec]
    change ∑ j, matrix g i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val ≤ k.val
    · rw [h k hk i j hi hj, zero_mul]
    · rw [(mem_standard_cutSpace_iff k v).mp hv j (Nat.lt_of_not_ge hj), mul_zero]

theorem mem_standardBorel_iff (g : BinaryLinear.GL (Vector 4)) :
    g ∈ standardBorel ↔ (matrix g).IsUpperTriangular := by
  rw [standardBorel, mem_standard_cutStabilizer_iff]
  constructor
  · intro h i j hji
    exact h ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      (Set.mem_univ _) i j hji le_rfl
  · intro h k _ i j hi hj
    exact h (show j < i by change j.val < i.val; omega)

private theorem unitriangular_pow_eight {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hA : A.IsUpperTriangular) (hdiag : ∀ i, A i i = 1) : A ^ 8 = 1 := by
  have hchar : A.charpoly = (Polynomial.X - Polynomial.C 1) ^ 4 := by
    rw [Matrix.charpoly_of_isUpperTriangular A hA]
    simp_rw [hdiag]
    simp
  have hnil : (A - 1) ^ 4 = 0 := by
    have h := Matrix.aeval_self_charpoly A
    rw [hchar] at h
    simpa using h
  have hnil' : (A - 1) ^ (2 ^ 3) = 0 := pow_eq_zero_of_le (by decide) hnil
  let : ExpChar (Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (ZMod 2) (Matrix (Fin 4) (Fin 4) (ZMod 2))) 2
  have h := add_pow_expChar_pow_of_commute 2 3 (Commute.one_left (A - 1))
  have hsum : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + (A - 1) = A := by
    rw [add_comm, sub_add_cancel]
  rw [hsum, one_pow, hnil', add_zero] at h
  norm_num only at h
  exact h

theorem standardBorel_diagonal {g : BinaryLinear.GL (Vector 4)} (hg : g ∈ standardBorel)
    (i : Fin 4) : matrix g i i = 1 := by
  have hd : (matrix g).det = 1 := ((slEquivLinear 4).symm g).property
  rw [Matrix.det_of_isUpperTriangular ((mem_standardBorel_iff g).mp hg)] at hd
  have hp : (∏ j : Fin 4, matrix g j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi : matrix g i i ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

theorem matrix_injective : Function.Injective matrix := by
  intro g h he
  apply (slEquivLinear 4).symm.injective
  exact Subtype.ext he

theorem standardBorel_isPGroup : IsPGroup 2 standardBorel := by
  intro g
  refine ⟨3, ?_⟩
  apply Subtype.ext
  apply matrix_injective
  simpa only [matrix, map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one,
    Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    show (2 : ℕ) ^ 3 = 8 by decide] using
    unitriangular_pow_eight ((mem_standardBorel_iff g.val).mp g.property)
      (fun i => standardBorel_diagonal g.property i)

/-- The permutation matrix sending the standard vector `i` to `σ i`. -/
noncomputable def permutation : Equiv.Perm (Fin 4) →* BinaryLinear.GL (Vector 4) where
  toFun σ := standardBasis.equiv standardBasis σ
  map_one' := by
    apply standardBasis.ext'
    intro i
    simp
  map_mul' σ τ := by
    apply standardBasis.ext'
    intro i
    simp [LinearEquiv.mul_apply]

@[simp] theorem permutation_basis (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    permutation σ (standardBasis i) = standardBasis (σ i) :=
  standardBasis.equiv_apply i standardBasis σ

/-- The concrete Bruhat factorization needed for the overgroup argument.
This is a proof obligation, not a supplied classification assertion. -/
def HasBruhatDecomposition : Prop :=
  ∀ g : BinaryLinear.GL (Vector 4), ∃ u ∈ standardBorel, ∃ σ : Equiv.Perm (Fin 4),
    ∃ v ∈ standardBorel, g = u * permutation σ * v

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four


