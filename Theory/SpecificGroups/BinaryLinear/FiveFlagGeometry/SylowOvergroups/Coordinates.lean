module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# Coordinates and transport for binary five-dimensional flags

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
-/

@[expose] public section

namespace BinaryLinear.FiveFlagGeometry.SylowOvergroups
open OuterCyclic
/-- The standard coordinate basis of the actual binary five-space. -/
noncomputable def standardBasis : FiveBasis := Pi.basisFun (ZMod 2) (Fin 5)
/-- The stabilizer of the complete standard flag. -/
noncomputable def standardBorel : Subgroup (LinearGroup 5) :=
  flagStabilizer standardBasis Set.univ

theorem mem_standard_flagSpace_iff (i : Fin 4) (v : Space 5) :
    v ∈ flagSpace standardBasis i ↔ ∀ j : Fin 5, i.val < j.val → v j = 0 := by
  rw [flagSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 5, v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

theorem flagSpace_map (b : FiveBasis) (g : LinearGroup 5) (i : Fin 4) :
    flagSpace (b.map g) i = (flagSpace b i).map g.toLinearMap := by
  rw [flagSpace, flagSpace, Submodule.map_span]
  congr 1
  ext v
  simp

theorem flagStabilizer_map_conj (b : FiveBasis) (cuts : Set (Fin 4))
    (g : LinearGroup 5) :
    (flagStabilizer b cuts).map (MulAut.conj g).toMonoidHom =
      flagStabilizer (b.map g) cuts := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_flagStabilizer_iff, mem_flagStabilizer_iff]
  simp_rw [flagSpace_map, Submodule.mem_map_equiv]
  constructor
  · intro hx i hi v
    have h := hx i hi (g.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hx i hi v
    have h := hx i hi (g v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

/-- The actual matrix of a linear automorphism, using the binary SL comparison. -/
noncomputable def matrix (g : LinearGroup 5) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ((slEquivLinear 5).symm g).val

theorem matrix_mulVec (g : LinearGroup 5) (v : Space 5) :
    (matrix g).mulVec v = g v := by
  rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]

theorem matrix_apply (g : LinearGroup 5) (i j : Fin 5) :
    matrix g i j = g (standardBasis j) i := by
  have h := congrFun (matrix_mulVec g (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, standardBasis, Pi.basisFun_apply] using h

/-- One-sided preservation suffices because the subspace and group are finite. -/
theorem mem_flagStabilizer_iff_maps (b : FiveBasis) (cuts : Set (Fin 4))
    (g : LinearGroup 5) :
    g ∈ flagStabilizer b cuts ↔
      ∀ i ∈ cuts, ∀ v ∈ flagSpace b i, g v ∈ flagSpace b i := by
  rw [mem_flagStabilizer_iff]
  constructor
  · exact fun h i hi v hv => (h i hi v).mpr hv
  · intro h i hi v
    refine ⟨?_, h i hi v⟩
    intro hv
    let f : flagSpace b i → flagSpace b i := fun w => ⟨g w, h i hi w w.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hf) ⟨g v, hv⟩
    have hwv : (w : Space 5) = v := g.injective (congrArg Subtype.val hw)
    exact hwv ▸ w.property

theorem mem_standard_flagStabilizer_iff (cuts : Set (Fin 4)) (g : LinearGroup 5) :
    g ∈ flagStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i j : Fin 5, k.val < i.val → j.val ≤ k.val → matrix g i j = 0 := by
  rw [mem_flagStabilizer_iff_maps]
  constructor
  · intro h k hk i j hi hj
    rw [matrix_apply]
    exact (mem_standard_flagSpace_iff k _).mp
      (h k hk _ ((basis_mem_flagSpace_iff standardBasis k j).mpr hj)) i hi
  · intro h k hk v hv
    apply (mem_standard_flagSpace_iff k _).mpr
    intro i hi
    rw [← matrix_mulVec]
    change ∑ j, matrix g i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val ≤ k.val
    · rw [h k hk i j hi hj, zero_mul]
    · rw [(mem_standard_flagSpace_iff k v).mp hv j (Nat.lt_of_not_ge hj), mul_zero]

theorem mem_standardBorel_iff (g : LinearGroup 5) :
    g ∈ standardBorel ↔ (matrix g).IsUpperTriangular := by
  rw [standardBorel, mem_standard_flagStabilizer_iff]
  constructor
  · intro h i j hji
    exact h ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      (Set.mem_univ _) i j hji le_rfl
  · intro h k _ i j hi hj
    exact h (show j < i by change j.val < i.val; omega)

private theorem unitriangular_pow_eight {A : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (hA : A.IsUpperTriangular) (hdiag : ∀ i, A i i = 1) : A ^ 8 = 1 := by
  have hchar : A.charpoly = (Polynomial.X - Polynomial.C 1) ^ 5 := by
    rw [Matrix.charpoly_of_isUpperTriangular A hA]
    simp_rw [hdiag]
    simp
  have hnil : (A - 1) ^ 5 = 0 := by
    have h := Matrix.aeval_self_charpoly A
    rw [hchar] at h
    simpa using h
  have hnil' : (A - 1) ^ (2 ^ 3) = 0 := pow_eq_zero_of_le (by decide) hnil
  let : ExpChar (Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (ZMod 2) (Matrix (Fin 5) (Fin 5) (ZMod 2))) 2
  have h := add_pow_expChar_pow_of_commute 2 3 (Commute.one_left (A - 1))
  have hsum : (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) + (A - 1) = A := by
    rw [add_comm, sub_add_cancel]
  rw [hsum, one_pow, hnil', add_zero] at h
  norm_num only at h
  exact h

theorem standardBorel_diagonal {g : LinearGroup 5} (hg : g ∈ standardBorel)
    (i : Fin 5) : matrix g i i = 1 := by
  have hd : (matrix g).det = 1 := ((slEquivLinear 5).symm g).property
  rw [Matrix.det_of_isUpperTriangular ((mem_standardBorel_iff g).mp hg)] at hd
  have hp : (∏ j : Fin 5, matrix g j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi : matrix g i i ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

theorem matrix_injective : Function.Injective matrix := by
  intro g h he
  apply (slEquivLinear 5).symm.injective
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
noncomputable def permutation : Equiv.Perm (Fin 5) →* LinearGroup 5 where
  toFun σ := standardBasis.equiv standardBasis σ
  map_one' := by
    apply standardBasis.ext'
    intro i
    simp
  map_mul' σ τ := by
    apply standardBasis.ext'
    intro i
    simp [LinearEquiv.mul_apply]

@[simp] theorem permutation_basis (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permutation σ (standardBasis i) = standardBasis (σ i) :=
  standardBasis.equiv_apply i standardBasis σ

/-- The concrete Bruhat factorization needed for the overgroup argument.
This is a proof obligation, not a supplied classification assertion. -/
def HasBruhatDecomposition : Prop :=
  ∀ g : LinearGroup 5, ∃ u ∈ standardBorel, ∃ σ : Equiv.Perm (Fin 5),
    ∃ v ∈ standardBorel, g = u * permutation σ * v

end BinaryLinear.FiveFlagGeometry.SylowOvergroups


