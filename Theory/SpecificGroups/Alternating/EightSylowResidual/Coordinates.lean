module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Binary four-space coordinates for the A₈ Sylow-overgroup calculation

The complete standard flag stabilizer is the image of the actual upper
unitriangular Sylow subgroup of SL₄(2). Partial flags and permutation matrices
provide the coordinates for Bruhat elimination and adjacent-swap generation.

Adapted in dimension four from the checked internal modules
`BinaryLinear.FiveFlagGeometry` and `FiveFlagGeometry.SylowOvergroups.Coordinates`.
The general unitriangular Sylow theorem supplies maximality without enumeration.
The eventual residual comparison is used in Aschbacher–Smith 3.3.21(e),
printed p.596 of the combined manuscript (1 March 2004).
-/

@[expose] public section
namespace BinaryLinear.FourSylowResidual
open OuterCyclic Subgroup

/-- The span of the first `i + 1` basis vectors; the indices are the three proper cuts. -/
noncomputable def flagSpace (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (i : Fin 3) : Submodule (ZMod 2) (Space 4) :=
  Submodule.span (ZMod 2) (b '' {j : Fin 4 | j.val ≤ i.val})

/-- The actual subgroup preserving each subspace specified by the cuts. -/
noncomputable def flagStabilizer (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (cuts : Set (Fin 3)) :
    Subgroup (LinearGroup 4) := ⨅ i ∈ cuts, parabolic (flagSpace b i)

theorem mem_flagStabilizer_iff (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (cuts : Set (Fin 3)) (g : LinearGroup 4) :
    g ∈ flagStabilizer b cuts ↔ ∀ i ∈ cuts, ∀ v, g v ∈ flagSpace b i ↔ v ∈ flagSpace b i := by
  simp only [flagStabilizer, mem_iInf]
  rfl

@[simp] theorem flagStabilizer_empty (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) : flagStabilizer b ∅ = ⊤ := by
  simp [flagStabilizer]

@[simp] theorem flagStabilizer_singleton (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (i : Fin 3) :
    flagStabilizer b {i} = parabolic (flagSpace b i) := by
  simp [flagStabilizer]

theorem flagStabilizer_antitone (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) : Antitone (flagStabilizer b) := by
  intro s t hst g hg
  rw [mem_flagStabilizer_iff] at hg ⊢
  exact fun i hi => hg i (hst hi)

theorem basis_mem_flagSpace_iff (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (i : Fin 3) (j : Fin 4) :
    b j ∈ flagSpace b i ↔ j.val ≤ i.val := b.self_mem_span_image

/-- The standard coordinate basis of the actual binary four-space. -/
noncomputable def standardBasis : Module.Basis (Fin 4) (ZMod 2) (Space 4) := Pi.basisFun (ZMod 2) (Fin 4)
/-- The stabilizer of the complete standard flag. -/
noncomputable def standardBorel : Subgroup (LinearGroup 4) :=
  flagStabilizer standardBasis Set.univ

theorem mem_standard_flagSpace_iff (i : Fin 3) (v : Space 4) :
    v ∈ flagSpace standardBasis i ↔ ∀ j : Fin 4, i.val < j.val → v j = 0 := by
  rw [flagSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 4, v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

/-- The actual matrix of a linear automorphism, using the binary SL comparison. -/
noncomputable def matrix (g : LinearGroup 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ((slEquivLinear 4).symm g).val

theorem matrix_mulVec (g : LinearGroup 4) (v : Space 4) :
    (matrix g).mulVec v = g v := by
  rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]

theorem matrix_apply (g : LinearGroup 4) (i j : Fin 4) :
    matrix g i j = g (standardBasis j) i := by
  have h := congrFun (matrix_mulVec g (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, standardBasis, Pi.basisFun_apply] using h

/-- One-sided preservation suffices because the subspace and group are finite. -/
theorem mem_flagStabilizer_iff_maps (b : Module.Basis (Fin 4) (ZMod 2) (Space 4)) (cuts : Set (Fin 3))
    (g : LinearGroup 4) :
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
    have hwv : (w : Space 4) = v := g.injective (congrArg Subtype.val hw)
    exact hwv ▸ w.property

theorem mem_standard_flagStabilizer_iff (cuts : Set (Fin 3)) (g : LinearGroup 4) :
    g ∈ flagStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i j : Fin 4, k.val < i.val → j.val ≤ k.val → matrix g i j = 0 := by
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

theorem mem_standardBorel_iff (g : LinearGroup 4) :
    g ∈ standardBorel ↔ (matrix g).IsUpperTriangular := by
  rw [standardBorel, mem_standard_flagStabilizer_iff]
  constructor
  · intro h i j hji
    exact h ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      (Set.mem_univ _) i j hji le_rfl
  · intro h k _ i j hi hj
    exact h (show j < i by change j.val < i.val; omega)


/-- The standard Sylow transported from the actual binary special linear group. -/
noncomputable def standardSylow : Sylow 2 (LinearGroup 4) :=
  (Theory.SpecificGroups.LinearSylowNormalizers.standardSylow 4 (ZMod 2) (by decide)).mapSurjective
    (f := (slEquivLinear 4).toMonoidHom) (slEquivLinear 4).surjective

@[simp] theorem standardSylow_coe :
    (standardSylow : Subgroup (LinearGroup 4)) = standardBorel := by
  change ((Theory.SpecificGroups.LinearSylowNormalizers.standardSylow
    4 (ZMod 2) (by decide) : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))).map
      (slEquivLinear 4).toMonoidHom) = _
  rw [Theory.SpecificGroups.LinearSylowNormalizers.coe_standardSylow]
  ext g
  rw [Subgroup.mem_map_equiv,
    Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent,
    Theory.SpecificGroups.LinearSylowNormalizers.mem_borel, mem_standardBorel_iff]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, fun i => ?_⟩
    have hd := ((slEquivLinear 4).symm g).property
    change (matrix g).det = 1 at hd
    rw [Matrix.det_of_isUpperTriangular h] at hd
    have hp : (∏ j, matrix g j j) ≠ 0 := by rw [hd]; exact one_ne_zero
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _
      (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))

theorem standardBorel_isPGroup : IsPGroup 2 standardBorel := by
  rw [← standardSylow_coe]
  exact standardSylow.isPGroup'

/-- The permutation matrix sending the standard vector `i` to `σ i`. -/
noncomputable def permutation : Equiv.Perm (Fin 4) →* LinearGroup 4 where
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
  ∀ g : LinearGroup 4, ∃ u ∈ standardBorel, ∃ σ : Equiv.Perm (Fin 4),
    ∃ v ∈ standardBorel, g = u * permutation σ * v

end BinaryLinear.FourSylowResidual
