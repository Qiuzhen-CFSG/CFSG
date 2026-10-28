module

public import Theory.SpecificGroups.SL3.SplitMonomial
public import Mathlib.LinearAlgebra.Determinant

/-!
# Invariant line bases and concrete monomial placement

A basis whose lines are permuted by a subgroup gives an actual change of
coordinates in SL₃. Determinant invariance makes this a group automorphism.
The action on the punctured coordinate axes proves containment in the concrete
split monomial subgroup. Descending the same automorphism through the full
center gives projective placement from a basis for the full inverse image.

No existence of an invariant basis is asserted for an arbitrary subgroup.
`HasNoncentralAbelianNormal` records the genuine relative-normality witness
used between the primitive exclusion and the weight-space construction.

Source: GLS3, proof of Theorem 6.5.3, decomposition (6.5.1) and case (b),
`refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open Matrix Module
open scoped Pointwise

namespace Matrix.SL3.SplitMonomial
variable {F : Type*} [Field F]
/-- The algebra automorphism that writes an endomorphism in basis coordinates. -/
noncomputable def matrixCoordinates (b : Basis (Fin 3) F (Fin 3 → F)) :
    Matrix (Fin 3) (Fin 3) F ≃ₐ[F] Matrix (Fin 3) (Fin 3) F :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)

/-- The actual SL₃ automorphism that writes matrices in the given basis. -/
noncomputable def basisChange (b : Basis (Fin 3) F (Fin 3 → F)) :
    SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F where
  toFun x := ⟨matrixCoordinates b x.val, by
    change (LinearMap.toMatrix b b (Matrix.toLin' x.val)).det = 1
    rw [LinearMap.det_toMatrix, LinearMap.det_toLin', x.property]⟩
  invFun x := ⟨(matrixCoordinates b).symm x.val, by
    change (LinearMap.toMatrix' (Matrix.toLin b b x.val)).det = 1
    rw [LinearMap.det_toMatrix', LinearMap.det_toLin, x.property]⟩
  left_inv x := Subtype.ext ((matrixCoordinates b).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((matrixCoordinates b).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((matrixCoordinates b).map_mul x.val y.val)

/-- Changing coordinates intertwines the two natural vector actions. -/
theorem basisChange_smul (b : Basis (Fin 3) F (Fin 3 → F)) (g : SpecialLinearGroup (Fin 3) F)
    (v : Fin 3 → F) :
    basisChange b g • b.equivFun v = b.equivFun (g • v) := by
  change LinearMap.toMatrix b b (Matrix.toLin' g.val) *ᵥ b.repr v = b.repr (Matrix.toLin' g.val v)
  exact LinearMap.toMatrix_mulVec_repr b b _ v

/-- An abelian subgroup normal in H and not contained in the ambient scalar
center. Normality is relative to H, not to SL₃. -/
def HasNoncentralAbelianNormal (H : Subgroup (SpecialLinearGroup (Fin 3) F)) : Prop :=
  ∃ A : Subgroup (SpecialLinearGroup (Fin 3) F), A ≤ H ∧
    (A.subgroupOf H).Normal ∧ IsMulCommutative A ∧
    ¬ A ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F)

/-- Every element carries each basis line onto another basis line. -/
def HasInvariantBasis (H : Subgroup (SpecialLinearGroup (Fin 3) F)) : Prop :=
  ∃ b : Basis (Fin 3) F (Fin 3 → F), ∀ g ∈ H, ∀ i : Fin 3,
    ∃ (j : Fin 3) (a : F), a ≠ 0 ∧ g • b i = a • b j

private theorem equivFun_smul_basis (b : Basis (Fin 3) F (Fin 3 → F))
    (a : F) (i : Fin 3) : b.equivFun (a • b i) = Pi.single i a := by
  ext j
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

private theorem coordinateVectors_eq_single {v : Fin 3 → F}
    (hv : v ∈ coordinateVectors F) : ∃ (i : Fin 3) (a : F), a ≠ 0 ∧ v = Pi.single i a := by
  obtain ⟨i, hi, hv⟩ := hv
  refine ⟨i, v i, hi, ?_⟩
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h, hv j h]

private theorem basisChange_preserves_coordinates
    (b : Basis (Fin 3) F (Fin 3 → F)) (g : SpecialLinearGroup (Fin 3) F)
    (h : ∀ i : Fin 3, ∃ (j : Fin 3) (a : F), a ≠ 0 ∧ g • b i = a • b j)
    {v : Fin 3 → F} (hv : v ∈ coordinateVectors F) :
    basisChange b g • v ∈ coordinateVectors F := by
  obtain ⟨i, a, ha, rfl⟩ := coordinateVectors_eq_single hv
  obtain ⟨j, c, hc, hg⟩ := h i
  rw [← equivFun_smul_basis b a i, basisChange_smul, smul_comm g a, hg,
    smul_smul, equivFun_smul_basis]
  exact single_mem_coordinateVectors F j (mul_ne_zero ha hc)

/-- A permuted line basis produces concrete linear monomial placement. -/
theorem exists_linear_map_le_of_invariant_basis
    (H : Subgroup (SpecialLinearGroup (Fin 3) F)) (h : HasInvariantBasis H) :
    ∃ e : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F,
      H.map e.toMonoidHom ≤ linear F := by
  obtain ⟨b, hb⟩ := h
  refine ⟨basisChange b, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  change basisChange b g ∈ MulAction.stabilizer _ (coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => basisChange_preserves_coordinates b g (hb g hg) hv)
  · rw [Set.subset_smul_set_iff, ← map_inv]
    exact Set.smul_set_subset_iff.mpr
      (fun _ hv => basisChange_preserves_coordinates b g⁻¹ (hb g⁻¹ (H.inv_mem hg)) hv)

/-- The complete inverse image under the actual central quotient. -/
def projectivePreimage (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F)) :
    Subgroup (SpecialLinearGroup (Fin 3) F) :=
  H.comap (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F)))

/-- A permuted line basis for the full inverse image produces concrete
projective monomial placement, retaining the central kernel. -/
theorem exists_projective_map_le_of_invariant_basis
    (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F))
    (h : HasInvariantBasis (projectivePreimage H)) :
    ∃ e : ProjectiveSpecialLinearGroup (Fin 3) F ≃*
        ProjectiveSpecialLinearGroup (Fin 3) F,
      H.map e.toMonoidHom ≤ projective F := by
  obtain ⟨e, he⟩ := exists_linear_map_le_of_invariant_basis (projectivePreimage H) h
  let eP := QuotientGroup.congr
    (Subgroup.center (SpecialLinearGroup (Fin 3) F))
    (Subgroup.center (SpecialLinearGroup (Fin 3) F)) e
    (Subgroup.characteristic_iff_map_eq.mp inferInstance e)
  refine ⟨eP, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin 3) F)) x
  refine ⟨e g, he (Subgroup.mem_map_of_mem e.toMonoidHom hx), ?_⟩
  rfl
end Matrix.SL3.SplitMonomial

