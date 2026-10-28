module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.LinearFour
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.KernelCalculation
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The split monomial witness with inverse transpose adjoined

The literal coordinate-axis stabilizer has a normal diagonal four-group with
abelian centralizer, so its action on the three nonidentity signs proves
solvability. Inverse transpose normalizes this stabilizer. Their join in the
actual graph extension is therefore solvable and contains a determinant-one
signed swap fixing coordinate zero and mixing coordinates one and two.

This generalizes the matrix argument in
`OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Solvability`.
The full ambient Sylow placement is a separate centralizer-index calculation.
Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209--210,
214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup
open scoped MatrixGroups Matrix Pointwise IsMulCommutative
open Matrix.PSL3.OddPrimeGraphExtension

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The full split monomial image, with the actual inverse-transpose element. -/
@[expose] def splitMonomialOvergroup : Subgroup (graphExtension F) :=
  (Matrix.SL3.SplitMonomial.linear F).map (innerSL F) ⊔ zpowers (graphElement F)

private theorem linear_solvable (hodd : Odd (Nat.card F)) : Group.IsSolvable (Matrix.SL3.SplitMonomial.linear F) := by
  obtain ⟨V, hV, hc, hC⟩ := Matrix.SL3.SplitMonomial.linear_normal_four F
    hodd
  let := hV
  let D := Matrix.SL3.SplitMonomial.LocalCore.threePointStructureOfNormalFour V hc hC
  let : IsMulCommutative D.action.ker := D.kernel_commutative
  let : Group.IsSolvable D.action.ker := Group.isSolvable_of_comm (fun _ _ => mul_comm _ _)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let e : Fin 3 ↪ Fin 4 := ⟨Fin.castSucc, Fin.castSucc_injective 3⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  exact Group.isSolvable_of_ker_le_range D.action.ker.subtype D.action (by rw [range_subtype])

omit [Finite F] in
open Matrix.SL3.SplitMonomial in
private theorem column_support (g : linear F) (j : Fin 3) :
    ∃ i, g.val i j ≠ 0 ∧ ∀ r, r ≠ i → g.val r j = 0 := by
  have hstab : g.val • coordinateVectors F = coordinateVectors F :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv : g.val • Pi.single j (1 : F) ∈ coordinateVectors F := by
    rw [← hstab]
    exact Set.smul_mem_smul_set (single_mem_coordinateVectors F j one_ne_zero)
  simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.mulVec_single_one, coordinateVectors, Set.mem_ofPred_eq, Matrix.col_apply] using hv

omit [Finite F] in
open Matrix.SL3.SplitMonomial in
private theorem column_permutation (g : linear F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ j,
      g.val (σ j) j ≠ 0 ∧ ∀ i, i ≠ σ j → g.val i j = 0 := by
  classical
  let p : Fin 3 → Fin 3 := fun j => (column_support F g j).choose
  have hp (j r : Fin 3) (h : r ≠ p j) : g.val r j = 0 :=
    (column_support F g j).choose_spec.2 r h
  have hs : Function.Surjective p := by
    intro i
    by_contra h
    have hz (j : Fin 3) : g.val i j = 0 := hp j i (fun he => h ⟨j, he.symm⟩)
    have hh := congrArg (fun A : SL(3, F) => A i i) (mul_inv_cancel g.val)
    change (g.val.val * (g.val⁻¹).val) i i = (1 : Matrix (Fin 3) (Fin 3) F) i i at hh
    simp only [Matrix.one_apply_eq, Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  exact ⟨Equiv.ofBijective p ⟨Finite.injective_iff_surjective.mpr hs, hs⟩,
    fun j => (column_support F g j).choose_spec⟩

omit [Finite F] in
open Matrix.SL3.SplitMonomial in
private theorem transpose_preserves (g : linear F) {v : Fin 3 → F}
    (hv : v ∈ coordinateVectors F) :
    Matrix.SpecialLinearGroup.transpose g.val • v ∈ coordinateVectors F := by
  classical
  obtain ⟨σ, hσ⟩ := column_permutation F g
  obtain ⟨j, hj, hv⟩ := hv
  have he : v = Pi.single j (v j) := by
    ext i
    by_cases hi : i = j
    · simp [hi]
    · simp [hi, hv i hi]
  rw [he]
  have heval (r : Fin 3) :
      (Matrix.SpecialLinearGroup.transpose g.val • (Pi.single j (v j) : Fin 3 → F)) r = g.val j r * v j := by
    simp [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single,
      Matrix.SpecialLinearGroup.coe_transpose]
  refine ⟨σ.symm j, ?_, ?_⟩
  · rw [heval]
    exact mul_ne_zero (by simpa using (hσ (σ.symm j)).1) hj
  · intro r hr
    rw [heval, (hσ r).2 j (by intro h; apply hr; exact (σ.symm_apply_eq.mpr h).symm), zero_mul]

omit [Finite F] in
open Matrix.SL3.SplitMonomial in
private theorem transpose_mem_linear (g : SL(3, F)) (hg : g ∈ linear F) :
    Matrix.SpecialLinearGroup.transpose g ∈ linear F := by
  change Matrix.SpecialLinearGroup.transpose g ∈ MulAction.stabilizer _ (coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => transpose_preserves F ⟨g, hg⟩ hv)
  · rw [Set.subset_smul_set_iff]
    have hi : (Matrix.SpecialLinearGroup.transpose g)⁻¹ = Matrix.SpecialLinearGroup.transpose g⁻¹ :=
      Subtype.ext (Matrix.adjugate_transpose g.val).symm
    rw [hi]
    exact Set.smul_set_subset_iff.mpr
      (fun _ hv => transpose_preserves F ⟨g⁻¹, (linear F).inv_mem hg⟩ hv)


omit [Finite F] in
/-- Inverse transpose conjugates the actual matrix image by the literal formula. -/
theorem split_graph_innerSL (x : SL(3,F)) :
    graphElement F * innerSL F x * (graphElement F)⁻¹ =
      innerSL F ((Matrix.SpecialLinearGroup.transpose x)⁻¹) := by
  symm
  apply Subtype.ext
  change MulAut.conj (Matrix.PSL3.projection F (Matrix.PSL3.OuterSolvable.graphSL F x)) =
    Matrix.PSL3.OuterSolvable.graph F * MulAut.conj (Matrix.PSL3.projection F x) *
      (Matrix.PSL3.OuterSolvable.graph F)⁻¹
  have he : Matrix.PSL3.projection F (Matrix.PSL3.OuterSolvable.graphSL F x) =
      Matrix.PSL3.OuterSolvable.graph F (Matrix.PSL3.projection F x) := rfl
  rw [he]
  ext y
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

/-- Graph normalizes the full linear monomial image, not just its two-subgroups. -/
theorem split_graph_normalizes :
    graphElement F ∈ normalizer
      ((Matrix.SL3.SplitMonomial.linear F).map (innerSL F) : Set (graphExtension F)) := by
  apply mem_normalizer_fintype
  rintro _ ⟨g, hg, rfl⟩
  rw [split_graph_innerSL]
  exact ⟨(Matrix.SpecialLinearGroup.transpose g)⁻¹,
    (Matrix.SL3.SplitMonomial.linear F).inv_mem (transpose_mem_linear F g hg), rfl⟩

/-- The split monomial subgroup with graph adjoined is solvable over every odd finite field. -/
theorem splitMonomialOvergroup_solvable (hodd : Odd (Nat.card F)) :
    Group.IsSolvable (splitMonomialOvergroup F) := by
  let : Group.IsSolvable (Matrix.SL3.SplitMonomial.linear F) := linear_solvable F hodd
  let : Group.IsSolvable ((Matrix.SL3.SplitMonomial.linear F).map (innerSL F)) :=
    Group.isSolvable_of_surjective ((innerSL F).subgroupMap_surjective _)
  exact Group.isSolvable_sup_of_normalizes _ _ (zpowers_le.mpr (split_graph_normalizes F))

/-- An orthogonal signed swap of the last two coordinates, of determinant one. -/
@[expose] def splitMixingMatrix : SL(3,F) :=
  ⟨!![1,0,0; 0,0,1; 0,-1,0], by simp [Matrix.det_fin_three]⟩

omit [Finite F] in
/-- This signed swap is the literal off-block witness in the generation predicate. -/
theorem splitMixingMatrix_mixes : MixesSecondPlane F (splitMixingMatrix F) :=
  ⟨rfl, rfl, rfl, rfl, rfl, one_ne_zero⟩

omit [Finite F] in
private theorem splitMixingMatrix_preserves {v : Fin 3 → F}
    (hv : v ∈ Matrix.SL3.SplitMonomial.coordinateVectors F) :
    splitMixingMatrix F • v ∈ Matrix.SL3.SplitMonomial.coordinateVectors F := by
  obtain ⟨i, hi, hv⟩ := hv
  have he (j : Fin 3) : (splitMixingMatrix F • v) j =
      ![v 0, v 2, -v 1] j := by
    change ((splitMixingMatrix F).val *ᵥ v) j = _
    fin_cases j <;> simp [splitMixingMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
  fin_cases i
  · refine ⟨0, by simpa [he] using hi, ?_⟩
    intro j hj
    fin_cases j <;> simp_all
  · refine ⟨2, by simpa [he] using hi, ?_⟩
    intro j hj
    fin_cases j <;> simp_all
  · refine ⟨1, by simpa [he] using hi, ?_⟩
    intro j hj
    fin_cases j <;> simp_all

/-- The witness belongs to the actual coordinate-axis stabilizer. -/
theorem splitMixingMatrix_mem_linear :
    splitMixingMatrix F ∈ Matrix.SL3.SplitMonomial.linear F := by
  change splitMixingMatrix F ∈ MulAction.stabilizer _ (Matrix.SL3.SplitMonomial.coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.eq_of_subset_of_ncard_le
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => splitMixingMatrix_preserves F hv)
  · exact le_of_eq (Set.ncard_smul_set _ _).symm
  · exact Set.toFinite _

/-- The full graph overgroup contains the actual mixing matrix image. -/
theorem splitMixingMatrix_mem : innerSL F (splitMixingMatrix F) ∈ splitMonomialOvergroup F :=
  mem_sup_left (mem_map_of_mem _ (splitMixingMatrix_mem_linear F))

omit [Finite F] in
/-- Inverse transpose fixes the marked involution. -/
theorem split_graph_centralizes_standard :
    graphElement F ∈ centralizer ({standardInner F} : Set (graphExtension F)) := by
  have ht : Matrix.SpecialLinearGroup.transpose (Matrix.SL3.standardInvolution F) =
      Matrix.SL3.standardInvolution F := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hi : (Matrix.SL3.standardInvolution F)⁻¹ = Matrix.SL3.standardInvolution F :=
    inv_eq_of_mul_eq_one_left ((pow_two _).symm.trans (Matrix.SL3.standardInvolution_sq F))
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  change graphElement F * innerSL F (Matrix.SL3.standardInvolution F) * _ = _
  rw [split_graph_innerSL, ht, hi]
  rfl

omit [Finite F] in
/-- The chosen orthogonal mixing matrix is fixed by inverse transpose as well. -/
theorem split_graph_centralizes_mixing :
    graphElement F ∈ centralizer ({innerSL F (splitMixingMatrix F)} : Set (graphExtension F)) := by
  have hi : (Matrix.SpecialLinearGroup.transpose (splitMixingMatrix F))⁻¹ =
      splitMixingMatrix F := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change (splitMixingMatrix F).val * (splitMixingMatrix F).val.transpose = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitMixingMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  rw [split_graph_innerSL, hi]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
