module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Solvable Sylow overgroups generating PSL₃ in odd characteristic

A common Sylow two-subgroup lies in the centralizer of diag(-1,-1,1),
using the single involution class in SL₃. It normalizes the abelian radicals
of the stabilizers of the plane v₂=0 and its complementary coordinate line.
Adjoining the Sylow subgroup to each radical gives two solvable subgroups.
The opposite radicals generate SL₃: they contain x₀₂, x₁₂, x₂₀ and x₂₁,
and commutators give x₀₁ and x₁₀. Elementary generation finishes the proof.
The literal central quotient transports the pair to PSL₃.

This supplies the matrix input for Aschbacher--Smith, *The Classification of
Quasithin Groups*, E.1.14(7), printed p.214, via E.1.12--13. In particular,
the prime five requires no separate PSL₂ generation theorem. The matrix
calculation works over every finite field of characteristic different from two.
The elementary generation identities are reused from the attributed ATLAS
port `Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`; its source
attribution and license remain in that module and `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise commutatorElement
namespace Matrix.PSL3.OddSolvableGeneration
variable (F : Type*) [Field F] [Finite F]
open LinearThree OuterSolvable

private def complementaryPointSL : Subgroup SL(3, F) :=
  MulAction.stabilizer SL(3, F) {v : Fin 3 → F | v 0 = 0 ∧ v 1 = 0}

private theorem mem_complementaryPointSL_iff (g : SL(3, F)) :
    g ∈ complementaryPointSL F ↔ g.val 0 2 = 0 ∧ g.val 1 2 = 0 := by
  rw [complementaryPointSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → F⦄, v 0 = 0 ∧ v 1 = 0 →
    (g.val.mulVec v) 0 = 0 ∧ (g.val.mulVec v) 1 = 0) ↔ _
  constructor
  · intro h
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using
      h (v := ![0, 0, 1]) (by simp)
  · rintro ⟨h0, h1⟩ v ⟨v0, v1⟩
    simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1, v0, v1]

private theorem graphSL_map_lineParabolic :
    (lineParabolicSL F).map (graphSL F).toMonoidHom = complementaryPointSL F := by
  ext x
  obtain ⟨g, rfl⟩ := (graphSL F).surjective x
  rw [Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  change g ∈ lineParabolicSL F ↔
    (SpecialLinearGroup.transpose g)⁻¹ ∈ complementaryPointSL F
  rw [inv_mem_iff, mem_complementaryPointSL_iff, mem_lineParabolicSL_iff]
  rfl

private theorem centralizer_le_parabolics (h2 : (2 : F) ≠ 0) :
    centralizer ({SL3.standardInvolution F} : Set SL(3, F)) ≤
      lineParabolicSL F ⊓ complementaryPointSL F := by
  intro g hg
  have h := (SL3.mem_standardInvolution_centralizer_iff F h2 g).mp hg
  rw [mem_inf, mem_lineParabolicSL_iff, mem_complementaryPointSL_iff]
  exact ⟨⟨h.2.2.1, h.2.2.2⟩, ⟨h.1, h.2.1⟩⟩

private theorem exists_sylowTwo_le_parabolicsSL (h2 : (2 : F) ≠ 0) :
    ∃ T : Sylow 2 SL(3, F), (T : Subgroup SL(3, F)) ≤ lineParabolicSL F ∧
      (T : Subgroup SL(3, F)) ≤ complementaryPointSL F := by
  let C := centralizer ({SL3.standardInvolution F} : Set SL(3, F))
  have hi : Odd C.index := odd_index_centralizer_of_one_involution_class _
    (SL3.standardInvolution_orderOf F h2)
    (fun w hw => SL3.involution_isConj_standard F w hw h2)
  let P : Sylow 2 C := Classical.choice inferInstance
  let S := (P : Subgroup C).map C.subtype
  have hS : IsPGroup 2 S := P.isPGroup'.map C.subtype
  have hindex : ¬ 2 ∣ S.index := by
    rw [show S.index = (P : Subgroup C).index * C.index from index_map_subtype _]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hi.not_two_dvd_nat
  let T : Sylow 2 SL(3, F) := hS.toSylow hindex
  have hTC : (T : Subgroup SL(3, F)) ≤ C := map_subtype_le _
  exact ⟨T, (hTC.trans (centralizer_le_parabolics F h2)).trans inf_le_left,
    (hTC.trans (centralizer_le_parabolics F h2)).trans inf_le_right⟩

open RootPlaneGeometry Matrix.PSL3Even.UnipotentGeometry

private def upperRadicalSL : Subgroup SL(3, F) := rootPlaneSL F false
private def lowerRadicalSL : Subgroup SL(3, F) :=
  (upperRadicalSL F).map (graphSL F).toMonoidHom

private theorem lineParabolicSL_le_normalizer_upperRadicalSL :
    lineParabolicSL F ≤ normalizer (upperRadicalSL F : Set SL(3, F)) :=
  parabolicSL_le_normalizer_rootPlaneSL F false

private theorem complementaryPointSL_le_normalizer_lowerRadicalSL :
    complementaryPointSL F ≤ normalizer (lowerRadicalSL F : Set SL(3, F)) := by
  rw [← graphSL_map_lineParabolic]
  exact (Subgroup.map_mono (lineParabolicSL_le_normalizer_upperRadicalSL F)).trans
    (Subgroup.le_normalizer_map _)

private instance upperRadicalSL_isSolvable : Group.IsSolvable (upperRadicalSL F) := by
  let : Group.IsSolvable (V₂ F) := Group.isSolvable_of_surjective (plane₂Equiv F).surjective
  exact Group.isSolvable_of_surjective ((specialLinear F).subgroupMap_surjective (V₂ F))

private instance lowerRadicalSL_isSolvable : Group.IsSolvable (lowerRadicalSL F) :=
  Group.isSolvable_of_surjective
    ((graphSL F).toMonoidHom.subgroupMap_surjective (upperRadicalSL F))

omit [Finite F] in
private theorem upper_transvection_mem (i : Fin 3) (hi : i ≠ 2) (a : F) :
    SpecialLinearGroup.transvection hi a ∈ upperRadicalSL F := by
  apply (mem_rootPlaneSL_line F _).mpr
  fin_cases i
  · refine ⟨0, a, ?_⟩
    apply Subtype.ext
    change matrix F ⟨0, 0, a⟩ = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe]
  · refine ⟨a, 0, ?_⟩
    apply Subtype.ext
    change matrix F ⟨0, a, 0⟩ = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe]
  · exact (hi rfl).elim

omit [Finite F] in
private theorem graphSL_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) :
    graphSL F (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm (-a) := by
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a))⁻¹ = _
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transpose, SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add, Matrix.transpose_single]
  rw [h, SpecialLinearGroup.transvection_inv]

omit [Finite F] in
private theorem lower_transvection_mem (j : Fin 3) (hj : (2 : Fin 3) ≠ j) (a : F) :
    SpecialLinearGroup.transvection hj a ∈ lowerRadicalSL F := by
  refine ⟨SpecialLinearGroup.transvection hj.symm (-a),
    upper_transvection_mem F j hj.symm (-a), ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, graphSL_transvection, neg_neg]

omit [Finite F] in
private theorem radicalsSL_sup_eq_top : upperRadicalSL F ⊔ lowerRadicalSL F = ⊤ := by
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction
    (fun x => x ∈ upperRadicalSL F ⊔ lowerRadicalSL F) _
    (fun _ _ => Subgroup.mul_mem _) g
  intro i j hij a
  by_cases hi : i = 2
  · subst i
    exact mem_sup_right (lower_transvection_mem F j hij a)
  by_cases hj : j = 2
  · subst j
    exact mem_sup_left (upper_transvection_mem F i hij a)
  rw [← mul_one a, ← Atlas.elementary_commutator hij hi (Ne.symm hj) a 1]
  let H := upperRadicalSL F ⊔ lowerRadicalSL F
  have h₁ : SpecialLinearGroup.transvection hi a ∈ H :=
    mem_sup_left (upper_transvection_mem F i hi a)
  have h₂ : SpecialLinearGroup.transvection (Ne.symm hj) 1 ∈ H :=
    mem_sup_right (lower_transvection_mem F j (Ne.symm hj) 1)
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

/-- Two solvable overgroups of a common Sylow two-subgroup generate SL₃. -/
theorem exists_solvable_generating_pairSL (h2 : (2 : F) ≠ 0) :
    ∃ (T : Sylow 2 SL(3, F)) (P Q : Subgroup SL(3, F)),
      (T : Subgroup SL(3, F)) ≤ P ∧ (T : Subgroup SL(3, F)) ≤ Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧ P ⊔ Q = ⊤ := by
  obtain ⟨T, hTl, hTp⟩ := exists_sylowTwo_le_parabolicsSL F h2
  let := T.isPGroup'.isNilpotent
  let P := upperRadicalSL F ⊔ (T : Subgroup SL(3, F))
  let Q := lowerRadicalSL F ⊔ (T : Subgroup SL(3, F))
  have hP : Group.IsSolvable P := Group.isSolvable_sup_of_normalizes _ _
    (hTl.trans (lineParabolicSL_le_normalizer_upperRadicalSL F))
  have hQ : Group.IsSolvable Q := Group.isSolvable_sup_of_normalizes _ _
    (hTp.trans (complementaryPointSL_le_normalizer_lowerRadicalSL F))
  refine ⟨T, P, Q, le_sup_right, le_sup_right, hP, hQ, ?_⟩
  apply top_unique
  rw [← radicalsSL_sup_eq_top F]
  exact sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)

/-- The same generating pair in the actual quotient PSL₃. -/
theorem exists_solvable_generating_pair (h2 : (2 : F) ≠ 0) :
    ∃ (T : Sylow 2 PSL(3, F)) (P Q : Subgroup PSL(3, F)),
      (T : Subgroup PSL(3, F)) ≤ P ∧ (T : Subgroup PSL(3, F)) ≤ Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧ P ⊔ Q = ⊤ := by
  obtain ⟨T, P, Q, hTP, hTQ, hP, hQ, hPQ⟩ := exists_solvable_generating_pairSL F h2
  let _ := hP
  let _ := hQ
  refine ⟨T.mapSurjective (f := projection F) (projection_surjective F),
    P.map (projection F), Q.map (projection F), map_mono hTP, map_mono hTQ,
    Group.isSolvable_of_surjective ((projection F).subgroupMap_surjective P),
    Group.isSolvable_of_surjective ((projection F).subgroupMap_surjective Q), ?_⟩
  rw [← Subgroup.map_sup, hPQ, map_top_of_surjective _ (projection_surjective F)]

end Matrix.PSL3.OddSolvableGeneration
