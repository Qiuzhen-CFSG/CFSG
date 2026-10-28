module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.Model

/-!
# Orthogonal normalization of graph-centralizing linear automorphisms

If conjugation by a matrix A commutes with inverse transpose on PSL₃(4),
then A and its inverse transpose induce the same projective automorphism.
The kernel of the linear action consists of scalar matrices: trace removes
central ambiguity on transvections, whose commutation equations force a
matrix to be scalar. Thus AᵀA = rI for a nonzero scalar r.

Every nonzero element of GF(4) has cube one, so rA is orthogonal. Its
determinant has square one and hence is one in characteristic two. It
therefore belongs to the actual inverse-transpose fixed subgroup of SL₃(4),
and its projective inner action is the original linear action.

The local scalar-kernel calculations are adapted from
`PSL3/FieldComponentFixer.lean`; the inverse-transpose conjugation identity
is adapted from `ProjectiveFixer/StandardForms.lean`. This supplies the
linear normalization input to the graph-centralizer calculation used in
Aschbacher–Smith 16.1.4(6), printed p.1171, and the quaternion application
on printed p.1192, `refs/quasithin.pdf` (1 March 2004 manuscript).
-/

public section

noncomputable section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph

private theorem scalar_of_projective_eq (x y : SL(3,F))
    (h : (QuotientGroup.mk x : PSL(3,F)) = QuotientGroup.mk y) :
    ∃ r : F, x.val = r • y.val := by
  have hc : y⁻¹ * x ∈ Subgroup.center SL(3,F) := QuotientGroup.eq.mp h.symm
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem trace_transvection {i j : Fin 3} (hij : i ≠ j) (c : F) :
    Matrix.trace (SpecialLinearGroup.transvection hij c).val = 1 := by
  simp [SpecialLinearGroup.transvection_coe, Matrix.trace_add, hij, Matrix.trace_one]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination htwo

private theorem conjugate_transvection_eq
    (m : GL (Fin 3) F) {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (a b : F) (h : linearConj F m (rootElement hij a) = rootElement hkl b) :
    m.val * (1 + Matrix.single i j a) = (1 + Matrix.single k l b) * m.val := by
  obtain ⟨r, hr⟩ := scalar_of_projective_eq
    (linearConjSL F m (SpecialLinearGroup.transvection hij a))
    (SpecialLinearGroup.transvection hkl b) h
  have hv (x : SL(3,F)) : (linearConjSL F m x).val = m.val * x.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m x)
  have ht : Matrix.trace (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val = 1 := by
    rw [hv, Matrix.trace_mul_cycle, m.inv_val, one_mul, trace_transvection]
  rw [hr, Matrix.trace_smul, trace_transvection, smul_eq_mul, mul_one] at ht
  have he : (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val =
      (SpecialLinearGroup.transvection hkl b).val := by simpa [ht] using hr
  have he' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M * m.val) he
  simpa only [hv, Matrix.mul_assoc, m.inv_val, mul_one,
    SpecialLinearGroup.transvection_coe] using he'

private theorem matrix_scalar_of_fixes_roots
    (m : GL (Fin 3) F)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j),
      linearConj F m (rootElement hij 1) = rootElement hij 1) :
    m.val = Matrix.scalar (Fin 3) (m.val 0 0) := by
  have he (i j : Fin 3) (hij : i ≠ j) :
      m.val * Matrix.single i j 1 = Matrix.single i j 1 * m.val := by
    have hh := conjugate_transvection_eq m hij hij 1 1 (h i j hij)
    simpa only [mul_add, add_mul, mul_one, one_mul, add_right_inj] using hh
  have hz (k i : Fin 3) (hki : k ≠ i) : m.val k i = 0 := by
    obtain ⟨j, hij⟩ := exists_ne i
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M k j) (he i j hij.symm)
    simpa [Matrix.mul_apply, Matrix.single_apply, hki, Ne.symm hki] using hh
  have hd (i j : Fin 3) : m.val i i = m.val j j := by
    by_cases hij : i = j
    · subst j; rfl
    · have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) (he i j hij)
      simpa [Matrix.mul_apply, Matrix.single_apply] using hh
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.scalar] using hd i 0
  · simp [Matrix.scalar, hij, hz i j hij]

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL(3,F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem graph_linearConj (A : GL (Fin 3) F) :
    graph F * linearConj F A = linearConj F (inverseTransposeGL A) * graph F := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk (graphSL F (linearConjSL F A x)) =
      QuotientGroup.mk (linearConjSL F (inverseTransposeGL A) (graphSL F x))
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, graphSL_toGL]


private theorem gram_scalar (A : GL (Fin 3) F)
    (h : Commute (linearConj F A) (graph F)) :
    ∃ r : F, r ≠ 0 ∧ A.val.transpose * A.val = r • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have he : linearConj F A = linearConj F (inverseTransposeGL A) := by
    apply mul_right_cancel (b := graph F)
    exact h.eq.trans (graph_linearConj A)
  let B := (inverseTransposeGL A)⁻¹ * A
  have hB : linearConj F B = 1 := by
    dsimp [B]
    rw [map_mul, map_inv, ← he, inv_mul_cancel]
  have hs := matrix_scalar_of_fixes_roots B (fun i j hij => by
    rw [hB]; rfl)
  have hv : B.val = A.val.transpose * A.val := rfl
  refine ⟨B.val 0 0, ?_, ?_⟩
  · intro hz
    have hzB : B.val = 0 := by
      rw [hz, map_zero] at hs
      exact hs
    have hh := B.val_inv
    rw [hzB, zero_mul] at hh
    exact zero_ne_one hh
  · rw [← hv, hs]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, hij]

private theorem linearConj_scalar (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) y
  change QuotientGroup.mk (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) =
    QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]


/-- Every linear automorphism of PSL₃(4) commuting with the graph involution
is induced by an actual inverse-transpose fixed determinant-one matrix. -/
theorem linearConj_eq_inner_of_commute_graph
    (A : GL (Fin 3) F) (h : Commute (linearConj F A) (graph F)) :
    ∃ x : Fixed, linearConj F A = inner x := by
  obtain ⟨r, hr, hgram⟩ := gram_scalar A h
  have hr3 : r ^ 3 = 1 := by
    apply mul_right_cancel₀ hr
    simpa only [← pow_succ, one_mul] using pow_four r
  let N : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr) * A
  have hN : N.val = r • A.val := by
    ext i j
    simp [N, GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal_mul]
  have horth : N.val.transpose * N.val = 1 := by
    rw [hN, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hgram,
      smul_smul, smul_smul]
    have hh : r * r * r = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hr3
    rw [hh, one_smul]
  have hdet : N.val.det = 1 := by
    apply CharTwo.sq_injective
    have hd := congrArg Matrix.det horth
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two, one_mul]
      using hd
  let x : Fixed := ⟨⟨N.val, hdet⟩, (GraphFixed.mem_graphSL_fixed_iff F _).mpr horth⟩
  refine ⟨x, ?_⟩
  have hx : SpecialLinearGroup.toGL x.val = N := Units.ext rfl
  have hi : linearConj F N = inner x := by
    rw [← hx]
    exact linearConj_toGL F x.val
  rw [← hi]
  change linearConj F A = linearConj F
    (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr) * A)
  rw [map_mul, linearConj_scalar, one_mul]

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph
