module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.UniversalKernel
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.StandardForms
public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity

/-!
# Removing field, graph and inner factors from a cubic standard actor

The field and graph factors of a standard automorphism of PSL₃(4) are commuting
involutions and normalize the linear conjugation image. Thus every standard
square is linear, and every standard cube-one actor is linear. Correcting its
matrix determinant with `diag(u,1,1)` leaves an inner factor. An outer actor
has `u ≠ 1`. Inner factors act trivially on the universal covering kernel.

These are unconditional matrix reductions for the diagonal action used in
Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of 1 March 2004.
They do not calculate the action on the exceptional multiplier. The standard
actions and their normalization identities are the matrix descriptions in
GLS3, §2.7; the private identities follow the existing `StandardForms` proofs.
-/

public section

open scoped MatrixGroups
open Subgroup PerfectCentralCovering Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
private theorem fieldSL_toGL (σ : F ≃+* F) (x : SL) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom x) =
      GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) := Units.ext rfl

private theorem field_linearConj (σ : F ≃+* F) (A : GL (Fin 3) F) :
    PSL3.OuterSolvable.fieldAction F σ * linearConj F A =
      linearConj F (GeneralLinearGroup.map σ.toRingHom A) *
        PSL3.OuterSolvable.fieldAction F σ := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, linearConj_mk]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [fieldSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, fieldSL_toGL]

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL) :
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

private theorem field_commute_graph (σ : F ≃+* F) :
    Commute (PSL3.OuterSolvable.fieldAction F σ) (graph F) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, graph_mk]
    rw [map_inv]
    congr 2

private theorem coefficient_eq_one_or_frobenius (σ : F ≃+* F) :
    σ = 1 ∨ σ = fieldFrobenius := by
  classical
  have hs : fieldFrobenius ^ 2 = 1 := by
    ext x
    exact fieldFrobenius_involutive x
  have hn : fieldFrobenius ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (congrArg (fun τ : F ≃+* F => τ x) he)
  have ho : orderOf fieldFrobenius = 2 := orderOf_eq_prime hs hn
  have hm : σ ∈ zpowers fieldFrobenius := by
    rw [← PSL3.FieldComponentFixer.coefficient_fixer_eq_zpowers]
    intro x
    rcases eq_zero_or_one_of_sq_eq_self x.property with hx | hx
    · change σ x.val = x.val
      rw [hx, map_zero]
    · change σ x.val = x.val
      rw [hx, map_one]
  have hf : IsOfFinOrder fieldFrobenius :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hn' : n < 2 := by simpa only [Finset.mem_range, ho] using hn
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)


private theorem coefficient_sq (σ : F ≃+* F) : σ ^ 2 = 1 := by
  rcases coefficient_eq_one_or_frobenius σ with rfl | rfl
  · exact one_pow _
  · ext x
    exact fieldFrobenius_involutive x

private theorem square_linear_product (A : GL (Fin 3) F) (r : MulAut PSL)
    (hr : r ^ 2 = 1)
    (hAr : ∃ B : GL (Fin 3) F, r * linearConj F A = linearConj F B * r) :
    (linearConj F A * r) ^ 2 ∈ innerDiagonal F := by
  obtain ⟨B, hB⟩ := hAr
  refine ⟨A * B, ?_⟩
  rw [map_mul]
  calc
    linearConj F A * linearConj F B =
        linearConj F A * (linearConj F B * r) * r := by
          have hr' : r * r = 1 := by simpa only [pow_two] using hr
          simp only [mul_assoc, hr', mul_one]
    _ = (linearConj F A * r) ^ 2 := by rw [← hB]; simp only [pow_two, mul_assoc]

theorem standard_square_mem_innerDiagonal (β : MulAut PSL)
    (hβ : β ∈ standard F) : β ^ 2 ∈ innerDiagonal F := by
  obtain ⟨A, σ, t, rfl⟩ := ProjectiveFixer.exists_standardForm β hβ
  have hσ : PSL3.OuterSolvable.fieldAction F σ ^ 2 = 1 := by
    rw [← map_pow, coefficient_sq, map_one]
  have ht : t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) := by
    exact (by decide : ∀ t : C2, t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2)) t
  rcases ht with rfl | rfl
  · simp only [ProjectiveFixer.standardForm, map_one, mul_one]
    exact square_linear_product A _ hσ ⟨_, field_linearConj σ A⟩
  · simp only [ProjectiveFixer.standardForm, involutionHom_generator, mul_assoc]
    apply square_linear_product
    · rw [(field_commute_graph σ).mul_pow, hσ, graph_sq, one_mul]
    · refine ⟨GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL A), ?_⟩
      rw [mul_assoc, graph_linearConj, ← mul_assoc, field_linearConj, mul_assoc]

theorem cubic_standard_mem_innerDiagonal (β : MulAut PSL)
    (hβ : β ∈ standard F) (h3 : β ^ 3 = 1) : β ∈ innerDiagonal F := by
  have h := (innerDiagonal F).inv_mem (standard_square_mem_innerDiagonal β hβ)
  have hi : (β ^ 2)⁻¹ = β := inv_eq_of_mul_eq_one_left (by
    simpa only [← pow_succ'] using h3)
  rwa [hi] at h

/-- The one-coordinate diagonal matrix with determinant `u`. -/
@[expose] noncomputable def determinantDiagonal (u : Fˣ) : GL (Fin 3) F :=
  OddPrimeCoverage.diagonalGL ![u, 1, 1]

/-- Its action on the actual projective special linear group. -/
@[expose] noncomputable def diagonalRepresentative (u : Fˣ) : MulAut PSL :=
  linearConj F (determinantDiagonal u)

theorem determinantDiagonal_det (u : Fˣ) :
    GeneralLinearGroup.det (determinantDiagonal u) = u := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal (fun i => (![u, 1, 1] i : F))) = (u : F)
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

theorem determinantDiagonal_one : determinantDiagonal 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem linearConj_eq_diagonal_mul_inner (A : GL (Fin 3) F) :
    ∃ g : PSL, linearConj F A =
      diagonalRepresentative (GeneralLinearGroup.det A) * MulAut.conj g := by
  let m := (determinantDiagonal (GeneralLinearGroup.det A))⁻¹ * A
  have hm : GeneralLinearGroup.det m = 1 := by
    simp only [m, map_mul, map_inv, determinantDiagonal_det, inv_mul_cancel]
  let x := (slEquivDetKernel F).symm ⟨m, hm⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [← linearConj_toGL, slEquivDetKernel_symm_toGL]
  change linearConj F A = linearConj F _ * linearConj F m
  rw [← map_mul]
  congr 1
  exact (mul_inv_cancel_left _ A).symm

/-- Every outer cubic standard actor has a nontrivial diagonal determinant,
up to an inner factor. No conjugacy choice on a covering group is involved. -/
theorem cubic_standard_eq_diagonal_mul_inner (β : MulAut PSL)
    (hβ : β ∈ standard F) (h3 : β ^ 3 = 1)
    (hout : β ∉ MulAut.innerSubgroup PSL) :
    ∃ (u : Fˣ) (g : PSL), u ≠ 1 ∧ β = diagonalRepresentative u * MulAut.conj g := by
  obtain ⟨A, rfl⟩ := cubic_standard_mem_innerDiagonal β hβ h3
  obtain ⟨g, hg⟩ := linearConj_eq_diagonal_mul_inner A
  refine ⟨GeneralLinearGroup.det A, g, ?_, hg⟩
  intro hdet
  apply hout
  rw [hg, hdet, diagonalRepresentative, determinantDiagonal_one, map_one, one_mul]
  exact ⟨g, rfl⟩


end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
