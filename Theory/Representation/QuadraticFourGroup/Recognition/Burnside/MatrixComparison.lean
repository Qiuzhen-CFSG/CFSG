module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.Coordinates
public import Theory.Representation.QuadraticFourGroup.Models
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Algebra.CharP.Two

/-!
# The translation and reciprocal group is PSL₂ in characteristic two

The action of SL₂ on the projective line `Option K` has kernel exactly its
center: fixing infinity, zero and one forces a matrix to be scalar, and every
central scalar acts trivially. In characteristic two, the coordinate-swap
matrix has determinant one and induces reciprocal. Upper transvections induce
translations; conjugating them by the swap matrix gives lower transvections.
Transvection generation therefore identifies the action image with the concrete
`projectiveGroup K` of `Coordinates.lean`. The first isomorphism theorem gives
an equivalence with the literal central quotient `PSL(2, K)`.

The finite-field specialization supplies the matrix comparison for Burnside
recognition, independently of the construction of coordinates on an ambient
group. The inverse equivalence sends each matrix class to its actual projective
permutation, as certified by `projectiveGroupEquivPSL_symm_apply`.

Source: W. Burnside, *On a Class of Groups of Finite Order* (1900), printed
p. 275, `refs/original/burnside-1900.pdf`. The three-point kernel calculation
also follows the projective-action argument in
`BenderSuzuki/External/Huppert/XI/theorem_2_6.lean`; only Mathlib's projective
line action is used here, with no dependency on that campaign.
-/

noncomputable section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.QuadraticFourGroup.Burnside.MatrixComparison
variable (K : Type*) [Field K]

local instance : DecidableEq K := Classical.decEq K
/-- The actual fractional-linear permutation action of determinant-one matrices. -/
@[expose] public noncomputable def sl2PermHom : SL(2, K) →* Equiv.Perm (Option K) := by
  classical
  exact (MulAction.toPermHom (GL (Fin 2) K) (OnePoint K)).comp toGL

private theorem scalar_of_fixes (g : SL(2, K))
    (hfix : ∀ x : OnePoint K, toGL g • x = x) :
    g ∈ Subgroup.center SL(2, K) := by
  classical
  have h10 : g 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (hfix OnePoint.infty)
  have hzero := hfix (↑(0 : K))
  rw [OnePoint.smul_some_eq_ite] at hzero
  have h11 : g 1 1 ≠ 0 := by
    intro h
    simp [h10, h, coe_GL_coe_matrix] at hzero
  have h01 : g 0 1 = 0 := by
    simpa [h10, h11, coe_GL_coe_matrix] using hzero
  have hone := hfix (↑(1 : K))
  rw [OnePoint.smul_some_eq_ite] at hone
  have hdiag : g 0 0 = g 1 1 := by
    simp [h10, h01, h11, coe_GL_coe_matrix] at hone
    exact (div_eq_one_iff_eq h11).mp hone
  apply mem_center_iff.mpr
  refine ⟨g 1 1, ?_, ?_⟩
  · simpa only [Fintype.card_fin, det_fin_two, h10, hdiag, mul_zero, sub_zero, pow_two]
      using g.property
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h10, h01, hdiag]

/-- A determinant-one matrix acts trivially exactly when it is central. -/
public theorem ker_sl2PermHom :
    (sl2PermHom K).ker = Subgroup.center SL(2, K) := by
  classical
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply scalar_of_fixes K g
    intro x
    exact congrArg (fun f : Equiv.Perm (Option K) => f x) hg
  · intro hg
    obtain ⟨a, ha, hga⟩ := mem_center_iff.mp hg
    have ha0 : a ≠ 0 := by
      intro h
      simp [h] at ha
    apply _root_.Equiv.ext
    intro x
    cases x with
    | none =>
      change toGL g • (OnePoint.infty : OnePoint K) = OnePoint.infty
      rw [OnePoint.smul_infty_eq_self_iff]
      change g.1 1 0 = 0
      rw [← hga]
      simp
    | some x =>
      change toGL g • (x : OnePoint K) = (x : OnePoint K)
      rw [OnePoint.smul_some_eq_ite]
      simp only [coe_GL_coe_matrix, ← hga]
      simp [Matrix.scalar_apply, ha0]

private theorem upper_action (b : K) :
    sl2PermHom K (transvection (i := 0) (j := 1) zero_ne_one b) =
      translation K b := by
  classical
  apply _root_.Equiv.ext
  intro x
  cases x with
  | none =>
    change toGL (transvection zero_ne_one b : SL(2, K)) • (OnePoint.infty : OnePoint K) =
      OnePoint.infty
    rw [OnePoint.smul_infty_eq_self_iff]
    simp [toGL, transvection_coe]
  | some x =>
    change toGL (transvection zero_ne_one b : SL(2, K)) • (x : OnePoint K) =
      ((b + x : K) : OnePoint K)
    rw [OnePoint.smul_some_eq_ite]
    simp [toGL, transvection_coe, add_comm]

variable [CharP K 2]

private def swapMatrix : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem swap_action : sl2PermHom K (swapMatrix K) = reciprocal K := by
  classical
  apply _root_.Equiv.ext
  intro x
  cases x with
  | none =>
    change toGL (swapMatrix K) • (OnePoint.infty : OnePoint K) = (0 : K)
    rw [OnePoint.smul_infty_eq_ite]
    simp [toGL, swapMatrix]
  | some x =>
    change toGL (swapMatrix K) • (x : OnePoint K) = _
    rw [OnePoint.smul_some_eq_ite]
    by_cases hx : x = 0
    · simp [toGL, swapMatrix, hx, OnePoint.infty]
      rfl
    · simp [toGL, swapMatrix, hx, reciprocal_some, OnePoint.some]
      rfl

private theorem lower_eq_swap_upper_swap (b : K) :
    transvection (i := 1) (j := 0) one_ne_zero b =
      swapMatrix K * transvection zero_ne_one b * swapMatrix K := by
  apply Subtype.ext
  change Matrix.transvection (1 : Fin 2) 0 b =
    !![0, 1; 1, 0] * Matrix.transvection 0 1 b * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Translations and reciprocal generate precisely the projective SL₂ image. -/
public theorem range_sl2PermHom : (sl2PermHom K).range = projectiveGroup K := by
  have ht (b : K) : translation K b ∈ projectiveGroup K :=
    Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)
  have hw : reciprocal K ∈ projectiveGroup K :=
    Subgroup.subset_closure (Or.inr rfl)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine Matrix.SL2.transvection_induction
      (fun g => sl2PermHom K g ∈ projectiveGroup K) ?_ ?_ g
    · intro i j hij b
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [upper_action]
        exact ht b
      · rw [lower_eq_swap_upper_swap, map_mul, map_mul, swap_action, upper_action]
        exact (projectiveGroup K).mul_mem ((projectiveGroup K).mul_mem hw (ht b)) hw
      · exact (hij rfl).elim
    · intro A B hA hB
      rw [map_mul]
      exact (projectiveGroup K).mul_mem hA hB
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases hf with ⟨b, rfl⟩ | hf
    · exact ⟨transvection zero_ne_one b, upper_action K b⟩
    · obtain rfl := Set.mem_singleton_iff.mp hf
      exact ⟨swapMatrix K, swap_action K⟩

/-- The generated permutation group is the literal quotient SL₂/Z(SL₂). -/
public noncomputable def projectiveGroupEquivPSL : projectiveGroup K ≃* PSL(2, K) :=
  (MulEquiv.subgroupCongr (range_sl2PermHom K)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (sl2PermHom K)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_sl2PermHom K)))

/-- The inverse comparison is the projective action on matrix representatives. -/
public theorem projectiveGroupEquivPSL_symm_apply (g : SL(2, K)) :
    ((projectiveGroupEquivPSL K).symm (QuotientGroup.mk g) : Equiv.Perm (Option K)) =
      sl2PermHom K g := by
  rfl

end Representation.QuadraticFourGroup.Burnside.MatrixComparison

namespace Representation.QuadraticFourGroup.Burnside

/-- The concrete permutation-to-matrix comparison over the binary Galois field. -/
public noncomputable def projectiveGroupEquivFactor (n : ℕ) :
    projectiveGroup (GaloisField 2 n) ≃* Factor n :=
  MatrixComparison.projectiveGroupEquivPSL (GaloisField 2 n)

/-- The matrix comparison at the parameter bound used in Burnside recognition. -/
public theorem nonempty_projectiveGroup_equiv_factor (n : ℕ) (_hn : 1 < n) :
    Nonempty (projectiveGroup (GaloisField 2 n) ≃* Factor n) :=
  ⟨projectiveGroupEquivFactor n⟩

end Representation.QuadraticFourGroup.Burnside
