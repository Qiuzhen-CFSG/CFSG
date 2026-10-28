module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.Basic
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Root displacements and the outer involution of the Hermitian SL₂ action

For the quadratic field over K of order 2^s, the upper-root double displacement
is the trace pairing of its two parameters times the bottom diagonal entry.
Triple displacements vanish, and quadratic root actors are precisely those
contained in a K-line. Transpose is the transvection whose moved vector is the
off-diagonal unit matrix, of determinant one. Its centralizer in the actual
SL₂ action consists exactly of matrices over K, yielding a group equivalence
with SL₂(K), including s=1.

The matrix formulas also occur locally in `OrthogonalFourMinusBinaryIrreducibility`.
Here they are exposed for the actor calculations, with the exact existing
Hermitian representation and orthogonal isometry conventions.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1.2,
printed p.454; the ratio conventions are D.2.1, printed p.178.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.BinaryOffender
open Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

abbrev upper (u : Field s) : Matrix.SpecialLinearGroup (Fin 2) (Field s) :=
  Matrix.SpecialLinearGroup.transvection zero_ne_one u

def rootDifference (u : Field s) : Space s →ₗ[fixedField s] Space s :=
  action s (upper s u) - LinearMap.id

theorem rootDifference_val (u : Field s) (X : Space s) :
    (rootDifference s u X).val =
      !![u * X.val 1 0 + conjugation s u * X.val 0 1 +
          u * conjugation s u * X.val 1 1, u * X.val 1 1;
        conjugation s u * X.val 1 1, 0] := by
  change (action s (upper s u) X).val - X.val = _
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.SpecialLinearGroup.transvection_coe, adjoint,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem double_rootDifference_val (u v : Field s) (X : Space s) :
    (rootDifference s u (rootDifference s v X)).val =
      !![(u * conjugation s v + conjugation s u * v) * X.val 1 1, 0; 0, 0] := by
  rw [rootDifference_val, rootDifference_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_mul, mul_assoc]

theorem triple_rootDifference (u v w : Field s) (X : Space s) :
    rootDifference s u (rootDifference s v (rootDifference s w X)) = 0 := by
  apply Subtype.ext
  rw [rootDifference_val, double_rootDifference_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem double_rootDifference_eq_zero_iff (u v : Field s) :
    (∀ X, rootDifference s u (rootDifference s v X) = 0) ↔
      u * conjugation s v + conjugation s u * v = 0 := by
  constructor
  · intro h
    have he := congrArg (fun X : Space s => X.val 0 0) (h (secondDiagonal s))
    simpa [double_rootDifference_val, secondDiagonal, coordinates_symm_val] using he
  · intro h X
    apply Subtype.ext
    rw [double_rootDifference_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

omit [NeZero s] in
theorem pair_vanishes_iff_ratio_fixed {u v : Field s} (hu : u ≠ 0) :
    u * conjugation s v + conjugation s u * v = 0 ↔
      conjugation s (v / u) = v / u := by
  rw [map_div₀, div_eq_div_iff ((map_ne_zero (conjugation s)).mpr hu) hu]
  rw [CharTwo.add_eq_zero]
  exact ⟨fun h => by simpa [mul_comm] using h, fun h => by simpa [mul_comm] using h⟩

/-- The moved vector of the field involution has determinant one. -/
def movedVector : Space s := offDiagonal s 1

theorem movedVector_form : form s (movedVector s) = 1 := by
  change form s ((coordinates s).symm ((0, 0), 1)) = 1
  rw [form_coordinates]
  apply Subtype.ext
  simp [FiniteModel.norm, CharTwo.neg_eq]

def traceFunctional : Space s →ₗ[fixedField s] fixedField s where
  toFun X := ⟨X.val 0 1 + X.val 1 0, by
    change conjugation s (X.val 0 1 + X.val 1 0) = X.val 0 1 + X.val 1 0
    rw [map_add, entry_conjugate s X 1 0, entry_conjugate s X 0 1, add_comm]⟩
  map_add' X Y := by apply Subtype.ext; change _ + _ = _; simp; ring
  map_smul' c X := by
    apply Subtype.ext
    change c.val * X.val 0 1 + c.val * X.val 1 0 = c.val * _
    ring

theorem traceFunctional_movedVector : traceFunctional s (movedVector s) = 0 := by
  apply Subtype.ext
  change (1 : Field s) + conjugation s 1 = 0
  simp [CharTwo.add_self_eq_zero]

theorem conjugationLinear_eq_transvection :
    conjugationLinear s = LinearEquiv.transvection (traceFunctional_movedVector s) := by
  ext X : 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearEquiv.transvection, LinearMap.transvection, conjugationLinear,
      traceFunctional, movedVector, offDiagonal, coordinates_symm_val,
      Subfield.smul_def, smul_eq_mul] <;>
    (abel_nf; simp [CharTwo.two_eq_zero])

theorem traceFunctional_surjective : Function.Surjective (traceFunctional s) := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro hz
  obtain ⟨z, hzne⟩ := exists_conjugation_ne s
  have he := congrArg (fun f : Space s →ₗ[fixedField s] fixedField s =>
    (f (offDiagonal s z)).val) hz
  have he' : z + conjugation s z = 0 := he
  exact hzne (CharTwo.add_eq_zero.mp he').symm

theorem conjugation_displacement (X : Space s) :
    conjugationLinear s X - X = traceFunctional s X • movedVector s := by
  rw [conjugationLinear_eq_transvection]
  change X + traceFunctional s X • movedVector s - X = _
  abel

theorem conjugation_moved_range :
    LinearMap.range ((conjugationLinear s).toLinearMap - LinearMap.id) =
      Submodule.span (fixedField s) {movedVector s} := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    change conjugationLinear s Y - Y ∈ _
    rw [conjugation_displacement]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
    obtain ⟨Y, rfl⟩ := traceFunctional_surjective s c
    exact ⟨Y, conjugation_displacement s Y⟩

theorem movedVector_ne_zero : movedVector s ≠ 0 := by
  intro h
  have he := movedVector_form s
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem conjugation_moved_finrank :
    Module.finrank (fixedField s)
      (LinearMap.range ((conjugationLinear s).toLinearMap - LinearMap.id)) = 1 := by
  rw [conjugation_moved_range]
  exact finrank_span_singleton (movedVector_ne_zero s)

theorem moved_line_nonsingular {X : Space s}
    (hX : X ∈ LinearMap.range ((conjugationLinear s).toLinearMap - LinearMap.id))
    (hne : X ≠ 0) : form s X ≠ 0 := by
  rw [conjugation_moved_range] at hX
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
  have hc : c ≠ 0 := by intro h; exact hne (by rw [h, zero_smul])
  rw [QuadraticMap.map_smul, movedVector_form, smul_eq_mul, mul_one]
  exact mul_ne_zero hc hc


theorem root_subgroup_cubic (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hA : A ≤ upperUnipotent (Field s)) : IsCubic (SL2.BinarySmall.hermitian s) A := by
  intro a ha b hb c hc X
  obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ a).mp (hA ha)
  obtain ⟨v, rfl⟩ := (mem_upperUnipotent _ b).mp (hA hb)
  obtain ⟨w, rfl⟩ := (mem_upperUnipotent _ c).mp (hA hc)
  exact triple_rootDifference s u v w X

theorem root_subgroup_quadratic_iff
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hA : A ≤ upperUnipotent (Field s)) :
    IsQuadratic (SL2.BinarySmall.hermitian s) A ↔
      ∀ u v : Field s, upper s u ∈ A → upper s v ∈ A →
        u * conjugation s v + conjugation s u * v = 0 := by
  constructor
  · intro h u v hu hv
    apply (double_rootDifference_eq_zero_iff s u v).mp
    intro X
    exact sub_eq_zero.mpr (h _ hu _ hv X)
  · intro h a ha b hb X
    obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ a).mp (hA ha)
    obtain ⟨v, rfl⟩ := (mem_upperUnipotent _ b).mp (hA hb)
    exact sub_eq_zero.mp ((double_rootDifference_eq_zero_iff s u v).mpr (h u v ha hb) X)

/-- Quadratic root actors are precisely the subgroups contained in a fixed-field line. -/
theorem root_subgroup_quadratic_iff_fixed_ratios
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hA : A ≤ upperUnipotent (Field s)) {u : Field s} (hu : u ≠ 0)
    (huA : upper s u ∈ A) :
    IsQuadratic (SL2.BinarySmall.hermitian s) A ↔
      ∀ v : Field s, upper s v ∈ A → conjugation s (v / u) = v / u := by
  rw [root_subgroup_quadratic_iff s A hA]
  constructor
  · intro h v hv
    exact (pair_vanishes_iff_ratio_fixed s hu).mp (h u v huA hv)
  · intro h v w hv hw
    have hv' := (pair_vanishes_iff_ratio_fixed s hu).mpr (h v hv)
    have hw' := (pair_vanishes_iff_ratio_fixed s hu).mpr (h w hw)
    have he : u * (v * conjugation s w + conjugation s v * w) = 0 := by
      linear_combination v * hw' + w * hv' -
        (conjugation s u * v) * (CharTwo.add_self_eq_zero w)
    exact (mul_eq_zero.mp he).resolve_left hu

theorem upper_not_quadratic :
    ¬ IsQuadratic (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) := by
  intro h
  obtain ⟨v, hv⟩ := exists_conjugation_ne s
  have he := (root_subgroup_quadratic_iff s _ le_rfl).mp h 1 v
    ((mem_upperUnipotent _ _).mpr ⟨1, rfl⟩) ((mem_upperUnipotent _ _).mpr ⟨v, rfl⟩)
  apply hv
  simpa using CharTwo.add_eq_zero.mp he

/-- A nonidentity root fixes exactly the matrices with bottom entry zero and
orthogonal off-diagonal coordinate, for the trace pairing of the quadratic field. -/
theorem root_fixed_iff {u : Field s} (hu : u ≠ 0) (X : Space s) :
    action s (upper s u) X = X ↔ X.val 1 1 = 0 ∧
      u * conjugation s (X.val 0 1) + conjugation s u * X.val 0 1 = 0 := by
  rw [← sub_eq_zero]
  change rootDifference s u X = 0 ↔ _
  constructor
  · intro h
    have h01 := congrArg (fun Y : Space s => Y.val 0 1) h
    have hb : X.val 1 1 = 0 := by
      have he : u * X.val 1 1 = 0 := by simpa [rootDifference_val] using h01
      exact (mul_eq_zero.mp he).resolve_left hu
    refine ⟨hb, ?_⟩
    have h00 := congrArg (fun Y : Space s => Y.val 0 0) h
    simpa [rootDifference_val, hb, entry_conjugate s X 1 0] using h00
  · rintro ⟨hb, hz⟩
    apply Subtype.ext
    rw [rootDifference_val]
    rw [entry_conjugate s X 1 0] at hz
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hz]


/-- The centralizer in SL₂ of the literal outer orthogonal involution. -/
def involutionCentralizer : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)) :=
  (Subgroup.centralizer {conjugationOrthogonal s}).comap (orthogonalAction s)

theorem mem_involutionCentralizer_iff (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    A ∈ involutionCentralizer s ↔ ∀ i j, conjugation s (A.val i j) = A.val i j := by
  change orthogonalAction s A ∈ Subgroup.centralizer {conjugationOrthogonal s} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff, conjugationOrthogonal_mul_action]
  rw [mul_left_inj, (orthogonalAction_injective s).eq_iff]
  constructor
  · intro h i j
    exact (congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) (Field s) => B.val i j) h).symm
  · intro h
    apply Subtype.ext
    ext i j
    exact (h i j).symm

/-- Entrywise inclusion of matrices over the fixed field. -/
def fixedFieldEmbedding : Matrix.SpecialLinearGroup (Fin 2) (fixedField s) →*
    Matrix.SpecialLinearGroup (Fin 2) (Field s) :=
  Matrix.SpecialLinearGroup.map (fixedField s).subtype

omit [NeZero s] in
theorem fixedFieldEmbedding_injective : Function.Injective (fixedFieldEmbedding s) := by
  intro A B h
  apply Subtype.ext
  ext i j
  exact congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) (Field s) => C.val i j) h

theorem range_fixedFieldEmbedding :
    (fixedFieldEmbedding s).range = involutionCentralizer s := by
  ext A
  rw [mem_involutionCentralizer_iff]
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact (B.val i j).property
  · intro h
    let Bmat : Matrix (Fin 2) (Fin 2) (fixedField s) := fun i j => ⟨A.val i j, h i j⟩
    have hd : Bmat.det = 1 := by
      apply (fixedField s).subtype.injective
      rw [RingHom.map_det, map_one]
      exact A.property
    let B : Matrix.SpecialLinearGroup (Fin 2) (fixedField s) := ⟨Bmat, hd⟩
    exact ⟨B, Subtype.ext rfl⟩

/-- `C_L(t)` is genuinely isomorphic to SL₂ over the fixed field. -/
def fixedFieldEquivCentralizer : Matrix.SpecialLinearGroup (Fin 2) (fixedField s) ≃*
    involutionCentralizer s :=
  (MonoidHom.ofInjective (fixedFieldEmbedding_injective s)).trans
    (MulEquiv.subgroupCongr (range_fixedFieldEmbedding s))

/-- Inside the chosen Sylow root group, the centralizer is exactly the fixed-field roots. -/
theorem mem_root_centralizer_iff (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    A ∈ upperUnipotent (Field s) ⊓ involutionCentralizer s ↔
      ∃ u : fixedField s, upper s u.val = A := by
  constructor
  · rintro ⟨hU, hC⟩
    obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ _).mp hU
    have hu := (mem_involutionCentralizer_iff s _).mp hC 0 1
    have hu' : conjugation s u = u := by simpa [upper, transvection_coe] using hu
    exact ⟨⟨u, hu'⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨(mem_upperUnipotent _ _).mpr ⟨u.val, rfl⟩, ?_⟩
    change upper s u.val ∈ involutionCentralizer s
    rw [mem_involutionCentralizer_iff]
    intro i j
    have hu : conjugation s u.val = u.val := u.property
    fin_cases i <;> fin_cases j <;> simp [upper, transvection_coe, hu]


/-- The distinguished orthogonal element is a genuine involution. -/
theorem conjugationOrthogonal_ne_one : conjugationOrthogonal s ≠ 1 := by
  intro h
  obtain ⟨X, hX⟩ := traceFunctional_surjective s 1
  have he : conjugationLinear s X = X :=
    congrArg (fun g : ClassicalOrthogonal.Minus.Orthogonal (fixedField s) (Space s) (form s) =>
      g.val X) h
  have hd := conjugation_displacement s X
  rw [he, sub_self, hX, one_smul] at hd
  exact movedVector_ne_zero s hd.symm

theorem conjugationLinear_mem_transvections :
    conjugationLinear s ∈ LinearEquiv.transvections (fixedField s) (Space s) := by
  rw [conjugationLinear_eq_transvection]
  exact LinearEquiv.mem_transvections (traceFunctional_movedVector s)


end Representation.OrthogonalFourMinus.RankOne
