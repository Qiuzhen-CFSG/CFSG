module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneDuality
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.Frames
public import Theory.SpecificGroups.SL2.Affine.Action
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Actual SL₂ orbit representatives for Hermitian hyperplane poles

Nonzero singular poles are determinant-one congruent to the first diagonal
unit. A nonsingular pole is determinant-one congruent to an off-diagonal
matrix of the same determinant. The conjugators are actual SL₂ matrices,
and the trace-polar duality transports their binary hyperplanes.

These are the orbit-normalization inputs for the hyperplane argument in
Aschbacher–Smith 6.1.4, printed p.665. They do not identify an arbitrary
original Sylow action with a selected canonical Sylow action.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]

local instance orbitsFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance orbitsBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- Every nonzero singular pole has the literal first diagonal unit as an
SL₂-conjugate; there is no remaining scalar parameter. -/
theorem singular_pole_normalization (X : Space s) (hX : X ≠ 0)
    (hq : form s X = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
      action s g X = firstDiagonal s := by
  obtain ⟨x,y,hxy⟩ := singular_factorization s X hq
  have hv : (![x,y] : Fin 2 → Field s) ≠ 0 := by
    intro hz
    have hx : x = 0 := congrFun hz 0
    have hy : y = 0 := congrFun hz 1
    apply hX
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hxy,hx,hy]
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq (Field s) ![1,0] ![x,y]
    (by intro h; have := congrFun h 0; simp at this) hv
  have h0 : g.val 0 0 = x := by
    have he := congrFun hg 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he
  have h1 : g.val 1 0 = y := by
    have he := congrFun hg 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he
  have he : action s g (firstDiagonal s) = X := by
    apply Subtype.ext
    rw [action_apply,hxy]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstDiagonal,coordinates_symm_val,adjoint,
        Matrix.mul_apply,Fin.sum_univ_two,h0,h1]
  refine ⟨g⁻¹,?_⟩
  rw [←he]
  exact (action s).inv_self_apply g (firstDiagonal s)

private theorem trace_pair_surjective (z : Field s) (hz : z ≠ 0)
    (a : fixedField s) :
    ∃ u : Field s, u * conjugation s z + conjugation s u * z = a.val := by
  obtain ⟨W,hW⟩ := traceFunctional_surjective s (a / FiniteModel.norm s z)
  have hw : W.val 0 1 + conjugation s (W.val 0 1) =
      a.val / (z * conjugation s z) := by
    have he := congrArg Subtype.val hW
    change W.val 0 1 + W.val 1 0 = _ at he
    rwa [←entry_conjugate s W 1 0] at he
  refine ⟨W.val 0 1 * z,?_⟩
  rw [map_mul]
  calc
    W.val 0 1 * z * conjugation s z +
        (conjugation s (W.val 0 1) * conjugation s z) * z =
        (W.val 0 1 + conjugation s (W.val 0 1)) * (z * conjugation s z) := by ring
    _ = a.val := by
      rw [hw,div_mul_cancel₀ _ (mul_ne_zero hz ((map_ne_zero (conjugation s)).mpr hz))]

private theorem upper_pole_val (u : Field s) (X : Space s) :
    (action s (upper s u) X).val =
      !![X.val 0 0 + (u * conjugation s (X.val 0 1) + conjugation s u * X.val 0 1) +
            u * conjugation s u * X.val 1 1,
          X.val 0 1 + u * X.val 1 1;
         conjugation s (X.val 0 1) + conjugation s u * X.val 1 1, X.val 1 1] := by
  rw [action_apply]
  have hc := entry_conjugate s X 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,transvection_coe,adjoint,Matrix.mul_apply,Fin.sum_univ_two,hc] <;> ring

private theorem lower_pole_val (u : Field s) (X : Space s) :
    (action s (transvection (show (1 : Fin 2) ≠ 0 by decide) u) X).val =
      !![X.val 0 0, X.val 0 1 + conjugation s u * X.val 0 0;
         conjugation s (X.val 0 1) + u * X.val 0 0,
         X.val 1 1 + (u * X.val 0 1 + conjugation s u * conjugation s (X.val 0 1)) +
           u * conjugation s u * X.val 0 0] := by
  rw [action_apply]
  have hc := entry_conjugate s X 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection_coe,adjoint,Matrix.mul_apply,Fin.sum_univ_two,hc] <;> ring

private theorem normalize_zero_bottom (X : Space s) (hq : form s X ≠ 0)
    (hb : X.val 1 1 = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
      action s g X = offDiagonal s (X.val 0 1) := by
  have hz : X.val 0 1 ≠ 0 := by
    intro hz
    apply hq
    apply Subtype.ext
    change X.val.det = 0
    simp [Matrix.det_fin_two,hb,hz]
  obtain ⟨u,hu⟩ := trace_pair_surjective s (X.val 0 1) hz
    ⟨X.val 0 0,entry_fixed s X 0⟩
  refine ⟨upper s u,?_⟩
  apply Subtype.ext
  rw [upper_pole_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal,coordinates_symm_val,hb,hu,CharTwo.add_self_eq_zero]

private theorem normalize_zero_top (X : Space s) (hq : form s X ≠ 0)
    (ha : X.val 0 0 = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
      action s g X = offDiagonal s (X.val 0 1) := by
  have hz : X.val 0 1 ≠ 0 := by
    intro hz
    apply hq
    apply Subtype.ext
    change X.val.det = 0
    simp [Matrix.det_fin_two,ha,hz]
  obtain ⟨u,hu⟩ := trace_pair_surjective s (conjugation s (X.val 0 1))
    ((map_ne_zero (conjugation s)).mpr hz) ⟨X.val 1 1,entry_fixed s X 1⟩
  rw [conjugation_involutive] at hu
  refine ⟨transvection (show (1 : Fin 2) ≠ 0 by decide) u,?_⟩
  apply Subtype.ext
  rw [lower_pole_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal,coordinates_symm_val,ha,hu,CharTwo.add_self_eq_zero]

private theorem nonsingular_offDiagonal_conjugate (X : Space s) (hq : form s X ≠ 0) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (z : Field s),
      action s g X = offDiagonal s z := by
  by_cases hb : X.val 1 1 = 0
  · obtain ⟨g,hg⟩ := normalize_zero_bottom s X hq hb
    exact ⟨g,X.val 0 1,hg⟩
  · have hs : Function.Surjective (fun t : fixedField s => t ^ 2) :=
      Finite.surjective_of_injective (fun a b h => CharTwo.sq_injective h)
    obtain ⟨t,ht⟩ := hs (form s X)
    have ht' : t.val * t.val = (form s X).val := by
      simpa only [pow_two,Subfield.coe_mul] using congrArg Subtype.val ht
    have htc : conjugation s t.val = t.val := t.property
    let u : Field s := (t.val + X.val 0 1) / X.val 1 1
    let Y := action s (upper s u) X
    have hYb : Y.val 1 1 = X.val 1 1 := by
      dsimp only [Y]
      rw [upper_pole_val]
      rfl
    have hYz : Y.val 0 1 = t.val := by
      dsimp only [Y]
      rw [upper_pole_val]
      change X.val 0 1 + u * X.val 1 1 = t.val
      simp [u,div_mul_cancel₀ _ hb,add_left_comm,CharTwo.add_self_eq_zero]
    have hYa : Y.val 0 0 = 0 := by
      have he := congrArg Subtype.val (form_preserved s (upper s u) X)
      change Y.val.det = (form s X).val at he
      rw [Matrix.det_fin_two,hYb,←entry_conjugate s Y 1 0,hYz,htc,←ht'] at he
      have hz : Y.val 0 0 * X.val 1 1 = 0 := by
        simpa only [CharTwo.add_self_eq_zero] using sub_eq_iff_eq_add.mp he
      exact (mul_eq_zero.mp hz).resolve_right hb
    have hYq : form s Y ≠ 0 := by
      change form s (action s (upper s u) X) ≠ 0
      rwa [form_preserved]
    obtain ⟨g,hg⟩ := normalize_zero_top s Y hYq hYa
    refine ⟨g * upper s u,t.val,?_⟩
    rw [map_mul,Module.End.mul_apply]
    exact hg.trans (congrArg (offDiagonal s) hYz)

/-- Every nonsingular pole has a literal off-diagonal SL₂-conjugate. Its
parameter is nonzero and its norm is exactly the original determinant. -/
theorem nonsingular_pole_normalization (X : Space s) (hq : form s X ≠ 0) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (z : Field s),
      z ≠ 0 ∧ action s g X = offDiagonal s z ∧ FiniteModel.norm s z = form s X := by
  obtain ⟨g,z,hg⟩ := nonsingular_offDiagonal_conjugate s X hq
  have hN : FiniteModel.norm s z = form s X := by
    have he := form_preserved s g X
    rw [hg] at he
    change form s ((coordinates s).symm ((0,0),z)) = form s X at he
    rw [form_coordinates] at he
    simpa only [zero_mul,zero_sub,CharTwo.neg_eq] using he
  have hz : z ≠ 0 := by
    intro hz
    apply hq
    rw [←hN,hz]
    exact (norm_eq_zero_iff s 0).mpr rfl
  exact ⟨g,z,hz,hg,hN⟩

/-- The actual binary hyperplane with singular pole moves to the trace
hyperplane of the first diagonal unit by the same SL₂ conjugator. -/
theorem singular_traceHyperplane_normalization (X : Space s) (hX : X ≠ 0)
    (hq : form s X = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
      action s g X = firstDiagonal s ∧
      (traceHyperplane s X).map (Representation.SL2.BinarySmall.hermitian s g) =
        traceHyperplane s (firstDiagonal s) := by
  obtain ⟨g,hg⟩ := singular_pole_normalization s X hX hq
  exact ⟨g,hg,by rw [traceHyperplane_map,hg]⟩

/-- Nonsingular pole normalization and binary hyperplane normalization use
one actual determinant-one congruence, preserving the norm parameter. -/
theorem nonsingular_traceHyperplane_normalization (X : Space s) (hq : form s X ≠ 0) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (z : Field s),
      z ≠ 0 ∧ action s g X = offDiagonal s z ∧ FiniteModel.norm s z = form s X ∧
      (traceHyperplane s X).map (Representation.SL2.BinarySmall.hermitian s g) =
        traceHyperplane s (offDiagonal s z) := by
  obtain ⟨g,z,hz,hg,hN⟩ := nonsingular_pole_normalization s X hq
  exact ⟨g,z,hz,hg,hN,by rw [traceHyperplane_map,hg]⟩

/-- Every actual binary hyperplane has a canonical singular or nonsingular
representative under the literal SL₂ Hermitian action. -/
theorem hyperplane_orbit_normalization
    (U : Submodule (ZMod 2) (Space s))
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) (Space s)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
      U.map (Representation.SL2.BinarySmall.hermitian s g) =
        traceHyperplane s (firstDiagonal s) ∨
      ∃ z : Field s, z ≠ 0 ∧
        U.map (Representation.SL2.BinarySmall.hermitian s g) =
          traceHyperplane s (offDiagonal s z) := by
  obtain ⟨X,⟨hX,rfl⟩,_⟩ := existsUnique_traceHyperplane s U hU
  by_cases hq : form s X = 0
  · obtain ⟨g,_,hg⟩ := singular_traceHyperplane_normalization s X hX hq
    exact ⟨g,Or.inl hg⟩
  · obtain ⟨g,z,hz,_,_,hg⟩ := nonsingular_traceHyperplane_normalization s X hq
    exact ⟨g,Or.inr ⟨z,hz,hg⟩⟩

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
