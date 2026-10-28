module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.QuadraticNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates
import Mathlib.Tactic.FinCases

/-!
# Quadratic coordinates for the explicit symplectic normalizer

The coordinates `(x₀ + x₁ω, y₀ - y₁ω)` identify the ternary symplectic
module with two copies of the nine-element field. The operator defining the
normalizer becomes multiplication by `ω`. Consequently each normalizer element
preserves field lines. Quadratic conjugation is realized by an explicit
symplectic involution, which exchanges the commuting and anticommuting cases.

This uses the field model of `NineCoordinates`, adapted there from Gerald Höhn
and the ATLAS contributors (revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
ATLAS Research and Attribution License 1.0, `LICENSES/ATLAS.txt`). The coordinate
comparison proved here is for the actual matrix carrier of `QuadraticNormalizer`.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4/482 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix
namespace Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
open Atlas.Comparisons.Exceptional
abbrev W := Fin 2 → Nine.F

noncomputable def coordinates : V ≃ₗ[ZMod 3] W where
  toFun x := ![⟨x (.inl 0), x (.inl 1)⟩, ⟨x (.inr 0), -x (.inr 1)⟩]
  invFun w := Sum.elim ![(w 0).re, (w 0).im] ![(w 1).re, -(w 1).im]
  left_inv x := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  right_inv w := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> apply QuadraticAlgebra.ext <;> simp [add_comm]
  map_smul' a x := by
    funext i
    fin_cases i <;> apply QuadraticAlgebra.ext <;> simp

theorem coordinates_quadraticOperator (x : V) :
    coordinates (quadraticOperator x) = Nine.omega • coordinates x := by
  have htwo : (2 : ZMod 3) = -1 := by decide
  funext i
  fin_cases i <;> apply QuadraticAlgebra.ext <;>
    simp [coordinates, quadraticOperator, Nine.omega, QuadraticAlgebra.omega,
      smul_eq_mul, htwo]

theorem scalar_decomposition (a : Nine.F) (w : W) :
    a • w = a.re • w + a.im • (Nine.omega • w) := by
  funext i
  apply QuadraticAlgebra.ext <;>
    simp [Nine.omega, QuadraticAlgebra.omega, smul_eq_mul]
  all_goals ring

noncomputable def transport (g : Sp 2 (ZMod 3)) : W ≃ₗ[ZMod 3] W :=
  coordinates.symm.trans ((toLinear g).trans coordinates)

@[simp] theorem transport_apply (g : Sp 2 (ZMod 3)) (w : W) :
    transport g w = coordinates (g • coordinates.symm w) := rfl

@[simp] theorem transport_one (w : W) : transport 1 w = w := by
  simp

@[simp] theorem transport_mul (g h : Sp 2 (ZMod 3)) (w : W) :
    transport (g * h) w = transport g (transport h w) := by
  simp [mul_smul]

theorem transport_omega (g : quadraticNormalizer) :
    ∃ c : ZMod 3, c * c = 1 ∧ ∀ w : W,
      transport g.val (Nine.omega • w) = c • (Nine.omega • transport g.val w) := by
  obtain ⟨c, hc, hg⟩ := g.property
  refine ⟨c, hc, fun w => ?_⟩
  have hJ : coordinates.symm (Nine.omega • w) = quadraticOperator (coordinates.symm w) := by
    apply coordinates.injective
    simp [coordinates_quadraticOperator]
  simp only [transport_apply, hJ, hg, map_smul, coordinates_quadraticOperator]

theorem transport_scalar (g : quadraticNormalizer) (a : Nine.F) (w : W) :
    ∃ b : Nine.F, transport g.val (a • w) = b • transport g.val w := by
  obtain ⟨c, _, hc⟩ := transport_omega g
  refine ⟨⟨a.re, a.im * c⟩, ?_⟩
  calc
    _ = a.re • transport g.val w + (a.im * c) • (Nine.omega • transport g.val w) := by
      rw [scalar_decomposition a w, map_add, map_smul, map_smul, hc, smul_smul]
    _ = _ := (scalar_decomposition ⟨a.re, a.im * c⟩ (transport g.val w)).symm


theorem coordinates_form (x y : V) :
    form x y = (coordinates x 0 * coordinates y 1 - coordinates x 1 * coordinates y 0).re := by
  have htwo : (2 : ZMod 3) = -1 := by decide
  simp [coordinates, form_apply, Fin.sum_univ_two, htwo]

/-- Quadratic conjugation on both coordinates is a genuine symplectic matrix. -/
def conjugationMatrix : Sp 2 (ZMod 3) :=
  ⟨Matrix.diagonal (Sum.elim ![1, -1] ![1, -1]), by
    rw [mem_iff_preserves]
    intro x y
    simp [form_apply, Fin.sum_univ_two, Matrix.mulVec_diagonal]⟩

@[simp] theorem conjugationMatrix_apply (x : V) :
    conjugationMatrix • x = Sum.elim ![x (.inl 0), -x (.inl 1)]
      ![x (.inr 0), -x (.inr 1)] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [conjugationMatrix, Matrix.mulVec_diagonal]

theorem conjugationMatrix_anticommutes (x : V) :
    conjugationMatrix • quadraticOperator x = -quadraticOperator (conjugationMatrix • x) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [conjugationMatrix_apply, quadraticOperator]

def conjugationElement : quadraticNormalizer :=
  ⟨conjugationMatrix, (mem_quadraticNormalizer_iff _).mpr (Or.inr conjugationMatrix_anticommutes)⟩

@[simp] theorem transport_conjugation (w : W) :
    transport conjugationMatrix w = fun i => star (w i) := by
  funext i
  fin_cases i <;> apply QuadraticAlgebra.ext <;>
    simp [transport_apply, coordinates, conjugationMatrix_apply]

theorem conjugationElement_sq : conjugationElement * conjugationElement = 1 := by
  apply Subtype.ext
  apply ext_action
  intro x
  simp only [Subgroup.coe_mul, Subgroup.coe_one, conjugationElement, mul_smul, one_smul,
    conjugationMatrix_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp

theorem anticommutes_mul_conjugation_commutes (g : Sp 2 (ZMod 3))
    (hg : ∀ x : V, g • quadraticOperator x = -quadraticOperator (g • x)) (x : V) :
    (g * conjugationMatrix) • quadraticOperator x =
      quadraticOperator ((g * conjugationMatrix) • x) := by
  simp only [mul_smul, conjugationMatrix_anticommutes]
  change (toLinear g) (-quadraticOperator (conjugationMatrix • x)) = _
  rw [map_neg]
  change -(g • quadraticOperator (conjugationMatrix • x)) = _
  rw [hg, neg_neg]

end Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
