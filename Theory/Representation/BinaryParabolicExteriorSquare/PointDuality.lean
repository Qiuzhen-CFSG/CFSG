module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneSpan
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Duality across the exterior point three-space

The polar form of the six-coordinate Pfaffian is nondegenerate and alternating.
Its first three-space is its own orthogonal complement. The determinant identity
for the exterior action proves invariance under the original SL₄ matrix, so the
quotient by this three-space is its contragredient dual, with the original action.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, 13.8.29(4),
printed p.964. The exterior model retains the imported ATLAS attribution.
-/

public noncomputable section
open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PointDuality
open PlaneSpan

@[expose] def form : LinearMap.BilinForm Bit Six := (pfaffian : QuadraticForm Bit Six).polarBilin

theorem form_apply (x y : Six) : form x y =
    x 0 * y 5 + x 5 * y 0 + x 1 * y 4 + x 4 * y 1 + x 2 * y 3 + x 3 * y 2 := by
  simp only [form, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    pfaffian_apply, Pi.add_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring_nf
  simp [show (2 : Bit) = 0 from by decide]

theorem form_alt : form.IsAlt := by
  intro x
  rw [form_apply]
  have htwo : (2 : Bit) = 0 := by decide
  ring_nf
  simp [htwo]

theorem form_nondegenerate : form.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  have h (i : Fin 6) := congrArg (fun f : Module.Dual Bit Six => f (Pi.single i 1)) hx
  ext i
  fin_cases i
  all_goals first
  | simpa [form_apply] using h 5
  | simpa [form_apply] using h 4
  | simpa [form_apply] using h 3
  | simpa [form_apply] using h 2
  | simpa [form_apply] using h 1
  | simpa [form_apply] using h 0

theorem firstSpace_orthogonal : form.orthogonal firstSpace = firstSpace := by
  ext x
  constructor
  · intro hx
    have h0 := hx (Pi.single 0 1) (by change _ ∧ _ ∧ _; simp)
    have h1 := hx (Pi.single 1 1) (by change _ ∧ _ ∧ _; simp)
    have h2 := hx (Pi.single 2 1) (by change _ ∧ _ ∧ _; simp)
    exact ⟨by simpa [form_apply] using h2, by simpa [form_apply] using h1,
      by simpa [form_apply] using h0⟩
  · intro hx y hy
    rcases hx with ⟨h3,h4,h5⟩
    rcases hy with ⟨k3,k4,k5⟩
    simp [form_apply,h3,h4,h5,k3,k4,k5]

theorem form_invariant (A : Matrix (Fin 4) (Fin 4) Bit) (hA : A.det = 1)
    (x y : Six) : form (exteriorMap A x) (exteriorMap A y) = form x y := by
  simp only [form, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ←map_add, pfaffian_exteriorMap, hA, one_mul]

end Representation.BinaryParabolicExteriorSquare.PointDuality
