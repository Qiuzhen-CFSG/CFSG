module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Field coordinates for a binary quadratic operator

An operator θ satisfying θ² = 1 + θ defines a module over the concrete
field F₄ = F₂[ω]. A basis over that field gives binary linear coordinates
in which θ acts as multiplication by ω. The paired coordinate equivalence
will identify complementary root spaces with copies of the natural plane.

Source application: Aschbacher–Smith, G.1.3 and G.1.7, printed pp.327–329.
-/

@[expose] public noncomputable section
namespace Representation.SL2FourNatural.ProjectiveRecognition
universe u
variable {A : Type u} [AddCommGroup A] [Module (ZMod 2) A]

theorem quadratic_coordinates [Finite A] (θ : Module.End (ZMod 2) A) (hθ : θ*θ=1+θ) :
    ∃ (s : ℕ) (e : A ≃ₗ[ZMod 2] (Fin s → F)),
      ∀ x i, e (θ x) i = QuadraticAlgebra.omega * e x i := by
  let f : F →ₐ[ZMod 2] Module.End (ZMod 2) A :=
    QuadraticAlgebra.lift ⟨θ, by simpa using hθ⟩
  let : Module F A := Module.compHom A f.toRingHom
  let e := (Module.finBasis F A).equivFun
  refine ⟨Module.finrank F A, e.restrictScalars (ZMod 2), ?_⟩
  intro x i
  have he := congrFun (e.map_smul (QuadraticAlgebra.omega : F) x) i
  have ho : (QuadraticAlgebra.omega : F) • x = θ x := by
    change (f QuadraticAlgebra.omega) x = θ x
    simp [f, QuadraticAlgebra.lift]
  simpa only [ho, Pi.smul_apply, smul_eq_mul, LinearEquiv.restrictScalars_apply] using he

noncomputable def pairPiCoordinates {s : ℕ} (e : A ≃ₗ[ZMod 2] (Fin s → F)) :
    (A × A) ≃ₗ[ZMod 2] (Fin s → Fin 2 → F) where
  toFun x i := ![e x.1 i, e x.2 i]
  invFun x := (e.symm (fun i => x i 0), e.symm (fun i => x i 1))
  left_inv x := by simp
  right_inv x := by
    funext i j
    fin_cases j <;> simp
  map_add' x y := by
    funext i j
    fin_cases j <;> simp
  map_smul' a x := by
    funext i j
    fin_cases j <;> simp

theorem pairPiCoordinates_apply {s : ℕ} (e : A ≃ₗ[ZMod 2] (Fin s → F))
    (x : A × A) (i : Fin s) : pairPiCoordinates e x i = ![e x.1 i,e x.2 i] := rfl

end Representation.SL2FourNatural.ProjectiveRecognition
