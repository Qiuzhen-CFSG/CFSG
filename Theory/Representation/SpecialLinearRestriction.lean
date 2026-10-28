module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.IsPerfect

/-!
# Realizing determinant-one representations as natural restrictions

Coordinates on a faithful finite-dimensional representation give an injective
homomorphism into the special linear group whenever every determinant is one.
The coordinate equivalence intertwines the original operators with the actual
matrix natural action. Perfect groups automatically satisfy the determinant
condition.

This supplies the final representation step in Aschbacher--Smith C.1.22,
printed p.129, for both exceptional block types.
-/

public section
namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- A perfect group's linear representations have determinant one. -/
theorem det_eq_one_of_perfect [Group.IsPerfect G] (ρ : Representation k G V) (g : G) :
    LinearMap.det (ρ g) = 1 := by
  let f : G →* kˣ := MonoidHom.toHomUnits (LinearMap.det.comp ρ)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : f.range => (x.val : k)) h

/-- Matrix coordinates exhibit an actual natural-module restriction. -/
theorem exists_specialLinear_restriction (ρ : Representation k G V)
    (hf : Function.Injective ρ) (hd : ∀ g, LinearMap.det (ρ g) = 1)
    {d : ℕ} (hn : Module.finrank k V = d) :
    ∃ (f : G →* Matrix.SpecialLinearGroup (Fin d) k)
      (e : V ≃ₗ[k] (Fin d → k)),
      Function.Injective f ∧ ∀ g v, e (ρ g v) = specialLinearNatural d (f g) (e v) := by
  classical
  let b := Module.finBasisOfFinrankEq k V hn
  let f : G →* Matrix.SpecialLinearGroup (Fin d) k := {
    toFun g := ⟨LinearMap.toMatrix b b (ρ g), by rw [LinearMap.det_toMatrix, hd]⟩
    map_one' := by apply Subtype.ext; simp only [map_one, LinearMap.toMatrix_one]; rfl
    map_mul' g h := by
      apply Subtype.ext
      simp only [map_mul, LinearMap.toMatrix_mul]
      rfl }
  refine ⟨f, b.equivFun, ?_, ?_⟩
  · intro g h he
    apply hf
    exact (LinearMap.toMatrix b b).injective (congrArg Subtype.val he)
  · intro g v
    exact (LinearMap.toMatrix_mulVec_repr b b (ρ g) v).symm
end Representation
