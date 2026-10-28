module

public import Theory.SpecificGroups.HigherLinear.ParabolicGeometry
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Change of basis for special-linear parabolics

An isomorphism between equal-dimensional subspaces extends to their ambient
vector space. Conjugation by this linear equivalence preserves determinant
one and identifies the actual subspace stabilizers. The natural-action
formula records the direction of transport explicitly.

Source: elementary change of basis for the type-A parabolics in
Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7(3)(g), p.145.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.HigherLinear.SubspaceTransport
variable {F : Type*} [Field F] {n : ℕ}

/-- Membership uses the literal matrix action on vectors. -/
theorem mem_parabolicSL_iff (W : Submodule F (Fin n → F)) (g : SL(n,F)) :
    g ∈ parabolicSL W ↔ ∀ x, Matrix.SpecialLinearGroup.toLin' g x ∈ W ↔ x ∈ W := Iff.rfl

/-- A change of basis conjugates determinant-one matrices. -/
def slConj (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) : SL(n,F) ≃* SL(n,F) :=
  (Matrix.SpecialLinearGroup.toLin'_equiv.trans
    (_root_.SpecialLinearGroup.congr_linearEquiv e)).trans
      Matrix.SpecialLinearGroup.toLin'_equiv.symm

/-- Conjugation is compatible with the natural matrix action. -/
theorem slConj_apply (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (g : SL(n,F)) (x : Fin n → F) :
    Matrix.SpecialLinearGroup.toLin' (slConj e g) x =
      e (Matrix.SpecialLinearGroup.toLin' g (e.symm x)) := by
  have hh : Matrix.SpecialLinearGroup.toLin'_equiv (slConj e g) =
      _root_.SpecialLinearGroup.congr_linearEquiv e
        (Matrix.SpecialLinearGroup.toLin'_equiv g) := by simp [slConj]
  exact congrArg (fun z : _root_.SpecialLinearGroup F (Fin n → F) => z x) hh

/-- A marked change of basis transports the full subspace stabilizer. -/
theorem conj_mem (W S : Submodule F (Fin n → F))
    (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (he : ∀ x, e x ∈ S ↔ x ∈ W) (g : SL(n,F)) :
    slConj e g ∈ parabolicSL S ↔ g ∈ parabolicSL W := by
  rw [mem_parabolicSL_iff, mem_parabolicSL_iff]
  constructor
  · intro h x
    have hx := h (e x)
    simpa only [slConj_apply, LinearEquiv.symm_apply_apply, he] using hx
  · intro h x
    rw [slConj_apply, he, h]
    simpa only [LinearEquiv.apply_symm_apply] using (he (e.symm x)).symm

/-- Restrict the change-of-basis automorphism to the actual parabolics. -/
def stabilizerEquiv (W S : Submodule F (Fin n → F))
    (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (he : ∀ x, e x ∈ S ↔ x ∈ W) :
    parabolicSL W ≃* parabolicSL S :=
  ((slConj e).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    ext g
    obtain ⟨g, rfl⟩ := (slConj e).surjective g
    change (slConj e) g ∈ (parabolicSL W).map (slConj e).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, conj_mem W S e he]))

/-- Equal-dimensional subspaces have isomorphic full special-linear stabilizers. -/
theorem exists_stabilizerEquiv (W S : Submodule F (Fin n → F))
    (hd : Module.finrank F W = Module.finrank F S) :
    Nonempty (parabolicSL W ≃* parabolicSL S) := by
  let f := LinearEquiv.ofFinrankEq W S hd
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨stabilizerEquiv W S e ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := f.surjective ⟨e x, hx⟩
    have hey : e (y : Fin n → F) = e x := (he y).symm.trans (congrArg Subtype.val hy)
    exact e.injective hey ▸ y.property
  · intro hx
    rw [← he ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).property

end Matrix.HigherLinear.SubspaceTransport

end
