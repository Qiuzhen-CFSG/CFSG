module
public import Theory.Representation.Isotypic
public import Mathlib.RepresentationTheory.Irreducible
/-!
# Finite coordinates on the canonical isotypic component

A simple type's isotypic component is semisimple even when the surrounding
module is not. The finite-dimensional component therefore has actual finite
copy coordinates, respecting the original group action. This supplies the
Schur multiplicity calculation on the original Suzuki Steinberg component.

Source: Isaacs 1.12–1.13 and Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
open scoped MonoidAlgebra
open Representation Module
namespace Representation.SchurCopies
variable {k D V E : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup E] [Module k E]

/-- Actual finite coordinates on the canonical isotypic component. The
ambient representation need not be semisimple. -/
theorem isotypic_finite_coordinates
    (ρ : Representation k D V) (σ : Representation k D E) [IsIrreducible σ] :
    ∃ n : ℕ, Nonempty
      (isotypicComponent k[D] ρ.asModule σ.asModule ≃ₗ[k[D]] (Fin n → σ.asModule)) := by
  let : Module.Finite k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  let : Module.Finite k (isotypicComponent k[D] ρ.asModule σ.asModule) :=
    FiniteDimensional.of_injective
      ((isotypicComponent k[D] ρ.asModule σ.asModule).subtype.restrictScalars k)
      Subtype.val_injective
  let : Module.Finite k[D] (isotypicComponent k[D] ρ.asModule σ.asModule) :=
    Module.Finite.of_restrictScalars_finite k k[D] _
  exact (IsIsotypicOfType.isotypicComponent k[D] ρ.asModule σ.asModule).linearEquiv_fun
end Representation.SchurCopies

namespace Representation.SchurCopies
variable {k D V E : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup E] [Module k E]

/-- The canonical isotypic coordinates intertwine the literal component action. -/
theorem isotypic_finite_rep_coordinates
    (ρ : Representation k D V) (σ : Representation k D E) [IsIrreducible σ] :
    ∃ n : ℕ, ∃ e : (Subrepresentation.ofSubmodule'
      (isotypicComponent k[D] ρ.asModule σ.asModule)).toSubmodule ≃ₗ[k] (Fin n → E),
      ∀ d v, e ((Subrepresentation.ofSubmodule'
        (isotypicComponent k[D] ρ.asModule σ.asModule)).toRepresentation d v) =
        fun i => σ d (e v i) := by
  obtain ⟨n,⟨e⟩⟩ := isotypic_finite_coordinates ρ σ
  let q : (isotypicComponent k[D] ρ.asModule σ.asModule) ≃ₗ[k] (Fin n → E) :=
    (e.restrictScalars k).trans (LinearEquiv.piCongrRight fun _ => σ.asModuleEquiv)
  refine ⟨n, q, ?_⟩
  intro d v
  let w : isotypicComponent k[D] ρ.asModule σ.asModule := ⟨v.val, v.property⟩
  have h := e.map_smul (MonoidAlgebra.single d (1 : k)) w
  have hv : MonoidAlgebra.single d (1 : k) • w =
      (Subrepresentation.ofSubmodule' (isotypicComponent k[D] ρ.asModule σ.asModule)).toRepresentation d v := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Representation.single_smul, one_smul]
    rfl
  rw [hv] at h
  funext i
  have hi := congrArg σ.asModuleEquiv (congrFun h i)
  change σ.asModuleEquiv (e _ i) = σ d (σ.asModuleEquiv (e w i))
  simpa only [Pi.smul_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul] using hi
end Representation.SchurCopies
