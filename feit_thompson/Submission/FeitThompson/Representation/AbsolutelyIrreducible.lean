/-
Authors: Yusen Tang
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RepresentationTheory.Irreducible
public import FeitThompson.Representation.ExtendScalars
public import FeitThompson.Representation.JacobsonDensity
public import FeitThompson.Representation.SubrepresentationLattice

open scoped TensorProduct
open scoped MonoidAlgebra

namespace Representation

section AbsolutelyIrreducibleRep

variable {F G V W : Type*} [Monoid G] [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)

/-- A representation is absolutely irreducible if it remains irreducible after extending scalars
to an algebraic closure of the base field. -/
@[mk_iff]
public class IsAbsolutelyIrreducible: Prop where
  irreducible_of_closure : IsIrreducible (extendScalars (AlgebraicClosure F) ρ)

set_option backward.isDefEq.respectTransparency false in
public theorem isAbsolutelyIrreducible_iff_surjective [FiniteDimensional F V] [IsIrreducible ρ] :
    IsAbsolutelyIrreducible ρ ↔ Function.Surjective (algebraMap F (End ρ)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let : (extendScalars (AlgebraicClosure F) ρ).IsIrreducible :=
      (isAbsolutelyIrreducible_iff ρ).mp h
    have := jacobson_density_surjective_isAlgClosed_rep (extendScalars (AlgebraicClosure F) ρ)
    rw [← extendScalars_surj_iff] at this
    exact surjective_of_jacobson_density_surjective_rep ρ this
  · let : Nontrivial (AlgebraicClosure F ⊗[F] V) := by
      rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]
      exact Subrepresentation.irreducible_module_nontrivial ρ
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    exact jacobson_density_surjective_rep ρ h

public theorem IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible [inst : IsAbsolutelyIrreducible ρ] : IsIrreducible ρ :=
  irreducible_of_extendScalars (AlgebraicClosure F) ρ (inst := inst.irreducible_of_closure)

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.irreducible_of_extension [FiniteDimensional F V]  (F' : Type*) [Field F'] [Algebra F F'] [inst : IsAbsolutelyIrreducible ρ] : IsIrreducible (extendScalars F' ρ) := by
  let : (extendScalars (AlgebraicClosure F) ρ).IsIrreducible := inst.irreducible_of_closure
  let : IsIrreducible ρ := irreducible_of_isAbsolutelyIrreducible ρ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine irreducible_of_jacobson_density_surjective (extendScalars F' ρ) ?_
  rw [← extendScalars_surj_iff F' ρ, extendScalars_surj_iff (AlgebraicClosure F) ρ]
  exact jacobson_density_surjective_isAlgClosed_rep (extendScalars (AlgebraicClosure F) ρ)

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars [FiniteDimensional F V]  (F' : Type*) [Field F'] [Algebra F F'] :
    IsAbsolutelyIrreducible (extendScalars F' ρ) ↔ IsAbsolutelyIrreducible ρ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [isAbsolutelyIrreducible_iff] at ⊢ h
    rw [RepEquiv.irreducible_euqiv (extendScalars_comp _)] at h
    let : Nontrivial V := by
      have : Nontrivial (AlgebraicClosure F' ⊗[F] V) := Subrepresentation.irreducible_module_nontrivial (extendScalars (AlgebraicClosure F') ρ)
      contrapose! this
      exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right F (AlgebraicClosure F')).mpr this
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    have : Algebra.adjoin (AlgebraicClosure F') (Set.range (extendScalars (AlgebraicClosure F') ρ)) = ⊤ := jacobson_density_surjective_isAlgClosed_rep _
    rw [← extendScalars_surj_iff (F := F) (F' := (AlgebraicClosure F'))] at this
    exact this
  · rw [isAbsolutelyIrreducible_iff] at ⊢ h
    rw [RepEquiv.irreducible_euqiv (extendScalars_comp _)]
    let : Nontrivial V := by
      have : Nontrivial (AlgebraicClosure F ⊗[F] V) := Subrepresentation.irreducible_module_nontrivial (extendScalars (AlgebraicClosure F) ρ)
      contrapose! this
      exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right F (AlgebraicClosure F)).mpr this
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    have : Algebra.adjoin (AlgebraicClosure F) (Set.range (extendScalars (AlgebraicClosure F) ρ)) = ⊤ := jacobson_density_surjective_isAlgClosed_rep _
    rw [← extendScalars_surj_iff (F := F) (F' := (AlgebraicClosure F))] at this
    exact this

variable {ρ} {σ}

public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_of_equiv (e : ρ ≃ₗ σ) :
    IsAbsolutelyIrreducible ρ → IsAbsolutelyIrreducible σ := fun h ↦ by
  rw [isAbsolutelyIrreducible_iff] at ⊢ h
  exact (RepEquiv.irreducible_euqiv <| extendScalars_equiv (AlgebraicClosure F) e).mp h

public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_equiv (e : ρ ≃ₗ σ) :
    IsAbsolutelyIrreducible ρ ↔ IsAbsolutelyIrreducible σ :=
  ⟨fun h ↦ isAbsolutelyIrreducible_of_equiv e h,
    fun h ↦ isAbsolutelyIrreducible_of_equiv e.symm h⟩

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_of_group_iso {H : Type*} [Monoid H] {ρ : Representation F G V} {σ : Representation F H V} (f : G ≃* H) (h : ∀ g : G, ∀ v : V, ρ g v = σ (f g) v) :
    IsAbsolutelyIrreducible ρ → IsAbsolutelyIrreducible σ := fun h1 ↦ by
  rw [isAbsolutelyIrreducible_iff] at ⊢ h1
  apply RepEquiv.irreducible_of_group_iso (ρ := extendScalars (AlgebraicClosure F) ρ) (σ := extendScalars (AlgebraicClosure F) σ) f
  intro g v
  let motive := fun (v : AlgebraicClosure F ⊗[F] V) ↦ ((extendScalars (AlgebraicClosure F) ρ) g) v = ((extendScalars (AlgebraicClosure F) σ) (f g)) v
  apply TensorProduct.induction_on (motive := motive)
  · simp only [extendScalars_apply, map_zero, motive]
  · intro x y
    unfold motive
    simp only [extendScalars_apply, LinearMap.baseChange_tmul]
    rw [h]
  · unfold motive
    intro x y hx hy
    simp only [extendScalars_apply, map_add] at hx hy ⊢
    rw [hx, hy]
  exact h1

public alias IsAbsolutelyIrreducible.isAbsolutelyIrreducible_of_monoid_iso :=
  IsAbsolutelyIrreducible.isAbsolutelyIrreducible_of_group_iso

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_group_iso {H : Type*} [Monoid H] {ρ : Representation F G V} {σ : Representation F H V} (f : G ≃* H) (h : ∀ g : G, ∀ v : V, ρ g v = σ (f g) v) :
    IsAbsolutelyIrreducible ρ ↔ IsAbsolutelyIrreducible σ := by
  have h' : ∀ g : H, ∀ v : V, σ g v = ρ (f.symm g) v := fun _ _ ↦ by
    simp_all only [MulEquiv.apply_symm_apply]
  refine ⟨isAbsolutelyIrreducible_of_group_iso f h,
    isAbsolutelyIrreducible_of_group_iso f.symm h'⟩

public alias IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_monoid_iso :=
  IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_group_iso

end AbsolutelyIrreducibleRep

end Representation
