module

public import Theory.Representation.BinaryOffender.SmallMovedProducts

/-!
# Moved-dimension bounds on literal sections

Restriction to an invariant submodule and passage to an actual quotient do
not increase the dimension of the whole commutator span. Equivariant linear
coordinates preserve this dimension. These elementary comparisons transport
the original seed-plane bound to the B.4.2 quotient models in 13.7.15.
-/

public section
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

theorem subspaceCommutator_comp_map (f : D →* G) (I : Submodule (ZMod 2) V)
    (A : Subgroup D) :
    subspaceCommutator (ρ.comp f) I A = subspaceCommutator ρ I (A.map f) := by
  simpa only [Submodule.map_id] using subspaceCommutator_map_embedding
    (ρ.comp f) ρ f (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) A I

theorem moved_finrank_equivariant (f : G →* D) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) =
      Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (A.map f)) := by
  have hh := subspaceCommutator_map_embedding ρ σ f e.symm.toLinearMap
    (fun g v => by
      apply e.injective
      simp [he]) A ⊤
  rw [Submodule.map_top, LinearEquiv.range] at hh
  rw [hh,e.symm.finrank_map_eq]

variable [FiniteDimensional (ZMod 2) V]

theorem moved_finrank_subrepresentation_le (U : Subrepresentation ρ) (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator U.toRepresentation ⊤ A) ≤
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  have hh := moved_finrank_map_le_of_embedding ρ U.toRepresentation
    (MonoidHom.id G) U.toSubmodule.subtype U.toSubmodule.subtype_injective (fun _ _ => rfl) A
  rw [Subgroup.map_id] at hh
  exact hh

theorem moved_finrank_quotient_le (U : Subrepresentation ρ) (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator U.quotientRepresentation ⊤ A) ≤
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  have hh := subspaceCommutator_map_embedding U.quotientRepresentation ρ
    (MonoidHom.id G) U.toSubmodule.mkQ (fun _ _ => rfl) A ⊤
  rw [Submodule.map_top,Submodule.range_mkQ,Subgroup.map_id] at hh
  rw [hh]
  exact Submodule.finrank_map_le _ _

/-- The offender inequality survives both literal section operations. -/
theorem IsOffender.on_subquotient (U : Subrepresentation ρ)
    (C : Subrepresentation U.toRepresentation) {A : Subgroup G} (hA : IsOffender ρ A) :
    IsOffender C.quotientRepresentation A := by
  refine ⟨hA.1,?_⟩
  have hU := fixedCodim_subrepresentation_le ρ U A
  have hC := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation C A
  have ha := hA.2
  omega
end Representation.BinaryOffender
