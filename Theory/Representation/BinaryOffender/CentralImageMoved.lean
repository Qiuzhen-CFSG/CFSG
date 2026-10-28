module
public import Theory.Representation.BinaryOffender.IrreducibleCentralLift
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Recovering a perfect actor's moved space from a central image

An irreducible faithful image of an invariant space is Irr⁺. A central
surjection lifts this property, and perfectness identifies its commutator
with the whole moved space whenever the containing space includes every
displacement. The proof retains the original inclusion and quotient map.

Source application: Aschbacher–Smith B.5.6(3),(5), p.105, and 12.3.8, p.810.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {D V W : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem irrPlus_top_of_irreducible
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [Nontrivial C]
    (hi : IsIrreducible (ρ.comp C.subtype))
    (hf : Function.Injective (ρ.comp C.subtype)) : IsIrrPlus ρ C ⊤ := by
  let := hi
  have hmin (J : Submodule (ZMod 2) V) (hJ : C ≤ subspaceStabilizer ρ J) :
      J = ⊥ ∨ J = ⊤ := by
    let R : Subrepresentation (ρ.comp C.subtype) :=
      ⟨J,fun c v hv => (hJ c.property v).2 hv⟩
    exact (eq_bot_or_eq_top R).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)
  have hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ C := by
    intro h
    obtain ⟨c,hc⟩ := exists_ne (1 : C)
    apply hc
    apply hf
    ext v
    simpa only [map_one, Module.End.one_apply] using h (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top) c
  apply isIrrPlus_of_minimal ρ (le_subspaceStabilizer _ _ (by intros; trivial))
  · rcases hmin (subspaceCommutator ρ ⊤ C) (subspaceCommutator_invariant _ _ _) with h | h
    · exact (hn ((subspaceCommutator_eq_bot_iff _ _ _).mp h)).elim
    · exact h
  · exact hn
  · intro J hJ _
    rcases hmin J hJ with rfl | h
    · exact Or.inr bot_le
    · exact Or.inl h

/-- A central image of a containing invariant space determines the whole moved layer. -/
theorem moved_irrPlus_of_central_image
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (C : Subgroup D) [Group.IsPerfect C] [Nontrivial C]
    (U : Subrepresentation ρ) (hm : subspaceCommutator ρ ⊤ C ≤ U.toSubmodule)
    (f : U.toSubmodule →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ c : C, ∀ v, f (U.toRepresentation c v) = σ c (f v))
    (hk : f.ker ≤ fixedSpace U.toRepresentation C)
    (hi : IsIrreducible (σ.comp C.subtype))
    (hfaith : Function.Injective (σ.comp C.subtype)) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  have h := IsIrrPlus.of_central_surjection U.toRepresentation σ C f hf he hk
    (irrPlus_top_of_irreducible σ C hi hfaith)
  have ht := IsIrrPlus.map_embedding ρ U.toRepresentation (MonoidHom.id D)
    U.toSubmodule.subtype U.toSubmodule.subtype_injective (fun _ _ => rfl)
    C (subspaceCommutator U.toRepresentation ⊤ C) (by simpa only [Subgroup.map_id] using h)
  have heq := subspaceCommutator_map_embedding ρ U.toRepresentation (MonoidHom.id D)
    U.toSubmodule.subtype (fun _ _ => rfl) C ⊤
  rw [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,
    subspaceCommutator_eq_moved_of_contains_moved ρ C _ hm] at heq
  rwa [←heq] at ht

end Representation.BinaryOffender
