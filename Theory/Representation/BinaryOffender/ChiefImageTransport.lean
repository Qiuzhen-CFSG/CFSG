module
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Sharp offenders and residual membership in literal action images

An equivariant identification of modules conjugates their faithful images,
including the image of each specified original actor. Thus sharp offending
transfers for the same subgroup. Equality of the original action kernels
also identifies preimages of the two-residual; no abstract quotient choice
or assumption on the order of the kernel is used.

Source application: Aschbacher–Smith3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {H V W : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) H W)
  (E : W ≃ₗ[ZMod 2] V) (hE : ∀ g w, ρ g (E w) = E (σ g w))

include E hE in
theorem sharp_image_offender_of_equivariant {A : Subgroup H}
    (hA : IsOffender (imageRepresentation σ) (actionSubgroup σ A))
    (hsharp : rank (actionSubgroup σ A) =
      fixedCodim (imageRepresentation σ) (actionSubgroup σ A)) :
    IsOffender (imageRepresentation ρ) (actionSubgroup ρ A) ∧
      rank (actionSubgroup ρ A) =
        fixedCodim (imageRepresentation ρ) (actionSubgroup ρ A) := by
  let f := MonoidHom.id H
  have hf : Function.Surjective f := fun x => ⟨x,rfl⟩
  let ψ : actionImage σ ≃* actionImage ρ := equivariantActionImageEquiv ρ σ f E hf hE
  have hψ (g : H) : ψ (actionHom σ g) = actionHom ρ g := by
    apply Subtype.ext
    exact conjugate_image_action ρ σ f E hE g
  have he : ∀ d w, E (imageRepresentation σ d w) =
      imageRepresentation ρ (ψ d) (E w) := by
    intro d w
    change E (d.val.val w) = E (d.val.val (E.symm (E w)))
    rw [E.symm_apply_apply]
  have hm : (actionSubgroup σ A).map ψ.toMonoidHom = actionSubgroup ρ A := by
    change (A.map (actionHom σ)).map ψ.toMonoidHom = A.map (actionHom ρ)
    rw [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro g
    exact hψ g
  refine ⟨?_,?_⟩
  · rw [←hm]
    exact hA.map_equivariant (imageRepresentation σ) (imageRepresentation ρ)
      ψ.toMonoidHom ψ.injective E he
  · rw [←hm,rank_map_injective ψ.toMonoidHom ψ.injective,
      ←fixedCodim_map_equivariant (imageRepresentation σ) (imageRepresentation ρ)
        ψ.toMonoidHom E he]
    exact hsharp
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {H V W : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem actionSubgroup_le_residual_iff (ρ : Representation (ZMod 2) H V) (A : Subgroup H) :
    actionSubgroup ρ A ≤ pResidual 2 (actionImage ρ) ↔ A ≤ pResidual 2 H ⊔ ρ.ker := by
  rw [actionSubgroup,← map_pResidual_of_surjective 2 (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective,Subgroup.map_le_iff_le_comap,
    Subgroup.comap_map_eq,actionHom_ker_eq]

theorem actionSubgroup_residual_iff_of_kernel_eq
    (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) H W)
    (hk : ρ.ker = σ.ker) (A : Subgroup H) :
    actionSubgroup ρ A ≤ pResidual 2 (actionImage ρ) ↔
      actionSubgroup σ A ≤ pResidual 2 (actionImage σ) := by
  rw [actionSubgroup_le_residual_iff,actionSubgroup_le_residual_iff,hk]
end Representation.BinaryOffender
