module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation
public import Theory.Representation.BinaryPermutation.SevenMarkedAction

/-!
# Relabelling a whole-module seven-letter chart

Conjugate the actor and apply the same permutation to module coordinates.
The conjugation formula, A₇ image and action kernel are preserved.
Source application: Aschbacher--Smith 4.3.7, printed p.616.
-/

public noncomputable section
open Subgroup BinaryPermutation BinaryPermutation.SevenMarkedAction
namespace BinaryPermutation.SevenParabolic.Ordinary.Chart
variable {G : Type*} [Group G] {J K U : Subgroup G}

@[expose] def reindex (d : Chart J K U) (σ : Equiv.Perm (Fin 7)) : Chart J K U where
  moduleEquiv := d.moduleEquiv.trans (coreAction σ)
  actor := (MulAut.conj σ).toMonoidHom.comp d.actor
  normalized := d.normalized
  component_image := by
    rw [← map_map,d.component_image]
    exact mem_normalizer_iff_map_conj_eq.mp ((alternatingGroup (Fin 7)).normalizer_eq_top ▸ mem_top σ)
  equivariant := by
    intro j u
    change coreRepresentation (Fin 7) σ (d.moduleEquiv _).toAdd =
      coreRepresentation (Fin 7) (σ * d.actor j * σ⁻¹)
        (coreRepresentation (Fin 7) σ (d.moduleEquiv u).toAdd)
    rw [d.equivariant]
    simp only [map_mul,Module.End.mul_apply]
    rw [(coreRepresentation (Fin 7)).inv_self_apply]

theorem reindex_ker (d : Chart J K U) (σ : Equiv.Perm (Fin 7)) :
    (d.reindex σ).actor.ker = d.actor.ker :=
  MonoidHom.ker_comp_of_injective _ _ (MulAut.conj σ).injective

end BinaryPermutation.SevenParabolic.Ordinary.Chart

