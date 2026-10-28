module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Kernels

/-!
# Transport of degree-six rigidity along compatible actions

An injective actor map and an equivariant linear equivalence identify the
actual commutator spaces, fixed spaces and subgroup ranks. Consequently the
rank-one and transvection-kernel results apply to subgroups of either the
symmetric or alternating action image, with the chosen action marking intact.

Source: the model substitutions in Aschbacher–Smith 13.8.26, printed p.962.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
open BinaryPermutation Representation.BinaryOffender

private theorem elementary_map {G D : Type*} [Group G] [Group D]
    (f : G →* D) (hf : Function.Injective f) {A : Subgroup G}
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map f) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  exact ⟨fun h => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp h),
    IsElementaryAbelian.map f⟩

private theorem commutator_finrank_equivariant
    {G D U W : Type*} [Group G] [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G U) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (E : U ≃ₗ[ZMod 2] W)
    (he : ∀ g u, E (ρ g u) = σ (f g) (E u)) (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) =
      Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (A.map f)) := by
  have he' (g : G) (w : W) : ρ g (E.symm w) = E.symm (σ (f g) w) := by
    apply E.injective
    simpa using he g (E.symm w)
  have hc := subspaceCommutator_map_embedding ρ σ f E.symm.toLinearMap he' A ⊤
  have htop : (⊤ : Submodule (ZMod 2) W).map E.symm.toLinearMap = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr E.symm.surjective]
  rw [htop] at hc
  rw [hc]
  exact (Submodule.equivMapOfInjective E.symm.toLinearMap E.symm.injective
    (subspaceCommutator σ ⊤ (A.map f))).finrank_eq.symm

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G U) (f : G →* Symmetric) (hf : Function.Injective f)

include hf

/-- The common-commutator-line bound for an equivariantly identified natural action. -/
theorem natural_rank_one_equivariant (E : U ≃ₗ[ZMod 2] Natural)
    (he : ∀ g u, E (ρ g u) = symmetricAction (f g) (E u))
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hline : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1) : rank A = 1 := by
  rw [commutator_finrank_equivariant ρ symmetricAction f E he A] at hline
  rw [← rank_map_injective f hf A]
  exact rank_one_of_natural_commutator_le_one (elementary_map f hf hA) hline

/-- The common-commutator-line bound for an equivariantly identified augmentation action. -/
theorem core_rank_one_equivariant (E : U ≃ₗ[ZMod 2] Augmentation)
    (he : ∀ g u, E (ρ g u) = coreRepresentation (Fin 6) (f g) (E u))
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hline : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1) : rank A = 1 := by
  rw [commutator_finrank_equivariant ρ (coreRepresentation (Fin 6)) f E he A] at hline
  rw [← rank_map_injective f hf A]
  exact rank_one_of_core_commutator_le_one (elementary_map f hf hA) hline

/-- Pointwise-kernel rigidity in the actual group acting on a recognized natural module. -/
theorem natural_kernel_equivariant (E : U ≃ₗ[ZMod 2] Natural)
    (he : ∀ g u, E (ρ g u) = symmetricAction (f g) (E u))
    {A : Subgroup G} (hA : IsElementaryTwo A) (hc : fixedCodim ρ A = 1) :
    subspaceKernel ρ (fixedSpace ρ A) ⊤ = A := by
  apply fixed_kernel_eq_of_equivariant ρ symmetricAction f hf E he A
  apply natural_fixed_kernel (elementary_map f hf hA)
  rw [← fixedCodim_map_equivariant ρ symmetricAction f E he A]
  exact hc

/-- Pointwise-kernel rigidity in the actual group acting on a recognized augmentation cover. -/
theorem core_kernel_equivariant (E : U ≃ₗ[ZMod 2] Augmentation)
    (he : ∀ g u, E (ρ g u) = coreRepresentation (Fin 6) (f g) (E u))
    {A : Subgroup G} (hA : IsElementaryTwo A) (hc : fixedCodim ρ A = 1) :
    subspaceKernel ρ (fixedSpace ρ A) ⊤ = A := by
  apply fixed_kernel_eq_of_equivariant ρ (coreRepresentation (Fin 6)) f hf E he A
  apply core_fixed_kernel (elementary_map f hf hA)
  rw [← fixedCodim_map_equivariant ρ (coreRepresentation (Fin 6)) f E he A]
  exact hc

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
