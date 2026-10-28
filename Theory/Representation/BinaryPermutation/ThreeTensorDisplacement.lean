module

public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Displacement dimensions for a tensor product with the binary S₃-module

A nonidentity second component moves at least the dimension of the first
factor. For an actor in the first factor, displacement dimension doubles,
because restriction to that factor is equivariantly two copies of its module.
These statements apply to individual elements, without any assumption that
their orders are two.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the tensor
inspection in 14.4.6(a), printed p.1008; the same calculation occurs in 13.8.21.
-/

public section
namespace BinaryPermutation.ThreeTensor
open Representation Representation.BinaryOffender Subgroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- A nontrivial S₃ component forces a full first-factor displacement bound. -/
theorem dimension_le_displacement (g : G × Equiv.Perm (Fin 3)) (hg : g.2 ≠ 1) :
    Module.finrank (ZMod 2) V ≤
      Module.finrank (ZMod 2) (LinearMap.range (action ρ g - LinearMap.id)) := by
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  exact dimension_le_fixedCodim ρ (zpowers g) g (mem_zpowers g) hg

/-- A pure first-factor actor has twice its original displacement dimension. -/
theorem displacement_first (g : G) :
    Module.finrank (ZMod 2) (LinearMap.range (action ρ (g, 1) - LinearMap.id)) =
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) := by
  let ι : G →* G × Equiv.Perm (Fin 3) := MonoidHom.inl _ _
  have he := fixedCodim_map_equivariant ((action ρ).comp ι) (ρ.prod ρ)
    (MonoidHom.id G) pairEquiv (pairEquiv_equivariant ρ) (zpowers g)
  simp only [Subgroup.map_id, fixedCodim_prod] at he
  have hc : fixedCodim ((action ρ).comp ι) (zpowers g) =
      fixedCodim (action ρ) (zpowers (g, 1)) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    rfl
  rw [hc, fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at he
  omega

end BinaryPermutation.ThreeTensor
