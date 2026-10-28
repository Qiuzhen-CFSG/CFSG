module
public import Theory.GroupTheory.SmallMoverFamily
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Fixed subgroups under commuting quotient actions

If two actors commute modulo a kernel centralizing V, either actor
normalizes the other's fixed subgroup in V. Saturating by the literal
kernel preserves fixed points and turns the assertion into ordinary
normalizer functoriality. No splitting of the action kernel is required.

Source application: MS93 (5.7), p.919; SymplecticFour.SmallMoverKernel.
-/

public section
open Subgroup
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

theorem normalizes_fixed_of_commuting_action_images
    (V J A : Subgroup G) (q : G →* K)
    (hJV : J ≤ normalizer (V : Set G))
    (hk : q.ker ≤ centralizer (V : Set G))
    (hc : J.map q ≤ centralizer (A.map q : Set K)) :
    J ≤ normalizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  let N := (A.map q).comap q
  have hJN : J ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro j hj a ha
    change q (j*a*j⁻¹) ∈ A.map q
    rw [map_mul,map_mul,map_inv]
    have hh := hc (mem_map_of_mem q hj) (q a) ha
    rw [←hh,mul_inv_cancel_right]
    exact ha
  have hfix : V ⊓ centralizer (N : Set G) = V ⊓ centralizer (A : Set G) := by
    dsimp only [N]
    rw [comap_map_eq, sup_comm]
    exact SmallMover.fixed_inf_sup V q.ker A (le_centralizer_iff.mp hk)
  rw [←hfix]
  exact (le_inf hJV (hJN.trans (normalizer_le_normalizer_centralizer N))).trans
    inf_normalizer_le_normalizer_inf
end Subgroup
