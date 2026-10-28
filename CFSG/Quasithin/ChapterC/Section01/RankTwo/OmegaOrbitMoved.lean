module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbit

/-!
# Full movement from a seed of the omega orbit

If the Sylow omega center lies in a subgroup fully moved by a subgroup of a
normal component, normal closure puts the entire omega orbit in its commutator
with that component. This is the elementary orbit step in source 9.3.7.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {G : Type*} [Group G]

theorem omegaOrbit_fully_moved_of_moved_seed (R V L K : Subgroup G) [K.Normal]
    (hRV : omegaCenterIn R ≤ V) (hVW : V ≤ omegaOrbit R)
    (hLK : L ≤ K) (hVL : ⁅V,L⁆ = V) :
    omegaOrbit R ≤ K ∧ ⁅omegaOrbit R,K⁆ = omegaOrbit R := by
  have hVK : V ≤ K := by
    rw [←hVL]
    exact (commutator_mono le_rfl hLK).trans (commutator_le_right _ _)
  have hWK : omegaOrbit R ≤ K := normalClosure_le_normal (hRV.trans hVK)
  refine ⟨hWK,le_antisymm (commutator_le_left _ _) ?_⟩
  apply normalClosure_le_normal
  rw [←hVL] at hRV
  exact hRV.trans (commutator_mono hVW hLK)

end CFSG.Quasithin.ChapterC.MSCentralOrbit
