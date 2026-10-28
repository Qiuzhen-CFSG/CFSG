module
public import Glauberman.SmallMoverBaumann
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The core commutator of a class-two Baumann Sylow

Suppose the Sylow normally generates the ambient group, has class at most
two and elementary center. Its commutator lies in the ordinary Thompson
central omega. If adjoining a normal layer U to that omega is normal,
and the residual moves this enlargement into U, then the entire core
commutator with the residual lies in U. Normal generation gives the first
bound and residual idempotence improves it to U, keeping all fixed layers.

Source: the characteristic-two commutator consequence of Niles Theorem B
used in MS93 (5.1), printed p.913. The literal original replacement
application is in CriticalReduction.RootProductCommutator.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- The full elementary Sylow center lies in the ordinary Thompson omega. -/
theorem elementary_center_le_thompson_omega (S : Subgroup G)
    (he : omegaCenterIn S = centerIn S) :
    centerIn S ≤ omegaCenterIn (thompsonSubgroup S) := by
  have hh := smallMover_fixed_le_thompson_omega (omegaCenterIn S) S S
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) (thompsonSubgroup_le S)
  have hc : omegaCenterIn S ≤ centralizer (S : Set G) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  rwa [inf_eq_left.mpr hc,he] at hh

/-- Residual idempotence improves the class-two commutator into the supplied
normal moving layer, rather than discarding the full central omega. -/
theorem core_residual_le_of_class_two_thompson_layer
    (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    [(omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U : Subgroup G).Normal]
    (hgen : normalClosure ((S : Subgroup G) : Set G) = ⊤)
    (hclass : (S : Subgroup G).lowerCentralSeries 2 = ⊥)
    (he : omegaCenterIn (S : Subgroup G) = centerIn (S : Subgroup G))
    (hmove : ⁅omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U,pResidual 2 G⁆ ≤ U) :
    ⁅pCore 2 G,pResidual 2 G⁆ ≤ U := by
  let W := omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U
  have hcenter : ⁅(S : Subgroup G),(S : Subgroup G)⁆ ≤ centerIn (S : Subgroup G) :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (S : Subgroup G).le_normalizer)
      (commutator_eq_bot_iff_le_centralizer.mp hclass)
  have hc : ⁅pCore 2 G,(S : Subgroup G)⁆ ≤ W :=
    ((commutator_mono (pCore_isPGroup.le_sylow_of_normal S) le_rfl).trans hcenter).trans
      ((elementary_center_le_thompson_omega (S : Subgroup G) he).trans le_sup_left)
  have hwhole := commutator_normalClosure_le_of_normal (pCore 2 G) (S : Subgroup G) W hc
  rw [hgen] at hwhole
  have hfirst := (commutator_mono (le_refl (pCore 2 G)) (le_top : pResidual 2 G ≤ ⊤)).trans hwhole
  rw [←commutator_isPPerfect_idempotent (pResidual 2 G) (pCore 2 G)
    (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal]
  exact (commutator_mono hfirst le_rfl).trans hmove

end Glauberman
