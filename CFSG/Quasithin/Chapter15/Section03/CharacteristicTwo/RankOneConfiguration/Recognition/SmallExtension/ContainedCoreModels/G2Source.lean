module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.BlockTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.G2Dual

/-!
# Containment of the whole G₂-block core

The original quotient marking sends M ∩ L to the prescribed null-plane
stabilizer. The source identity Y₊ = O^{3′}(M ∩ L) therefore identifies
the actual Y₊ image with the residual on which contragredient cocycles
are detected. The short-block transport applies to the whole U(L), retaining
its fixed kernel, and proves Q = [Q,Y₊]. The source normalizer calculation
then gives Q ≤ O₂(Y₊), so D = C_I(Y₊) centralizes Q. This discharges the
core-centralization premise of SourceData.excluded_of_models.

Inputs are exactly SourceData and the fields of MarkedModels.g2; construction
of that marked configuration remains with the source assembly owner.

Source: Aschbacher–Smith, C.1.7, C.1.30 and I.1.5–6, and the proof of
15.3.31, printed p.1132 (PDF p.1149).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover ChapterC
namespace ContainedCoreModels

variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
  (s : SourceData κ d c) (short : IsShort c.L)
  (model : BlockModuleModel c.L
    (BlockModels.multiplicativeAction BlockModels.G2.action))
  (parabolic : ((d.M ⊓ c.L).subgroupOf c.L).map
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
      BlockModels.planeStabilizer BlockModels.G2.action BlockModels.G2.markedPlane)
include s short model parabolic

/-- The actual marked G₂ residual generates the entire source core. -/
theorem g2_core_eq_commutator :
    extensionCore c.L = ⁅extensionCore c.L, d.Yplus⁆ := by
  apply core_eq_commutator_of_short_detected_dual s.contains short model
  have hY : d.Yplus.subgroupOf c.L =
      (primeToResidual 3 ((d.M ⊓ c.L).subgroupOf c.L)).map
        ((d.M ⊓ c.L).subgroupOf c.L).subtype := by
    apply Subgroup.map_injective c.L.subtype_injective
    rw [map_subgroupOf_eq_of_le s.contains,
      map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le inf_le_right]
    exact s.component_residual
  rw [hY, map_embedded_primeToResidual_of_hom, parabolic]
  exact G2.dual_detected_on_markedPlane_residual

/-- The whole G₂-block core lies in the two-core of the original Y₊. -/
theorem g2_core_le_yplus_core :
    extensionCore c.L ≤ d.Yplus.pCoreIn 2 := by
  rw [g2_core_eq_commutator s short model parabolic]
  exact core_commutator_le_yplus_core s

/-- The source D centralizes the whole G₂-block core, including its fixed kernel. -/
theorem g2_centralizes_core :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
  inf_le_right.trans (centralizer_le
    ((g2_core_le_yplus_core s short model parabolic).trans (pCoreIn_le 2 d.Yplus)))

/-- Exclusion of the marked G₂ configuration with no additional core premise. -/
theorem g2_excluded : False :=
  s.excluded_of_models (.g2 short model parabolic)
    (g2_centralizes_core s short model parabolic)

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
