module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicStarGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction

/-!
# The original marked centralizer contains the cubic layer kernel

The original fixed subgroup E lies in the full star module. Its centralizer
is the actual M_Z. Thus every element in the literal layer kernel fixes E
and belongs to M_Z, hence normalizes Q1. In the cubic-kernel branch this
places the entire retained extension kernel in the original radical's
normalizer, with the ambient subtype map preserved.

This supplies a source placement premise for the cubic-plane exclusion;
it does not remove the cubic covering kernel or assume a Sylow radical.

Source: Aschbacher--Smith 15.1.18--20, pp.1093--1095, and C.2.7, p.146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Exceptional.Exhaustion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The full star-module kernel lies in the actual marked centralizer. -/
theorem layerKernel_le_marked_centralizer (d : CaseIComponentData T M Mc V)
    (E : Subgroup G)
    (hE : E ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype)
    (hMZ : d.MZ = centralizer (E : Set G)) :
    (layerKernel d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ≤ d.MZ := by
  rintro x ⟨a,ha,rfl⟩
  apply hMZ.ge
  intro z hz
  obtain ⟨b,hb,rfl⟩ := hE hz
  exact congrArg Subtype.val (ha b hb)

/-- The retained cubic kernel normalizes the same original radical. The
placement follows from the marked seed, without any Sylow upgrade. -/
theorem cubic_extensionKernel_normalizes_radical
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hMZ : d.MZ = centralizer (E : Set G))
    (hk : layerKernel d.L d.Q1 = extensionKernel hms) :
    extensionKernel hms ≤ normalizer
      (d.Q1.subgroupOf (d.L ⊔ d.Q1) : Set (d.L ⊔ d.Q1 : Subgroup G)) := by
  have hplace : (extensionKernel hms).map (d.L ⊔ d.Q1 : Subgroup G).subtype ≤ d.MZ := by
    rw [←hk]
    exact d.layerKernel_le_marked_centralizer E (d.marked_core_star_geometry hi E hMZ).1 hMZ
  have hn : (extensionKernel hms).map (d.L ⊔ d.Q1 : Subgroup G).subtype ≤
      normalizer (d.Q1 : Set G) := hplace.trans (s.core_normalizer.ge.trans inf_le_right)
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  change (x : G) ∈ d.Q1 ↔ (a : G) * (x : G) * (a : G)⁻¹ ∈ d.Q1
  exact mem_normalizer_iff.mp (hn (mem_map_of_mem _ ha)) x

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
