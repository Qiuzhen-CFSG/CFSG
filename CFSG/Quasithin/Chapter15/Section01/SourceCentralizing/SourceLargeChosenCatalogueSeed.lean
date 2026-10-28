module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock
-- Intentional internal extension of the selected-component catalogue: the
-- existing original central-seed lemma is reused without changing its owner.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock

/-!
# The original central seed controls the selected cubic kernel

For the literal pre-exclusion source, T normalizes M_Z and its nontrivial
radical. The original central seed Z lies in Q₁, hence in Ω₁Z(Q₁) and the
full star module. The full layer kernel therefore fixes Z. It lies in G₁
and in C_G(Z) ≤ M_c, so it lies in M_Z and normalizes the original Q₁.

This replaces the stronger special-row equality M_Z = C_G(E). It applies
only to the actual source geometry; no universal MS reconstruction is used.
Source: Aschbacher--Smith 15.1.18 and 15.1.20, pp.1093--1095; C.2.7, p.146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Exceptional.Exhaustion
open AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original central seed lies in the full star module of the same
selected component and original radical. -/
theorem PreExclusionSource.central_seed_le_original_star
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L) :
    centralInvolutions T ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype := by
  have hZQ := d.central_seed_le_radical hG h hTM hu s.core_nontrivial s.sylow_normalizes_MZ
  have hQT := (d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans d.S_le_T
  apply le_trans ?_ (omega_radical_le_starV_from_source hi)
  intro z hz
  apply (mem_omegaOneCenterAmbient_iff d.Q1 z).mpr
  exact ⟨hZQ hz,((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.1,
    fun q hq => centralInvolutions_le_centralizer_sylow T hz q (hQT hq)⟩

/-- In the retained cubic-kernel branch the actual source geometry forces
normalization of the literal original radical. -/
theorem PreExclusionSource.original_cubic_kernel_normalizes_radical
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (hk : layerKernel d.L d.Q1 = extensionKernel hms) :
    extensionKernel hms ≤ normalizer
      (d.Q1.subgroupOf (d.L ⊔ d.Q1) : Set (d.L ⊔ d.Q1 : Subgroup G)) := by
  have hZ := s.central_seed_le_original_star (h := h) hG hTM hu hi
  have hJ : d.L ⊔ d.Q1 ≤ d.G1 := sup_le d.L_component.1 (d.Q1_le_MZ.trans inf_le_left)
  have hplace : (extensionKernel hms).map (d.L ⊔ d.Q1 : Subgroup G).subtype ≤ d.MZ := by
    rintro x ⟨a,ha,rfl⟩
    refine ⟨hJ a.property,centralizer_le_partner T hu ?_⟩
    have haL : a ∈ layerKernel d.L d.Q1 := hk.symm ▸ ha
    intro z hz
    obtain ⟨b,hb,rfl⟩ := hZ hz
    exact congrArg Subtype.val (haL b hb)
  have hn : (extensionKernel hms).map (d.L ⊔ d.Q1 : Subgroup G).subtype ≤
      normalizer (d.Q1 : Set G) := hplace.trans (s.core_normalizer.ge.trans inf_le_right)
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  change (x : G) ∈ d.Q1 ↔ (a : G) * (x : G) * (a : G)⁻¹ ∈ d.Q1
  exact mem_normalizer_iff.mp (hn (mem_map_of_mem _ ha)) x

/-- The same original source has whole-core exhaustion in the cubic
six-point branch; the two remaining radical images are both impossible. -/
theorem PreExclusionSource.original_cubic_coreExhaustion
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) :
    CoreExhaustion d.L d.Q1 := by
  let e := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  rcases CubicFull.coreExhaustion_or_cubic_plane_paths hms e hz with
    hx | ⟨hk,_,_,_,a,hb | ⟨hp,_⟩⟩
  · exact hx
  · exact (CubicFull.extensionKernel_not_normalizes_remaining_radical hms e hz hk a
      (Or.inr hb) (s.original_cubic_kernel_normalizes_radical (h := h) hG hTM hu hi hms hk)).elim
  · exact (CubicFull.extensionKernel_not_normalizes_remaining_radical hms e hz hk a
      (Or.inl hp) (s.original_cubic_kernel_normalizes_radical (h := h) hG hTM hu hi hms hk)).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
