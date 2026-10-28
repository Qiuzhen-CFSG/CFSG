module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicKernelPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ExceptionalSixExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizerExclusion

/-!
# Excluding the original cubic component from its marked centralizer

The original elementary marked subgroup has centralizer M_Z and lies in the
full star module by C.2.7. Thus, in the retained cubic-kernel branch, the
extension kernel normalizes the literal Q₁. The finite triple-cover
involution theorem excludes both remaining symmetric radical images.

The whole core therefore has the exceptional cubic block structure, which
the original marked source excludes. No global residual-centralization or
Sylow-radical hypothesis enters this argument.

Source: Aschbacher--Smith 15.1.18--26, pp.1093--1102; C.1.32 and C.2.7.
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

/-- The actual marked centralizer rules out both remaining cubic radical
images and forces exhaustion of the whole original core. -/
theorem PreExclusionSource.cubic_coreExhaustion_of_marked_centralizer
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hMZ : d.MZ = centralizer (E : Set G))
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
      (Or.inr hb) (cubic_extensionKernel_normalizes_radical (h := h) s hi hms E hMZ hk)).elim
  · exact (CubicFull.extensionKernel_not_normalizes_remaining_radical hms e hz hk a
      (Or.inl hp) (cubic_extensionKernel_normalizes_radical (h := h) s hi hms E hMZ hk)).elim

/-- The original selected source has no cubic six-point MS component with
its actual elementary marked centralizer. -/
theorem PreExclusionSource.false_of_cubic_marked_source
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hMZ : d.MZ = centralizer (E : Set G))
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) : False := by
  let e := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  have hx := s.cubic_coreExhaustion_of_marked_centralizer (h := h) hi hms E hMZ t hz
  obtain ⟨he,hc,hirr,h64,hfaith⟩ := core_facts_of_exhaustion hms e hz hx
  have hs := hms.short_of_core he hc s.quasisimple hirr
  have hb : IsExceptionalAhat6Block d.L :=
    ⟨hs,s.quasisimple,hz,
      ⟨(centralPreimageQuotientEquiv (pCore 2 d.L)).symm.trans t⟩,h64,hfaith⟩
  exact s.not_constrained_exceptionalSix (h := h) hG hM hu hb

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
