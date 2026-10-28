module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.IntrinsicAlternatives

/-!
# The small MS classification on the actual binary input

The binary source input contains every MS hypothesis. Its literal product
identifies the generated carrier with the ambient group, so its finite SQTK,
characteristic-two, component, odd-index radical and characteristic-normal
conditions supply `SmallMSPair`. Apply the earlier C.1.34 implication and
transport every module alternative to the same ambient section conventions.
The common quotient marking and the original Sylow subgroup are preserved.

Source: Aschbacher–Smith C.1.31–34, printed pp.135–137;
15.3.23–24, printed pp.1128–1130.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
open RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {L R : Subgroup G}

/-- Every binary MS input satisfies the complete small MS hypotheses. -/
theorem smallMSPair_of_binary_input (h : ChapterC.BinaryMS.Input κ L R) :
    SmallMSPair κ L R := by
  refine ⟨inferInstance, (IsSQTK.equiv h.joinEquiv).mpr h.sqtk, ?_,
    fun g _ => h.product g, h.component.subgroupOf le_sup_left,
    Or.inl ⟨h.derivedQuotientEquiv⟩, ?_, ?_⟩
  · apply map_injective (f := h.joinEquiv.toMonoidHom) h.joinEquiv.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, h.fitting]
  · obtain ⟨H,hH,hodd,hcore⟩ := h.radical
    refine ⟨H, h.sup_eq_top.symm ▸ hH, ?_, hcore⟩
    change Odd (H.relIndex (L ⊔ R))
    rwa [h.sup_eq_top, relIndex_top_right]
  · intro C hC hn
    let _ := hC
    apply h.characteristic.eq_bot_of_normal C
    refine ⟨fun x hx g => ?_⟩
    exact (normal_subgroupOf_iff (show C.map R.subtype ≤ L ⊔ R from
      (map_subtype_le C).trans le_sup_right)).mp hn x g hx
        (h.sup_eq_top.symm ▸ mem_top g)

/-- Specialize the earlier classification to the literal binary pair and Sylow. -/
theorem binary_ms_module_alternatives_of_classifications
    (earlier : EarlierMSClassifications κ) (h : ChapterC.BinaryMS.Input κ L R)
    (P : Sylow 2 G) (hRP : R ≤ (P : Subgroup G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      MSModuleAlternatives L R (P : Subgroup G) 1 (ZMod 2) e := by
  have hP : Chapter1.IsSylowIn 2 (P : Subgroup G) (L ⊔ R) := by
    apply Chapter1.isSylowIn_iff.mpr
    refine ⟨P.isPGroup', ?_, fun U hU hPU _ => P.is_maximal' hU hPU⟩
    rw [h.sup_eq_top]
    exact le_top
  exact earlier.linearThree G L R (smallMSPair_of_binary_input h) 1 (by decide)
    (ZMod 2) (by simp) ⟨h.quotientEquiv⟩ (P : Subgroup G) hP hRP

open Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

/-- The exact five-case source conclusion used by the rank-two exclusions. -/
theorem binary_ms_alternatives_of_classifications
    (earlier : EarlierMSClassifications κ) (h : ChapterC.BinaryMS.Input κ L R)
    (P : Sylow 2 G) (hRP : R ≤ (P : Subgroup G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Alternatives (ZMod 2) 1 L R P e := by
  obtain ⟨e, he⟩ := binary_ms_module_alternatives_of_classifications earlier h P hRP
  exact ⟨e, alternatives_of_MSModuleAlternatives h.sup_eq_top P 1 (ZMod 2) e he⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
