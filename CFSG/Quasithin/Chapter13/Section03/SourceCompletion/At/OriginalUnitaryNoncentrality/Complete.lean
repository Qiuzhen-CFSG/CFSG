module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Complete
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryBaumann.SourceComplete
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.SourceEscape

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.Complete`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact original unitary plane-noncentrality conclusion. -/
theorem unitary_original_noncentrality
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
 : ⁅D.QH,B⁆ ≠ ⊥ := by
  intro hc
  exact unitary_original_baumann_escape D h chosen hmax eL structural e E0 he0
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
    (unitary_original_baumann_bound D h chosen hmax eL structural e E0 he0
      hUV hZV hTZ hTU hZ hU B hBV hTB hB)

/-- The original exclusion consumer now receives proved noncentrality under the original source hypotheses. Its independent odd-normalizer and escape-action
inputs retain their original final assembly owner. -/
theorem unitary_original_false_of_noncentrality_sources
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)

    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  have hm := unitary_original_noncentrality D h chosen hmax eL structural e E0 he0 hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five
  exact unitary_original_false_of_earlier_sources D h hmax eL chosen structural earlier
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hplanes hact hodd

/-- The original13.3.15/17 parabolic-control consumer, with its exact
plane movement premise proved under the original source hypotheses. -/
theorem unitary_original_parabolic_control_of_noncentrality_sources
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
 :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) ∧
      D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) := by
  have hm := unitary_original_noncentrality D h chosen hmax eL
    structural e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
    h1332 fixed five
  have h12 := unitary_original_hypothesis1223 h hmax eL
  have hred := ((structural D.L h12).2.2 D.V chosen).2.1
  have hNL := (unitary_original_module_normalizers h hmax eL chosen structural).2
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  exact unitary_original_parabolic_control D e E0 he0 hUV hZV hTZ hTU hZ hU
    ((pResidual_eq_top_iff 2 D.L).mpr (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1))
    chosen.sylow_normalizes_component (chosen.le_sylow.trans le_sup_right) hred hNL hfaith
    B hBV hTB hB hHfull hm (h12.source_chosen_TI_at structural chosen)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
