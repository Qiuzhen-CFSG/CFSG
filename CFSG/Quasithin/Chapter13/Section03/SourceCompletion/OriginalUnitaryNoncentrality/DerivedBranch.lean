module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.DerivedAction
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.SourceEscape

/-!
# Noncentrality in the original unitary component-action branch

The actual LT action may equal the component image or enlarge it to G₂(2).
In the first branch, the proved normalizer bound contradicts the original
Baumann escape. This discharges the literal plane-noncentrality premise
in the original exclusion consumer for that branch. The full G₂(2) image
remains a separate local obligation of qt-d-13316-noncentrality.
Earlier universal source statements and plane-centralizer control retain
final discharge in qt-d-13316-source.

Source: Aschbacher--Smith13.3.10(2) and13.3.14, pp.887--888,891--893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Plane noncentrality with the original component-action branch discharged. -/
theorem unitary_original_noncentrality_of_component_action
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G)) ≤
      inducedAutomizer D.V D.L) : ⁅D.QH,B⁆ ≠ ⊥ := by
  intro hc
  exact unitary_original_baumann_escape D h chosen hmax eL structural e E0 he0 hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
    (unitary_original_baumann_bound_of_component_action D h chosen hmax eL structural e E0 he0 hsmall)

/-- The original exclusion consumer now receives proved noncentrality in
this action branch. Its independent odd-normalizer and escape-action inputs
are unchanged. -/
theorem unitary_original_false_of_component_action
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G)) ≤
      inducedAutomizer D.V D.L)
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  have hm := unitary_original_noncentrality_of_component_action D h chosen hmax eL structural e E0 he0 hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hsmall
  exact unitary_original_false_of_earlier_sources D h hmax eL chosen structural earlier
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hplanes hact hodd

/-- The original13.3.15/17 parabolic-control consumer, with its exact
plane movement premise proved in the component-action branch. -/
theorem unitary_original_parabolic_control_of_component_action
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G)) ≤
      inducedAutomizer D.V D.L) :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) ∧
      D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) := by
  have hm := unitary_original_noncentrality_of_component_action D h chosen hmax eL
    structural e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
    h1332 fixed five hsmall
  have h12 := unitary_original_hypothesis1223 h hmax eL
  have hred := ((structural G D.T D.L h12).2.2 D.V chosen).2.1
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
    B hBV hTB hB hHfull hm (h12.source_chosen_TI structural chosen)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
