module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ReductionA
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ReductionB
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ComponentGeometry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.PointGeneration

/-!
# Original-source application of unitary component geometry

The original contrary assumption puts the seed span in the point core's
omega-center. Reduction (b) supplies solvability, so the selected point
C-component is faithful. The genuine earlier 12.2 and 13.3.2 statements
supply uniqueness and maximality. Finally generation under the original
point centralizer makes the actual plane residual escape the component
normalizer. This proves the selected-component conclusions (e)--(f).

The selected C-component is still an explicit input: the point residual's
cubic quotient, nontrivial star core and the preceding Fitting argument
must construct it before final noncentrality assembly.
Source: Aschbacher--Smith 13.3.14, printed pp.891--892.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The selected point component satisfies the original faithful-local,
maximal-normalizer and plane-residual escape conclusions (e)--(f). The
existence of that component is the separate preceding (c)--(d) step. -/
theorem unitary_original_selected_component_geometry
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
    (hc : ⁅D.QH,B⁆ = ⊥) (K : Subgroup D.H) (hK : K.IsCComponent) :
    K.map D.H.subtype ∈ MainForward.faithfulLocalComponents D.T ∧
      K.map D.H.subtype ∈ Chapter1.LStar G D.T ∧
      D.H ≤ normalizer (K.map D.H.subtype : Set G) ∧
      IsMaximalTwoLocal (normalizer (K.map D.H.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        K.map D.H.subtype ⊔ (D.T : Subgroup G) ≤ N →
          N = normalizer (K.map D.H.subtype : Set G)) ∧
      ¬ D.L ≤ normalizer (K.map D.H.subtype : Set G) ∧
      ¬ K.map D.H.subtype ≤ normalizer (D.L : Set G) ∧
      ¬ (pResidual 2 (D.L ⊓ normalizer (B : Set G) : Subgroup G)).map
          (D.L ⊓ normalizer (B : Set G)).subtype ≤ normalizer (K.map D.H.subtype : Set G) := by
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  have hb := unitary_original_residual_solvable_and_odd_rank D h chosen hmax eL structural
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
  have ha := (unitary_flag_reduction_a D h chosen hTN hNL
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hc).2
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hH : IsTwoLocal D.H := by
    rw [hHfull]
    exact ⟨D.V₁,hZn,(IsElementaryAbelian.isPGroup 2 D.V).to_le hZV,rfl⟩
  have hf := unitary_component_faithful h.qtke D.T D.H D.UH hTH hH ha hb.1 K hK
  have h12 := unitary_original_hypothesis1223 h hmax eL
  have huniq := h12.source_normalizer_maximal_unique structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape h h12 earlier chosen e E0 he0 hZV hZ
  obtain ⟨hstar,hHN,hN,huni,hLN,hKM⟩ := unitary_component_normalizer_conclusions h.qtke D.T
    D.L D.H hTH hH chosen.sylow_normalizes_component huniq.1 huniq.2 hout h1332 K hK hf
  refine ⟨hf,hstar,hHN,hN,huni,hLN,hKM,?_⟩
  obtain ⟨rho,E,he,_,hd,hz,hp,_⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hh := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hh).le
  have hres : pResidual 2 D.L = ⊤ :=
    (pResidual_eq_top_iff 2 D.L).mpr (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1)
  have hgen := unitary_plane_residual_point_generation D.L B D.V₁ rho E he hp hz hBV hZV
    chosen.normalizes hfaith hres hd
  intro hXN
  apply hLN
  rw [←hgen]
  apply conjugateSpanBy_le hXN
  have hPH : D.L ⊓ centralizer (D.V₁ : Set G) ≤ D.H := by
    rw [hHfull]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  exact (hPH.trans hHN).trans (normalizer (K.map D.H.subtype : Set G)).le_normalizer
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
