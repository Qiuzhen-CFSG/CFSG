module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalGeometry
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.FinalAssembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.Complete

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalGeometry`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE
open Chapter12.Section02 OriginalPlaneCentralizers
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
  (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
  (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
  (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
  (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
  (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
  (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
  (B : Subgroup G) (hBV : B ≤ D.V)
  (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
  (hHfull : D.H = normalizer (D.V₁ : Set G))
  (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
  (fixed : OriginalFixedModule1332At D.T D.L)
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- Noncentrality, strict rank and parabolic consequences of original
13.3.17, recording the three-space centralizer in N(L) for 4.4.3. -/
theorem unitary_original_geometric_controls :
    ⁅D.QH,B⁆ ≠ ⊥ ∧ (3 : ℕ∞) < globalR D.V ∧
      centralizer (D.Vplus : Set G) ≤ normalizer (D.L : Set G) ∧
      D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) := by
  have hp := planeCentralizers_of_source s
  have hm := unitary_original_noncentrality D s.hypothesis s.chosen s.maximal s.quotient
    s.structural s.actor s.coordinates s.equivariant hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull earlier hp h1332 fixed five
  have hr := unitary_rank_gt_three_of_original_plane_source D s hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull hm
  have hc := unitary_original_parabolic_control_of_noncentrality_sources D
    s.hypothesis s.chosen s.maximal s.quotient s.structural s.actor s.coordinates s.equivariant
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hp h1332 fixed five
  have hNL := (unitary_original_module_normalizers s.hypothesis s.maximal s.quotient
    s.chosen s.structural).2
  exact ⟨hm,hr,hc.1.trans hNL,hc.2⟩

/-- The terminal Hall actor with all local geometric and applicability
premises discharged. Its normalizer escape is literal inside the chosen H. -/
theorem unitary_original_escaping_prime_actor_of_source_geometry :
    ∃ H ∈ Chapter3.HStar (D.T : Subgroup G) (normalizer (D.L : Set G)),
      H ≤ D.H ∧ 2 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
        IsElementaryAbelian p A ∧ A ≤ H ⊓ normalizer (D.L : Set G) ∧
        A ≤ centralizer (D.V : Set G) ∧ ⁅A,D.L⁆ ≤ D.L.pCoreIn 2 ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (D.L : Set G) := by
  have hm := (unitary_original_geometric_controls D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five).1
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  obtain ⟨hTV,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hs := s.quotient.isSimpleGroup
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (s.chosen.centralizer_eq_core_of_simple hs)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  have huniq := h12.source_normalizer_maximal_unique_at s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hcharL : generalizedFitting D.L = pCore 2 D.L :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo D.T
        (s.hypothesis.qtke.evenCharacteristic D.T) s.maximal.1)
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hZp : IsPGroup 2 D.V₁ := (IsElementaryAbelian.isPGroup 2 D.V).to_le hZV
  have hcharH : generalizedFitting D.H = pCore 2 D.H := by
    rw [hHfull]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le D.T
        (s.hypothesis.qtke.evenCharacteristic D.T) ⟨D.V₁,hZn,hZp,rfl⟩ hTZ))
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape s.hypothesis h12 earlier s.chosen
      s.actor s.coordinates s.equivariant hZV hZ
  exact unitary_escaping_prime_actor_of_earlier_geometry D s.actor s.coordinates s.equivariant
    hUV hZV hTZ hTU hZ hU
    ((pResidual_eq_top_iff 2 D.L).mpr
      (Chapter1.Section02.Adequate.mem_L_isPPerfect s.maximal.1))
    s.chosen.sylow_normalizes_component hcharL (s.chosen.le_sylow.trans le_sup_right)
    ((s.structural D.L h12).2.2 D.V s.chosen).2.1
    (unitary_chosen_sylow_kernel s.chosen hs hTV) hcharH hNL hfaith huniq.2 hout
    B hBV hTB hB hHfull hm s.hypothesis.qtke (h12.source_chosen_TI_at s.structural s.chosen)
    (planeCentralizers_of_source s) (maximalEscapeAction_of_source s.earlier_geometry.1)

/-- The original unitary contradiction now retains only prime-normalizer
control as a local proof obligation, besides the named earlier source inputs. -/
theorem unitary_original_false_of_prime_normalizer_control
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  obtain ⟨H,_,_,_,p,A,hp,hp3,hcard,_,hAH,hAV,hAL,hout⟩ :=
    unitary_original_escaping_prime_actor_of_source_geometry D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  exact hout (inf_le_right.trans (hodd p A hp hp3 hcard (hAH.trans inf_le_right) hAV hAL))

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
