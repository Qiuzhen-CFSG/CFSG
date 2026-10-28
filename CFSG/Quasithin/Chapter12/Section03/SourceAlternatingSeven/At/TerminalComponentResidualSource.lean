module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperNatural
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentResidualOpening

/-!
# TerminalComponentResidualSource at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentResidualSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 Section02.RecognitionSource Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem hstarOmega_centralizer_le_original_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    centralizer (hstarOmegaModule T P.H : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_le (le_conjugateSpanBy _ _)).trans
    (omega_center_centralizer_le_at S D structural)

theorem hstarOmega_centralizer_le_normalCore_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) ≤
      ((normalizer (V : Set G)).subgroupOf P.H).normalCore := by
  let := (chosen_hstar_omega_reduced S.hypothesis P.minimal).normal
  apply normal_le_normalCore.mpr
  have hnV : P.H ⊓ centralizer (hstarOmegaModule T P.H : Set G) ≤
      normalizer (V : Set G) :=
    S.hypothesis.source_point_normalizes_chosen_at structural S.chosen P.point.property
      (fun he => P.nonidentity (Subtype.ext he))
      (le_inf (inf_le_right.trans (P.hstarOmega_centralizer_le_original_at structural))
        (inf_le_left.trans P.centralizes))
  intro c hc
  apply hnV
  refine ⟨c.property,?_⟩
  intro w hw
  exact congrArg P.H.subtype (mem_centralizer_iff.mp hc
    ⟨w,hstarOmegaModule_le P.minimal.1.1.2 hw⟩ hw)

private theorem hstarOmega_centralizer_le_parabolicCore_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) ≤
      ChapterB.minimalParabolicCore (T.subtype P.minimal.1.1.2)
        (P.minimalParabolic_at structural hw) := by
  let := (chosen_hstar_omega_reduced S.hypothesis P.minimal).normal
  apply ChapterB.minimalParabolic_normal_le_core_of_residual_not_le
  intro hk
  apply P.residual_escape_at structural
  apply le_trans _ (omega_center_centralizer_le_at S D structural)
  rintro _ ⟨k,hk',rfl⟩ z hz
  have hzW : z ∈ hstarOmegaModule T P.H := le_conjugateSpanBy _ _ hz
  exact congrArg P.H.subtype (mem_centralizer_iff.mp (hk hk')
    ⟨z,hstarOmegaModule_le P.minimal.1.1.2 hzW⟩ hzW)

theorem sylow_centralizer_hstarOmega_eq_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    (T : Subgroup G) ⊓ centralizer (hstarOmegaModule T P.H : Set G) = P.H.pCoreIn 2 := by
  apply le_antisymm
  · intro t ht
    have hc : (⟨t,P.minimal.1.1.2 ht.1⟩ : P.H) ∈
        centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) := by
      intro w hw
      exact Subtype.ext (ht.2 w hw)
    have hk := P.hstarOmega_centralizer_le_parabolicCore_at structural hw hc
    have hm : (⟨t,P.minimal.1.1.2 ht.1⟩ : P.H) ∈
        ((T.subtype P.minimal.1.1.2 : Sylow 2 P.H) : Subgroup P.H) ⊓
          ChapterB.minimalParabolicCore _ (P.minimalParabolic_at structural hw) := ⟨ht.1,hk⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core] at hm
    exact mem_map_of_mem P.H.subtype hm
  · refine le_inf ?_ (chosen_hstar_core_centralizes_omega S.hypothesis P.minimal)
    have hh := pCoreIn_le_sylow P.H (T.subtype P.minimal.1.1.2)
    change P.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P.H).map P.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le P.minimal.1.1.2] at hh

theorem overcomponents_of_original_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ∃ F : P.Overcomponents, Hypothesis1223 KnownSimple.IsKnownSimple T F.Y := by
  obtain ⟨F⟩ := P.overcomponents_nonempty
    (P.residual_local_and_quasisimple_at structural modules hr hw).1
  exact ⟨F,P.residual_overgroup_hypothesis_at structural modules hr hw F.maximal
    (F.residual_le.trans F.le_maximal)⟩

theorem residualAnalysis_of_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (proper : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      Nonempty (CentralQuotient Y ≃* alternatingGroup (Fin 7)))
    (natural : P.K ∈ Chapter1.LStar G (T : Subgroup G) →
      Nonempty (Representation.BinaryConjugationSection P.K ⁅hstarOmegaModule T P.H,P.K⁆ ⊥
        (P.residualNaturalAction q)) ∨
      Nonempty (Representation.BinaryConjugationSection P.K ⁅hstarOmegaModule T P.H,P.K⁆ ⊥
        (Representation.prod (P.residualNaturalAction q) (P.residualNaturalAction q)))) :
    Nonempty P.ResidualAnalysis := by
  refine ⟨⟨(P.residual_local_and_quasisimple_at structural modules hr hw).1,q,?_,?_⟩⟩
  · intro Y hY hKY
    have h := P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY
    refine ⟨h.maximal_faithful.2,?_⟩
    by_cases he : P.K = Y
    · exact Or.inl he
    · obtain ⟨e⟩ := proper Y hY (lt_of_le_of_ne hKY he)
      obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y h).2.1
      exact Or.inr ⟨W,⟨⟨h,E,e⟩⟩⟩
  · intro hm
    simpa only [AtMostTwoNatural, P.hstarOmega_commutator_eq] using natural hm

theorem componentAnalysis_of_residual_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (proper : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      Nonempty (CentralQuotient Y ≃* alternatingGroup (Fin 7)))
    (natural : P.K ∈ Chapter1.LStar G (T : Subgroup G) →
      Nonempty (Representation.BinaryConjugationSection P.K ⁅hstarOmegaModule T P.H,P.K⁆ ⊥
        (P.residualNaturalAction q)) ∨
      Nonempty (Representation.BinaryConjugationSection P.K ⁅hstarOmegaModule T P.H,P.K⁆ ⊥
        (Representation.prod (P.residualNaturalAction q) (P.residualNaturalAction q)))) :
    Nonempty P.ComponentAnalysis := by
  obtain ⟨R⟩ := P.residualAnalysis_of_models_at structural modules hr hw q proper natural
  exact P.componentAnalysis_of_residual_at structural escape localAnalysis_at R

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

