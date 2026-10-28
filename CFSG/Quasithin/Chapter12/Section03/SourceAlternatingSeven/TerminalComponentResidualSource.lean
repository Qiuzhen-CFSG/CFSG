module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualOpening
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperNatural
public import Theory.GroupTheory.Commutator.FixedSeedMovement

/-!
# The terminal omega-span kernel and the residual-model consumer

The normal core of N_H(V) contains C_H(V_H), using local TI in M and
H ≤ C_G(e). Minimal parabolicity and escape give C_T(V_H)=O₂(H),
with V_H=⟨Ω₁Z(T)^H⟩. The supplement H=KT fixes the seed Z, and
normalizes [Z,K], so [V_H,K]=[Z,K] on the original ambient subgroups.

The residual opening now constructs the actual point-centralizer component
and its maximal overcomponent. The conditional final assembly only retains
the A₅ quotient marking, the proper A₇ model restriction, and one or two
whole natural modules on the printed [V_H,K]. Their proofs remain with
qt-d-1231-terminal-component. It constructs the chosen overcomponent module
from Structural1222 and transports the whole action through the proved
commutator equality before applying the completed 12.3.12 branch proofs.

Source: Aschbacher–Smith, 12.2.7, pp.797–798, and 12.3.12, p.811.
The Sylow centralizer in 12.2.7(1) is C_T(V_H), as used in 12.2.18.
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

/-- Passing from the source omega-span to the literal seed leaves the K-commutator unchanged. -/
theorem hstarOmega_commutator_eq : ⁅hstarOmegaModule T P.H,P.K⁆ = ⁅P.Z,P.K⁆ := by
  have hTZ : (T : Subgroup G) ≤ centralizer (P.Z : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  have hTn : (T : Subgroup G) ≤ normalizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) (hTZ ht)),
      mem_normalizer_iff_map_conj_eq.mp (P.sylow_normalizes_residual ht)]
  have hHn : P.H ≤ normalizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
    rw [← P.residual_sup_sylow]
    exact sup_le (normalizer_commutator_ge_right _ _) hTn
  have hZH : P.Z ≤ P.H := by
    intro z hz
    exact P.minimal.1.1.2 ((mem_omegaCenterIn_iff _ _).mp hz).1
  apply le_antisymm _ (commutator_mono (le_conjugateSpanBy _ _) le_rfl)
  exact (commutator_mono le_rfl (map_subtype_le _)).trans
    (conjugateSpan_commutator_le_of_fixed_generators P.Z P.H P.K ⊥ T ⁅P.Z,P.K⁆
      hZH
      (by simpa only [sup_bot_eq] using P.residual_sup_sylow) hHn le_rfl
      (by rw [commutator_bot_right]; exact bot_le) hTZ)


/-- The actual omega-span centralizer is contained in the original normalizer. -/
theorem hstarOmega_centralizer_le_original
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    centralizer (hstarOmegaModule T P.H : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_le (le_conjugateSpanBy _ _)).trans
    (omega_center_centralizer_le S D structural)

/-- The source centralizer kernel lies in the normal core of N_H(V),
using only TI inside M and the actual point centralized by H. -/
theorem hstarOmega_centralizer_le_normalCore
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) ≤
      ((normalizer (V : Set G)).subgroupOf P.H).normalCore := by
  let := (chosen_hstar_omega_reduced S.hypothesis P.minimal).normal
  apply normal_le_normalCore.mpr
  have hnV : P.H ⊓ centralizer (hstarOmegaModule T P.H : Set G) ≤
      normalizer (V : Set G) :=
    S.hypothesis.source_point_normalizes_chosen structural S.chosen P.point.property
      (fun he => P.nonidentity (Subtype.ext he))
      (le_inf (inf_le_right.trans (P.hstarOmega_centralizer_le_original structural))
        (inf_le_left.trans P.centralizes))
  intro c hc
  apply hnV
  refine ⟨c.property,?_⟩
  intro w hw
  exact congrArg P.H.subtype (mem_centralizer_iff.mp hc
    ⟨w,hstarOmegaModule_le P.minimal.1.1.2 hw⟩ hw)

private theorem hstarOmega_centralizer_le_parabolicCore
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) ≤
      ChapterB.minimalParabolicCore (T.subtype P.minimal.1.1.2)
        (P.minimalParabolic structural hw) := by
  let := (chosen_hstar_omega_reduced S.hypothesis P.minimal).normal
  apply ChapterB.minimalParabolic_normal_le_core_of_residual_not_le
  intro hk
  apply P.residual_escape structural
  apply le_trans _ (omega_center_centralizer_le S D structural)
  rintro _ ⟨k,hk',rfl⟩ z hz
  have hzW : z ∈ hstarOmegaModule T P.H := le_conjugateSpanBy _ _ hz
  exact congrArg P.H.subtype (mem_centralizer_iff.mp (hk hk')
    ⟨z,hstarOmegaModule_le P.minimal.1.1.2 hzW⟩ hzW)

/-- The source-correct Sylow centralizer formula C_T(V_H)=O₂(H). -/
theorem sylow_centralizer_hstarOmega_eq_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    (T : Subgroup G) ⊓ centralizer (hstarOmegaModule T P.H : Set G) = P.H.pCoreIn 2 := by
  apply le_antisymm
  · intro t ht
    have hc : (⟨t,P.minimal.1.1.2 ht.1⟩ : P.H) ∈
        centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) := by
      intro w hw
      exact Subtype.ext (ht.2 w hw)
    have hk := P.hstarOmega_centralizer_le_parabolicCore structural hw hc
    have hm : (⟨t,P.minimal.1.1.2 ht.1⟩ : P.H) ∈
        ((T.subtype P.minimal.1.1.2 : Sylow 2 P.H) : Subgroup P.H) ⊓
          ChapterB.minimalParabolicCore _ (P.minimalParabolic structural hw) := ⟨ht.1,hk⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core] at hm
    exact mem_map_of_mem P.H.subtype hm
  · refine le_inf ?_ (chosen_hstar_core_centralizes_omega S.hypothesis P.minimal)
    have hh := pCoreIn_le_sylow P.H (T.subtype P.minimal.1.1.2)
    change P.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P.H).map P.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le P.minimal.1.1.2] at hh

/-- The component and maximal overcomponent needed by 12.3.12 now exist
from the original hypotheses, before either model is recognized. -/
theorem overcomponents_of_original
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ∃ F : P.Overcomponents, Hypothesis1223 KnownSimple.IsKnownSimple T F.Y := by
  obtain ⟨F⟩ := P.overcomponents_nonempty
    (P.residual_local_and_quasisimple structural modules hr hw).1
  exact ⟨F,P.residual_overgroup_hypothesis structural modules hr hw F.maximal
    (F.residual_le.trans F.le_maximal)⟩

/-- The remaining model inputs suffice for the existing residual boundary.
The natural-module assumption still concerns the printed V_H, and the
proved seed identity supplies the literal [Z,K] required by its consumer. -/
theorem residualAnalysis_of_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
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
  refine ⟨⟨(P.residual_local_and_quasisimple structural modules hr hw).1,q,?_,?_⟩⟩
  · intro Y hY hKY
    have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY
    refine ⟨h.maximal_faithful.2,?_⟩
    by_cases he : P.K = Y
    · exact Or.inl he
    · obtain ⟨e⟩ := proper Y hY (lt_of_le_of_ne hKY he)
      obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural G T Y h).2.1
      exact Or.inr ⟨W,⟨⟨h,E,e⟩⟩⟩
  · intro hm
    simpa only [AtMostTwoNatural, P.hstarOmega_commutator_eq] using natural hm

/-- Actual 12.3.12 consumer of the residual opening. The remaining three
model obligations are retained by qt-d-1231-terminal-component; this is
conditional assembly, not a source recognition theorem. -/
theorem componentAnalysis_of_residual_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
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
  obtain ⟨R⟩ := P.residualAnalysis_of_models structural modules hr hw q proper natural
  exact P.componentAnalysis_of_residual structural escape localAnalysis R

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
