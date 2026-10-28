module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualMaximal
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentResidualSource

/-!
# TerminalComponentResidualMaximal at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentResidualMaximal`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 Section02.RecognitionSource

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private theorem intrinsic_moved_eq_at :
    ⁅(hstarOmegaModule T P.H).subgroupOf P.H, pResidual 2 P.H⁆ =
      (⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H := by
  apply map_injective P.H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le (hstarOmegaModule_le P.minimal.1.1.2),
    map_subgroupOf_eq_of_le P.moved_le_hstar]
  exact P.hstarOmega_commutator_eq

theorem sylow_centralizer_moved_eq_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    (T : Subgroup G) ⊓ centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) = P.H.pCoreIn 2 := by
  rw [← P.sylow_centralizer_hstarOmega_eq_core_at structural hw]
  ext t
  constructor
  · rintro ⟨ht,hc⟩
    refine ⟨ht,?_⟩
    have hi : (⟨t,P.minimal.1.1.2 ht⟩ : P.H) ∈
        centralizer ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H : Set P.H) := by
      intro w hw
      exact Subtype.ext (hc w hw)
    rw [P.moved_centralizer_eq] at hi
    intro w hw
    exact congrArg P.H.subtype (hi ⟨w,hstarOmegaModule_le P.minimal.1.1.2 hw⟩ hw)
  · rintro ⟨ht,hc⟩
    refine ⟨ht,?_⟩
    have hi : (⟨t,P.minimal.1.1.2 ht⟩ : P.H) ∈
        centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) := by
      intro w hw
      exact Subtype.ext (hc w hw)
    rw [← P.moved_centralizer_eq] at hi
    intro w hw
    exact congrArg P.H.subtype (hi ⟨w,P.moved_le_hstar hw⟩ hw)

theorem residual_moves_moved_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ¬ P.K ≤ centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
  intro hc
  apply P.residual_escape_at structural
  apply le_trans _ (P.hstarOmega_centralizer_le_original_at structural)
  intro k hk
  have hi : (⟨k,map_subtype_le (pResidual 2 P.H) hk⟩ : P.H) ∈
      centralizer ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H : Set P.H) := by
    intro w hw
    exact Subtype.ext (hc hk w hw)
  rw [P.moved_centralizer_eq] at hi
  intro w hw
  exact congrArg P.H.subtype (hi ⟨w,hstarOmegaModule_le P.minimal.1.1.2 hw⟩ hw)

theorem maximal_residual_five_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T P.K W),
        letI := E.actionCentralizer_normal
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv E.faithfulCentralAction
          (ChapterB.QuasisimpleSource.alternatingNatural 5)) := by
  have hK := P.residual_overgroup_hypothesis_at structural modules hr hw hm le_rfl
  have hP' (J : Subgroup G) (he : J = P.H) (hTJ : (T : Subgroup G) ≤ J) :
      ChapterB.IsMinimalParabolicOver (T.subtype hTJ) ⊤ := by
    subst J
    exact P.minimalParabolic_at structural hw
  have hP := hP' _ P.residual_sup_sylow le_sup_right
  have each (W : Subgroup G) (E : ChosenModule T P.K W) :=
    E.five_of_minimalParabolic hK ((structural P.K hK).2.2 W E).1
      hP (modules P.K W hK E)
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural P.K hK).2.1
  exact ⟨(each W E).1,fun W E => (each W E).2⟩

theorem maximal_thompson_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ⁅P.K,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K := by
  obtain ⟨q⟩ := (P.maximal_residual_five_at structural modules hr hw hm).1
  exact P.maximal_residual_thompson_at q
    (P.residual_overgroup_hypothesis_at structural modules hr hw hm le_rfl).maximal_faithful

theorem maximal_thompson_moves_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
  intro hj
  apply P.residual_moves_moved_source_at structural
  conv_lhs => rw [← P.maximal_thompson_source_at structural modules hr hw hm]
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_eq_bot_iff_le_centralizer.mpr hj,commutator_bot_left]
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right P.Z P.K)).trans
        (le_centralizer_iff.mp hj))

theorem maximal_moved_isFF_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    let := P.moved_elementary_source
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized) := by
  let := P.moved_elementary_source
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T P.H ⁅P.Z,P.K⁆
    P.minimal.1.1.2 P.moved_le_sylow_source P.moved_module_normalized
    (P.maximal_thompson_moves_source_at structural modules hr hw hm)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

