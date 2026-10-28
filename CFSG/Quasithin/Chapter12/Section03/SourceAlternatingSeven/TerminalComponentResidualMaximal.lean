module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualSource
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceActionRows
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer

/-!
# Maximal residual recognition and its literal moved module

Minimal parabolicity and the seven chosen-module alternatives identify a
maximal terminal residual modulo its own two-core with A₅. Every chosen
central action is the orthogonal A₅ action. This discharges the quotient
marking in the maximal branch and proves its Thompson generation.

Independently of that marking, the actual moved subgroup [Z,K] is reduced
inside H and has the same H-centralizer as the original omega-span.
Consequently its Sylow centralizer is O₂(H). Escape proves movement, and
Thompson generation gives an FF action on the entire [Z,K], without any
assumption about its number of natural summands.

The full natural-module identification and proper-overcomponent recognition
remain with qt-d-1231-terminal-component. These results supply their actual
maximal-branch inputs; they do not assert the complete 12.3.12 conclusion.
Source: Aschbacher–Smith, 12.2.7 and 12.3.12, printed pp.797–798,811.
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

/-- The actual moved subgroup lies in the original escaping H. -/
theorem moved_le_hstar : ⁅P.Z,P.K⁆ ≤ P.H := by
  apply (commutator_mono ?_ (map_subtype_le (pResidual 2 P.H))).trans
    (commutator_le_self P.H)
  intro z hz
  exact P.minimal.1.1.2 ((mem_omegaCenterIn_iff _ _).mp hz).1

private theorem intrinsic_moved_eq :
    ⁅(hstarOmegaModule T P.H).subgroupOf P.H, pResidual 2 P.H⁆ =
      (⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H := by
  apply map_injective P.H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le (hstarOmegaModule_le P.minimal.1.1.2),
    map_subgroupOf_eq_of_le P.moved_le_hstar]
  exact P.hstarOmega_commutator_eq

/-- Reducedness of the entire moved subgroup, relative to H. -/
theorem moved_reduced : IsPReduced 2 ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H) := by
  have hr := chosen_hstar_omega_reduced S.hypothesis P.minimal
  let := hr.normal
  let := hr.elementary
  rw [← P.intrinsic_moved_eq]
  exact hr.moved _

/-- Elementarity before any module-model identification. -/
theorem moved_elementary_source : IsElementaryAbelian 2 (⁅P.Z,P.K⁆ : Subgroup G) := by
  let := P.moved_reduced.elementary
  have hh := IsElementaryAbelian.map (p := 2)
    (A := (⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H) P.H.subtype
  rwa [map_subgroupOf_eq_of_le P.moved_le_hstar] at hh

/-- The moved subgroup detects precisely the original omega-span action. -/
theorem moved_centralizer_eq :
    centralizer ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H : Set P.H) =
      centralizer ((hstarOmegaModule T P.H).subgroupOf P.H : Set P.H) := by
  have hr := chosen_hstar_omega_reduced S.hypothesis P.minimal
  let := hr.normal
  let := hr.elementary
  rw [← P.intrinsic_moved_eq]
  exact hr.centralizer_moved_eq _

/-- The literal Sylow centralizer is the original two-core of H. -/
theorem sylow_centralizer_moved_eq_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    (T : Subgroup G) ⊓ centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) = P.H.pCoreIn 2 := by
  rw [← P.sylow_centralizer_hstarOmega_eq_core structural hw]
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

/-- Residual escape forces nontrivial action on its moved subgroup. -/
theorem residual_moves_moved_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ¬ P.K ≤ centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
  intro hc
  apply P.residual_escape structural
  apply le_trans _ (P.hstarOmega_centralizer_le_original structural)
  intro k hk
  have hi : (⟨k,map_subtype_le (pResidual 2 P.H) hk⟩ : P.H) ∈
      centralizer ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H : Set P.H) := by
    intro w hw
    exact Subtype.ext (hc hk w hw)
  rw [P.moved_centralizer_eq] at hi
  intro w hw
  exact congrArg P.H.subtype (hi ⟨w,hstarOmegaModule_le P.minimal.1.1.2 hw⟩ hw)

/-- Reducedness places the moved subgroup in the original Sylow subgroup. -/
theorem moved_le_sylow_source : ⁅P.Z,P.K⁆ ≤ (T : Subgroup G) := by
  have hh := map_mono (f := P.H.subtype) P.moved_reduced.le_pCore
  rw [map_subgroupOf_eq_of_le P.moved_le_hstar] at hh
  exact hh.trans (by
    have h := pCoreIn_le_sylow P.H (T.subtype P.minimal.1.1.2)
    change P.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P.H).map P.H.subtype at h
    rwa [map_subgroupOf_eq_of_le P.minimal.1.1.2] at h)

/-- Recognition of the maximal residual and all its chosen central actions. -/
theorem maximal_residual_five
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T P.K W),
        letI := E.actionCentralizer_normal
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv E.faithfulCentralAction
          (ChapterB.QuasisimpleSource.alternatingNatural 5)) := by
  have hK := P.residual_overgroup_hypothesis structural modules hr hw hm le_rfl
  have hP' (J : Subgroup G) (he : J = P.H) (hTJ : (T : Subgroup G) ≤ J) :
      ChapterB.IsMinimalParabolicOver (T.subtype hTJ) ⊤ := by
    subst J
    exact P.minimalParabolic structural hw
  have hP := hP' _ P.residual_sup_sylow le_sup_right
  have each (W : Subgroup G) (E : ChosenModule T P.K W) :=
    E.five_of_minimalParabolic hK ((structural G T P.K hK).2.2 W E).1
      hP (modules G T P.K W hK E)
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural G T P.K hK).2.1
  exact ⟨(each W E).1,fun W E => (each W E).2⟩

/-- The maximal branch of Thompson generation with its model input discharged. -/
theorem maximal_thompson_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ⁅P.K,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K := by
  obtain ⟨q⟩ := (P.maximal_residual_five structural modules hr hw hm).1
  exact P.maximal_residual_thompson q
    (P.residual_overgroup_hypothesis structural modules hr hw hm le_rfl).maximal_faithful

/-- Thompson movement follows from escape on the entire actual moved subgroup. -/
theorem maximal_thompson_moves_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G) := by
  intro hj
  apply P.residual_moves_moved_source structural
  conv_lhs => rw [← P.maximal_thompson_source structural modules hr hw hm]
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_eq_bot_iff_le_centralizer.mpr hj,commutator_bot_left]
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right P.Z P.K)).trans
        (le_centralizer_iff.mp hj))

/-- The maximal-branch FF input, without an assumed natural decomposition. -/
theorem maximal_moved_isFF_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    let := P.moved_elementary_source
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized) := by
  let := P.moved_elementary_source
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T P.H ⁅P.Z,P.K⁆
    P.minimal.1.1.2 P.moved_le_sylow_source P.moved_module_normalized
    (P.maximal_thompson_moves_source structural modules hr hw hm)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
