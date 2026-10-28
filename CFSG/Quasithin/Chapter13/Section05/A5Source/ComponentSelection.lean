module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.FittingAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ResidualStructure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# Original A₅ component selection after13.5.20

The original chosen module lies in O₂(L), hence in O₂(N_G(L)). The proved
F.9.1 setup and geometry apply to every member of the original H_z family.
Under the source counterexample and the genuine normal recognition13.5.17,
13.5.18 rules out normal point residuals;13.5.19 then supplies their actual
normalizer image and core containment. Fitting centralization and a moved
C-component follow on the original starred quotient.
Source: Aschbacher–Smith13.5.18–20 and the following paragraph, pp.922–923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (h17 : ∀ J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)),
    ¬ IsMulCommutative (Source.UH J V₃) → ((residualCentralizer L V₁).subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
include d

omit [IsElementaryAbelian 2 V] in
/-- The source choice lies in the actual two-core of N_G(L). -/
theorem Context.module_le_normalizer_core : V ≤ (normalizer (L : Set G)).pCoreIn 2 :=
  d.chosen.le_componentCore.trans (pCoreIn_mono_of_normalizes L.le_normalizer le_rfl)

omit [Finite G] [IsElementaryAbelian 2 V] d in
include h17 hnot in
/-- Original13.5.18 on the original local-overgroup family. -/
theorem source13_5_18 {J : Subgroup G}
    (hJ : J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
    (hu : ¬ IsMulCommutative (Source.UH J V₃)) :
    ¬ ((residualCentralizer L V₁).subgroupOf J).Normal := by
  intro hn
  exact hnot (Or.inl ⟨rfl,h17 J hJ hu hn⟩)

include hA312 hH h17 hnot in
/-- Both original13.5.19 conclusions with their earlier geometry discharged. -/
theorem source13_5_19 :
    Source.starImage H (H ⊓ normalizer (residualCentralizer L V₁ : Set G)) =
      normalizer (Source.starImage H (residualCentralizer L V₁) : Set (Source.Hstar H)) ∧
    V ≤ (H ⊓ normalizer (residualCentralizer L V₁ : Set G)).pCoreIn 2 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  refine ⟨local_normalizer_image D hf,?_⟩
  apply local_normalizer_core D hf (normalizer (L : Set G)) d.module_le_normalizer_core
    (inf_le_right.trans ((d.seed_normalizer hA312).trans d.module_normalizer))
    ?_ ?_ ?_
  · have hc : normalizer (L : Set G) ⊓ centralizer (V₃ : Set G) ≤ centralizer (V : Set G) :=
      d.third_centralizer_local.le
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hc]
    exact bot_le
  · intro J hJ
    have hz : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := hf.normalizer_point_eq
    change J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (normalizer (V₁ : Set G)) (normalizer (L : Set G)) at hJ
    rw [hz] at hJ
    exact (source13_5_7 d hA312 hJ).f9Hypothesis
  · intro J hJ hu
    have hz : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := hf.normalizer_point_eq
    change J ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (normalizer (V₁ : Set G)) (normalizer (L : Set G)) at hJ
    rw [hz] at hJ
    exact source13_5_18 h17 hnot hJ hu

include hA312 hH hU h17 hnot in
/-- The original13.5.20 Fitting conclusion in the source counterexample. -/
theorem source13_5_20 :
    Source.starImage H V ≤
      centralizer (fittingSubgroup (Source.Hstar H) : Set (Source.Hstar H)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨himage,hcore⟩ := source13_5_19 d hA312 hH h17 hnot
  have hYV : residualCentralizer L V₁ ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans d.chosen.normalizes)
  exact source_centralizes_fitting d hA312 hH hU (residualCentralizer L V₁)
    (le_sup_left.trans hf.local_le) (isPPerfect_embedded_pResidual 2 _)
    (residual_quotient_card d hA312 hH hU) hYV himage hcore

include hA312 hH hU h17 hnot in
/-- The original moved component chosen immediately after13.5.20. -/
theorem source_component_selection :
    ∃ C : Subgroup G, C ≤ H ∧ (C.subgroupOf H).IsCComponent ∧
      IsQuasisimple (Source.starImage H C) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Source.starImage H C) ∧
      ⁅Source.starImage H C,Source.starImage H V⁆ ≠ ⊥ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact exists_component_of_fitting_centralized D hf hU
    (source13_5_20 d hA312 hH hU h17 hnot)
end CFSG.Quasithin.Chapter13.Section05.A5Source
