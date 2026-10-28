module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NormalSupplementModels
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRestrictionsNormalization
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalPreparation
public import Theory.GroupTheory.NormalizerActionFixer

/-!
# H-star residual model restrictions

The source residual in a nonsolvable H-star subgroup is an actual normal
Sylow supplement after passing to H itself. The literal quotient by its own
two-core therefore inherits the E.2.2 minimal-parabolic exclusions. The
same transport is used for the faithful centralizer action, whose kernel is
relative to the original L and is kept distinct from O₂(L).

The final 12.2.7 assembly still supplies the proper overcomponent and model
identifications. This module records the exact source restrictions already
discharged for the equal-component branch and preserves all seven original
module interfaces.

Source: Aschbacher–Smith, 12.2.7, pp.797–798, and E.2.2, pp.215–216.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem join_supplement (L : Subgroup G) (T : Sylow 2 G) :
    L.subgroupOf (L ⊔ (T : Subgroup G)) ⊔
      ((T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) :
        Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) = ⊤ := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left]
  change L ⊔ ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map _ = _
  rw [map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

theorem ChosenModule.not_binary_linear_of_minimalParabolic
    (D : ChosenModule T L V)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rintro ⟨e⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  exact ChapterB.normal_supplement_twoCore_not_binary_linear _ K
    (join_supplement L T) hP hn
    ⟨(QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e⟩

theorem ChosenModule.not_binary_g2_of_minimalParabolic
    (D : ChosenModule T L V)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  exact ChapterB.normal_supplement_twoCore_not_binary_g2 _ K
    (join_supplement L T) hP
    ⟨(QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e⟩

theorem ChosenModule.not_alternating_of_minimalParabolic
    (D : ChosenModule T L V) (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    {n : ℕ} (hn : n = 7 ∨ n = 8) :
    letI := D.actionCentralizer_normal
    ¬ Nonempty ((L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃*
      alternatingGroup (Fin n)) := by
  let := D.actionCentralizer_normal
  rintro ⟨e⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let eK : L ≃* K := (subgroupOfEquivOfLe le_sup_left).symm
  apply ChapterB.normal_supplement_action_quotient_not_alternating _ K
    (join_supplement L T) eK (RecognitionSource.chosenJoinConjugation D hT)
    ((centralizer (V : Set G)).subgroupOf L) _ hn e hP
  change (V.normalizerMonoidHom.comp (inclusion D.normalizes)).ker = _
  exact normalizer_action_ker_comap V L D.normalizes

/-- The surviving literal module rows when the chosen component together
with T is minimal parabolic. This is an intermediate sieve, not 12.2.7. -/
def MinimalParabolicChosenRows (D : ChosenModule T L V) : Prop :=
  Nonempty (ActionEquiv D.quotientAction (specialLinearNatural (k := ZMod 2) 3)) ∨
  (Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    Module.finrank (ZMod 2) D.space = 4 ∧ IsIndecomposable D.quotientAction) ∨
  (∃ n : ℕ, (n = 5 ∨ n = 6) ∧ letI := D.actionCentralizer_normal
    Nonempty (ActionEquiv D.faithfulCentralAction (alternatingNatural n))) ∨
  (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    Module.finrank (ZMod 2) D.space = 6 ∧ Function.Injective D.quotientAction ∧
    IsIrreducible D.quotientAction)

theorem ChosenModule.minimalParabolic_rows
    (D : ChosenModule T L V) (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    (rows : ModuleAlternatives1222 D) : MinimalParabolicChosenRows D := by
  let := D.actionCentralizer_normal
  cases rows with
  | linear n hn e =>
    rcases hn with rfl | hn
    · exact Or.inl ⟨e⟩
    · exact (D.not_binary_linear_of_minimalParabolic hP hn ⟨e.groupEquiv⟩).elim
  | linearThreeExtension e hd hi => exact Or.inr (Or.inl ⟨⟨e⟩,hd,hi⟩)
  | linearFiveExterior e _ _ =>
    exact (D.not_binary_linear_of_minimalParabolic hP (Or.inr rfl) ⟨e⟩).elim
  | alternating n hlo hhi e =>
    have hn : n = 5 ∨ n = 6 := by
      by_contra hh
      have hn : n = 7 ∨ n = 8 := by omega
      exact D.not_alternating_of_minimalParabolic hT hP hn ⟨e.groupEquiv⟩
    exact Or.inr (Or.inr (Or.inl ⟨n,hn,⟨e⟩⟩))
  | alternatingSevenFour e _ =>
    exact (D.not_alternating_of_minimalParabolic hT hP (Or.inl rfl) ⟨e⟩).elim
  | g2 e => exact (D.not_binary_g2_of_minimalParabolic hP ⟨e.groupEquiv⟩).elim
  | tripleSix e hd hf hi => exact Or.inr (Or.inr (Or.inr ⟨⟨e⟩,hd,hf,hi⟩))

namespace RecognitionSource
open ChapterI.Section06To08
variable {H X Y W : Subgroup G}

/-- These model quotients are excluded for the original intrinsic O²(H),
without assuming the remaining A₅ identification or module restrictions. -/
theorem chosen_hstar_residual_model_exclusions_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (∀ n : ℕ, n = 4 ∨ n = 5 →
      ¬ Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∧
    (∀ n : ℕ, n = 7 ∨ n = 8 →
      ¬ Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        alternatingGroup (Fin n))) ∧
    ¬ Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
  let S := T.subtype hH.1.1.2
  have hP := chosen_hstar_minimalParabolic_at h D structural hTI hH
  have hgen := pResidual_sup_sylow_eq_top S
  exact ⟨fun _ hn => ChapterB.normal_supplement_twoCore_not_binary_linear
      S (pResidual 2 H) hgen hP hn,
    fun _ hn => ChapterB.normal_supplement_twoCore_not_alternating
      S (pResidual 2 H) hgen hP hn,
    ChapterB.normal_supplement_twoCore_not_binary_g2 S (pResidual 2 H) hgen hP⟩

/-- Application to the original H-star group when its generating component
is already its faithful maximal overcomponent. All action quotients remain literal. -/
theorem HStarGeneratingComponent.module_rows_of_eq_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) (he : X = Y)
    (E : ChosenModule T Y W) : MinimalParabolicChosenRows E := by
  have hgen : Y ⊔ (T : Subgroup G) = H := he ▸ C.generates
  subst H
  exact E.minimalParabolic_rows ((structural Y hY).2.2 W E).1
    (chosen_hstar_minimalParabolic_at h D structural hTI hH) (modules Y W hY E)

/-- The guarded source construction now returns either proper containment
in its faithful maximal overcomponent or the surviving literal module rows.
The SL₃, small alternating, triple-six and proper-containment analysis remains
with qt-d-12213-hstar-natural; no source conclusion is hidden in this split. -/
theorem chosen_hstar_residual_overcomponent_rows_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      (X < Y ∨ ∀ (W : Subgroup G) (E : ChosenModule T Y W),
        MinimalParabolicChosenRows E) := by
  obtain ⟨X,Y,C,hres,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  refine ⟨X,Y,C,hres,hXY,hY,?_⟩
  by_cases he : X = Y
  · exact Or.inr fun _ E => C.module_rows_of_eq_at
      h D structural modules hTI hH hY he E
  · exact Or.inl (lt_of_le_of_ne hXY he)

end RecognitionSource
end CFSG.Quasithin.Chapter12.Section02
