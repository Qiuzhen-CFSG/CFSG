module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CompletePlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly.Elementary
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CensusApplication
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.SourceAssembly

/-!
# Complete native four-local cover and arbitrary-radical restriction

Every pure subgroup containing a conjugate native pair now has its entire
maximal two-local normalizer placed in max2. Orders two and four are handled
by the proved line and census endpoints. The exhaustive all-row-two census
and canonical F-intersection geometry place larger pure groups containing no
native pair. Together with the mixed and nonsingular reductions, these give
the four literal locals, each of which is proved two-local.
Choosing a maximal two-local overgroup gives full elementary-normalizer
coverage and the original arbitrary-radical restriction and core identities.

The conditional assembly APIs are retained. The final unconditional theorems
discharge their all-row-two premise using the completed source branch, with
no additional geometry, symmetry or coverage assumption.
Source: Kleidman--Wilson (1988), Section 2, pp.488--493, and p.509.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.CompleteCover
open ElementaryNormalizerCover LargeCenterRadicals
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open PureTwoA.NativePair PureTwoA.NativeExtensions
attribute [local irreducible] modelGroup matrixA matrixB
set_option backward.isDefEq.respectTransparency true

/-- The independently owned source branch, retained as the input specification
for the conditional assembly APIs. `allRowTwoPlacement` proves it below. -/
abbrev AllRowTwoPlacement : Prop :=
  ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], 4 < Nat.card X →
    (∀ x ∈ X, x ≠ 1 → IsConj a x) →
    (¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) →
    IsMaximalTwoLocal (normalizer (X : Set Model)) →
    NativeLocalPlacement (normalizer (X : Set Model))

/-- Conditional pure assembly from the independent no-native-pair branch. -/
theorem pure_normalizer_placement (hallrow : AllRowTwoPlacement)
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    NativeLocalPlacement (normalizer (X : Set Model)) := by
  by_cases hpair : ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X
  · obtain ⟨g,hg⟩ := hpair
    obtain ⟨k,hk⟩ := marked_extension_maximal X g hg hpure hmax
    exact ⟨g*k,Or.inr (Or.inl hk)⟩
  by_cases htwo : Nat.card X = 2
  · obtain ⟨g,hg⟩ := PureTwoA.order_two_normalizer X htwo hpure
    exact ⟨g,Or.inr (Or.inl hg)⟩
  by_cases hfour : Nat.card X = 4
  · obtain ⟨g,_,_,hn⟩ := maximal_pure_four_group_seven X hfour hpure hmax
    rw [hn] at hmax
    exact (row_seven_not_maximal
      ((Theory.Quasithin.isMaximalTwoLocal_map_iff (MulAut.conj g) _).mp hmax)).elim
  apply hallrow X _ hpure hpair hmax
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 X).exists_card_eq
  have hnlarge : 3 ≤ n := by
    by_contra h
    have hnsmall : n < 3 := by omega
    interval_cases n
    · exact hne (X.eq_bot_of_card_eq (by simpa using hn))
    · exact htwo (by simpa using hn)
    · exact hfour (by simpa using hn)
  rw [hn]
  exact lt_of_lt_of_le (by decide : 4 < 2^3) (pow_le_pow_right' (by decide : 1 ≤ 2) hnlarge)

/-- Full maximal-two-local coverage from the all-row-two source branch. -/
theorem maximalTwoLocalCover_of_allRowTwo (hallrow : AllRowTwoPlacement) :
    MaximalTwoLocalCover :=
  maximalTwoLocalCover_of_pure_first (pure_normalizer_placement hallrow)

/-- The four actual embedded native locals, with no group-family tags. -/
@[expose] def nativeLocal : Fin 4 → Subgroup Model :=
  ![max1,sourceSubgroup,LinearFive.fullNormalizer,SymmetricLinear.max4Subgroup]

theorem nativeLocal_isTwoLocal (i : Fin 4) : IsTwoLocal (nativeLocal i) := by
  fin_cases i
  · exact embedded_localKernel_isTwoLocal
  · exact PureTwoA.sourceSubgroup_isTwoLocal
  · change IsTwoLocal LinearFive.fullNormalizer
    rw [← LinearFive.M_F_eq_fullNormalizer]
    exact nativeF_generated_isTwoLocal
  · exact max4_isTwoLocal

/-- The exact fixed finite family covers each maximal TWO-local. -/
theorem maximal_twoLocal_cover (hallrow : AllRowTwoPlacement)
    (M : Subgroup Model) (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 4) (g : Model), M = (nativeLocal i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,h | h | h | h⟩ := maximalTwoLocalCover_of_allRowTwo hallrow M hM
  · exact ⟨0,g,h⟩
  · exact ⟨1,g,h⟩
  · exact ⟨2,g,h⟩
  · exact ⟨3,g,h⟩

/-- The WHOLE normalizer of every nontrivial elementary subgroup is covered;
no ambient Sylow, odd-index or normality-in-a-fixed-Sylow premise is used. -/
theorem elementary_normalizer_cover (hallrow : AllRowTwoPlacement)
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hne : X ≠ ⊥) :
    ∃ (i : Fin 4) (g : Model), normalizer (X : Set Model) ≤
      (nativeLocal i).map (MulAut.conj g).toMonoidHom := by
  have hl : IsTwoLocal (normalizer (X : Set Model)) :=
    ⟨X,hne,IsElementaryAbelian.isPGroup 2 X,rfl⟩
  obtain ⟨M,hNM,hM⟩ := hl.exists_le_maximal
  obtain ⟨i,g,hg⟩ := maximal_twoLocal_cover hallrow M hM
  exact ⟨i,g,hg ▸ hNM⟩

/-- The original arbitrary radical restricts to an actual native local
conjugate with its WHOLE normalizer and both literal two-core identities.
No center-size bound is imposed. -/
theorem arbitrary_radical_cover (hallrow : AllRowTwoPlacement)
    (P : Subgroup Model) (hP : P.IsPRadical 2) :
    ∃ (i : Fin 4) (g : Model), let L := (nativeLocal i).map (MulAut.conj g).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  have hl : IsTwoLocal (normalizer (P : Set Model)) := ⟨P,hP.1,hP.isPGroup,rfl⟩
  obtain ⟨M,hNM,hM⟩ := hl.exists_le_maximal
  obtain ⟨i,g,hg⟩ := maximal_twoLocal_cover hallrow M hM
  let L := (nativeLocal i).map (MulAut.conj g).toMonoidHom
  have hNL : normalizer (P : Set Model) ≤ L := hNM.trans hg.le
  have hPL := P.le_normalizer.trans hNL
  have hNN := hNL.trans L.le_normalizer
  have hc := hP.normalizer_core_subgroupOf L hPL hNN
  refine ⟨i,g,(nativeLocal_isTwoLocal i).map_equiv (MulAut.conj g),hNL,hPL,?_,
    hP.subgroupOf_of_normalizer_normalizes L hPL hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPL,map_subgroupOf_eq_of_le hNL]
  · rw [hc,map_subgroupOf_eq_of_le hPL]

/-- The complete census and invariant F-intersection geometry discharge the
exact no-native-pair premise of the retained conditional assembly. -/
theorem allRowTwoPlacement : AllRowTwoPlacement :=
  AllRowTwo.NamedLocalGeometry.all_row_two_nativeLocalPlacement

/-- Every pure-first elementary subgroup with maximal two-local normalizer
has its whole normalizer in one of the four named native conjugacy classes. -/
theorem pure_normalizer_placement_unconditional
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    NativeLocalPlacement (normalizer (X : Set Model)) :=
  pure_normalizer_placement allRowTwoPlacement X hne hpure hmax

/-- The native four-local cover required by the original large-center and
residual consumers. Every source-geometry premise is discharged. -/
theorem maximalTwoLocalCover : MaximalTwoLocalCover :=
  maximalTwoLocalCover_of_allRowTwo allRowTwoPlacement

/-- Unconditional coverage of every maximal TWO-local by the fixed family of
four actual embedded subgroups, retaining its ambient conjugator. -/
theorem maximal_twoLocal_cover_unconditional
    (M : Subgroup Model) (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 4) (g : Model), M = (nativeLocal i).map (MulAut.conj g).toMonoidHom :=
  maximal_twoLocal_cover allRowTwoPlacement M hM

/-- Unconditional coverage of the whole normalizer of any nontrivial
elementary two-subgroup, without an ambient Sylow or maximality premise. -/
theorem elementary_normalizer_cover_unconditional
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hne : X ≠ ⊥) :
    ∃ (i : Fin 4) (g : Model), normalizer (X : Set Model) ≤
      (nativeLocal i).map (MulAut.conj g).toMonoidHom :=
  elementary_normalizer_cover allRowTwoPlacement X hne

/-- The original arbitrary-radical consumer with all source premises
discharged. The same conjugate local contains P and its whole normalizer;
the relative normalizer, radicality and both two-core identities use the
literal inclusion map. There is no center-size restriction. -/
theorem arbitrary_radical_cover_unconditional
    (P : Subgroup Model) (hP : P.IsPRadical 2) :
    ∃ (i : Fin 4) (g : Model), let L := (nativeLocal i).map (MulAut.conj g).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P :=
  arbitrary_radical_cover allRowTwoPlacement P hP

end Janko4.LocalStructure.PureFirstNormalizers.CompleteCover
