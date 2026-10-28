module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Irreducible
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import Theory.Representation.BinaryOffender.Replacement

/-!
# The full B.4.2 implication and its strict-ratio consequence

The source input quantifies over finite faithful binary actions with
quasisimple generalized Fitting subgroup acting irreducibly. Its conclusion
is the full eleven-case action list, including exact ratios and offender
clauses. A strong offender rules out precisely the ratio-one alternatives.
The remaining generalized Fitting models are SL₃, Sp₄, A₆, SL₄(2) and
SL₅(2); the S₈ case uses its actual marked A₈ subgroup and the checked
A₈–SL₄(2) comparison.

`StrongPSLTwoAction` describes the still-needed irreducible reduction. It
is not asserted to exist for an arbitrary two-component action here.

Source: Aschbacher–Smith, B.4.2, printed pp.86–87, used in 13.8.16(1), p.952.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

universe u v w

/-- The complete universal B.4.2 implication, with no specialized exclusion
or irreducible-reduction hypothesis hidden in its conclusion. -/
def FullB42 (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (U : Type v)
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) E U) (A : Subgroup E),
    B42Hypotheses 𝒦 σ A →
      IrreducibleActionCase σ (Theory.GroupTheory.generalizedFitting E) (offenderSubgroup σ)

/-- Only the component models in B.4.2 whose listed ratios are below one.
This is a consequence extracted from the full list, not a source premise. -/
def StrictRatioModel (L : Type*) [Group L] : Prop :=
  (∃ F : BinaryField, Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ∨
  (∃ F : BinaryField, 1 < F.degree ∧
    Nonempty (L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)) ∨
  Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

/-- Exact ratios eliminate every ratio-one branch without forgetting any
of the source hypotheses in the full classification implication. -/
theorem strictRatioModel_of_actionCase
    {E : Type u} [Group E] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) E U) {L H : Subgroup E}
    (hc : IrreducibleActionCase σ L H) (hq : quadraticRatio σ < 1) :
    StrictRatioModel L := by
  cases hc with
  | linearTwo _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | linearThree F _ e _ => exact Or.inl ⟨F, ⟨e.groupEquiv⟩⟩
  | symplectic F hn _ e _ => exact Or.inr (Or.inl ⟨F, hn, ⟨e.groupEquiv⟩⟩)
  | symplecticTwo e _ =>
    exact Or.inr (Or.inr (Or.inl ⟨e.subgroupEquiv.trans binarySymplecticDerivedEquiv⟩))
  | g2 _ _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | g2Two _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | symmetric _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | alternatingSix _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | alternatingSeven _ _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | tripleSix _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.groupEquiv⟩)))
  | orthogonalSix _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | symmetricEight _ e _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.subgroupEquiv.trans alternatingEightLinearEquiv⟩)))
  | exteriorFive _ _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim

/-- B.4.2 is used only after all its genuine irreducible-action hypotheses
have been established. Strong replacement provides the best offender. -/
theorem strictRatioModel_of_strong
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    {E : Type u} [Group E] [Finite E]
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) E U) (h : B4Hypotheses 𝒦 σ)
    (hs : IsStrongFFModule σ) : StrictRatioModel (Theory.GroupTheory.generalizedFitting E) := by
  have hf : IsFFModule σ := by
    obtain ⟨A, hA, hlt⟩ := hs
    exact ⟨A, hA, hlt.le⟩
  obtain ⟨A, hA⟩ := h.exists_bestOffender hf
  exact strictRatioModel_of_actionCase σ (hB42 E U σ A hA)
    ((isStrongFFModule_iff_quadraticRatio_lt_one σ).mp hs)

/-- The exact missing reduction target: a faithful strong action to which
B.4.2 actually applies, with a multiplicative equivalence identifying its
entire generalized Fitting subgroup with the original projective factor. -/
structure StrongPSLTwoAction (𝒦 : GroupClass.{u}) (F : Type w) [Field F] where
  Actor : Type u
  [actor_group : Group Actor]
  [actor_finite : Finite Actor]
  Space : Type v
  [space_add : AddCommGroup Space]
  [space_module : Module (ZMod 2) Space]
  [space_finite : Finite Space]
  representation : Representation (ZMod 2) Actor Space
  hypotheses : B4Hypotheses 𝒦 representation
  strong : IsStrongFFModule representation
  componentEquiv : Theory.GroupTheory.generalizedFitting Actor ≃* PSL(2,F)

attribute [instance] StrongPSLTwoAction.actor_group StrongPSLTwoAction.actor_finite
  StrongPSLTwoAction.space_add StrongPSLTwoAction.space_module StrongPSLTwoAction.space_finite

/-- The reduced action forces the original projective factor into one of
the strict-ratio models. A concrete model comparison must exclude this. -/
theorem StrongPSLTwoAction.strictRatioModel
    {𝒦 : GroupClass.{u}} {F : Type w} [Field F]
    (a : StrongPSLTwoAction.{u,v,w} 𝒦 F) (hB42 : FullB42.{u,v} 𝒦) :
    StrictRatioModel PSL(2,F) := by
  have hm := strictRatioModel_of_strong hB42 a.representation a.hypotheses a.strong
  unfold StrictRatioModel at hm
  rcases hm with ⟨B, ⟨e⟩⟩ | ⟨B, hn, ⟨e⟩⟩ | he | he | he
  · exact Or.inl ⟨B, ⟨a.componentEquiv.symm.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨B, hn, ⟨a.componentEquiv.symm.trans e⟩⟩)
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (Or.inl ⟨a.componentEquiv.symm.trans e⟩))
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a.componentEquiv.symm.trans e⟩)))
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a.componentEquiv.symm.trans e⟩)))

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
