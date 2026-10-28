module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

/-!
# Native exclusion of strong external PSL₂ offenders

The corrected B.4.2 source classifier forces every strict-ratio component
to contain an element of order four. Characteristic-two PSL₂ has no such
element. The faithful irreducible reduction and the proved B.1.5(3)
stabilization theorem extend this obstruction to arbitrary minimal strong
offenders generating the normal component. A normal fixed-free cubic then
excludes the only remaining offenders, those moving the cubic subgroup.

This discharges the classification and invariance premises of the external
L₂ strong-offender argument. It never instantiates the legacy B.4.2
vector-line interface. The subsequent source module applies the result to
the literal original quotient and its invariant sections.
Source: Aschbacher–Smith, B.1.5(3), B.4.2, and 13.8.20(a), pp.69–70,86,954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NativeSource
open Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open NoStrongMoved
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
universe u v w

private def field (F : ChapterB.QuasisimpleSource.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

private theorem strict_model {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {L J : Subgroup D}
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L J)
    (hq : quadraticRatio ρ < 1) : StrictRatioModel L := by
  cases h with
  | linearTwo _ _ _ _ hr => exact (lt_irrefl _ (hr ▸ hq)).elim
  | linearThree F _ e _ => exact Or.inl ⟨field F, ⟨e.groupEquiv⟩⟩
  | symplectic F hn _ e _ => exact Or.inr (Or.inl ⟨field F, hn, ⟨e.groupEquiv⟩⟩)
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

/-- Corrected B.4.2 excludes strong FF actions whose generalized Fitting
subgroup is a characteristic-two PSL₂, without a universal classification input. -/
theorem not_strong_irreducible {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (e : generalizedFitting D ≃* PSL(2,F)) : ¬ IsStrongFFModule ρ := by
  intro hs
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hff : IsFFModule ρ := by
    obtain ⟨A,hA,hr⟩ := hs
    exact ⟨A,hA,hr.le⟩
  obtain ⟨A,hA⟩ := h.exists_bestOffender hff
  have hm := strict_model ρ
    (ChapterB.SourceClassification.actionCase_of_bestOffender h.sqtk rfl h.quasisimple
      h.faithful h.irreducible hA.bestOffender)
    ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs)
  obtain ⟨g,hg⟩ := hm.exists_order_four
  exact psl_order_ne_four (e g) ((e.orderOf_eq g).trans hg)

/-- The actual B.1.5(3) theorem supplies the complete Irr⁺ invariance input. -/
theorem irr_invariance : FullIrrInvariance.{u,v} := by
  intro D _ _ V _ _ _ ρ hf A X hA _ hr hc hchief I hI
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  exact ChapterB.source_lemma_B_1_5_3 ρ hf hA hr hc hchief hI

/-- Faithful PSL₂ strong actions are impossible after the actual irreducible reduction. -/
theorem preaction_impossible_of_source {F : Type w} [Field F] [Finite F] [CharP F 2]
    (a : Preaction.{u,v,w} KnownSimple.IsKnownSimple F) : False := by
  obtain ⟨b⟩ := a.action_of_stabilization (by
    intro A hA I hI
    obtain ⟨hr,hc,hcomm⟩ := a.stabilization_hypotheses hA.1.1
    exact ChapterB.source_lemma_B_1_5_3 a.representation a.faithful hA hr hcomm hc hI)
  exact not_strong_irreducible b.representation b.hypotheses b.componentEquiv b.strong

/-- Strong offenders cannot generate a normal PSL₂ component by commutation.
The generated actor may have a nontrivial two-core; its faithful irreducible
reduction is constructed before applying the native classification. -/
theorem not_strong_of_component_commutator
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hS : IsSQTK KnownSimple.IsKnownSimple D)
    (L A : Subgroup D) [L.Normal] [IsQuasisimple L]
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (e : L ≃* PSL(2,F)) (hc : ⁅L,A⁆ = L)
    (hA : IsMinimalBestOffender ρ A) : ¬ IsStrongOffender ρ A := by
  intro hs
  let E := L ⊔ A
  let L₀ := L.subgroupOf E
  let A₀ := A.subgroupOf E
  let : L₀.Normal := inferInstance
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ E from le_sup_left)).symm
  have hc₀ : ⁅L₀,A₀⁆ = L₀ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(L.subgroupOf E).map E.subtype, (A.subgroupOf E).map E.subtype⁆ =
      (L.subgroupOf E).map E.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right),hc]
  have hg : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf E).map E.subtype ⊔ (A.subgroupOf E).map E.subtype =
      (⊤ : Subgroup E).map E.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right)]
    exact E.range_subtype.symm.trans E.subtype.range_eq_map
  exact preaction_impossible_of_source
    (preaction_of_generated (ρ.comp E.subtype) (hf.comp E.subtype_injective)
      (hS.subgroup E) L₀ A₀ ((subgroupOfEquivOfLe le_sup_left).trans e)
      hc₀ hg (minimal_subgroupOf ρ hA le_sup_right)
      (strongOffender_subgroupOf ρ hs le_sup_right))

/-- A normal fixed-free cubic rules out the remaining strong-offender branch.
Both irreducible recognition and Irr⁺ invariance are discharged. -/
theorem no_strong_cubic {D : Type u} [Group D] [Finite D]
    (K X : Subgroup D) [K.Normal] [IsQuasisimple K] [X.Normal]
    {F : Type w} [Field F] [Finite F] [CharP F 2] (e : K ≃* PSL(2,F))
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hg : subspaceCommutator ρ ⊤ X = ⊤) : ¬ IsStrongFFModule ρ := by
  rintro ⟨B,hB⟩
  obtain ⟨A,_,hA,hq,hs⟩ := hB.exists_quadratic_minimalBestOffender ρ
  by_cases hAX : A ≤ centralizer (X : Set D)
  · exact not_strong_of_component_commutator ρ hf hS K A e
      (component_commutator_of_centralizes_cubic K X hx hc hA.1.1 hAX) hA hs
  · have hr := (normalThree_quadratic_rank_fixedCodim ρ hf X inferInstance hx hg A hA.1.1 hq hAX).1
    have hp := fixedCodim_pos_of_faithful ρ hf hA.1.1.1
    have ht := hs.2
    omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NativeSource
