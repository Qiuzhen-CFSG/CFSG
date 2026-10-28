module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.FieldFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstReeModels
public import Theory.SpecificGroups.Triality.BinaryCenter
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.SourceFF

/-!
# The characteristic-two Lie rows of the component comparison

The actual central quotients exclude Ree and both triality parameters.
For the remaining rows, centerlessness identifies the symplectic and G₂
quotients with the literal module image. In the linear row the complete
B.5.1 reduction supplies an irreducible test action on the same component;
SL₃ recognition recovers the whole covering group at the original field.
Thus no central covering kernel is silently discarded.

Source: Aschbacher--Smith 11.4.2, printed p.777, using B.4.2 and B.5.1.
The chosen-flag application is assembled in Lie.lean. The proper-overcomponent
and Hall/Cartan arguments remain with the component-comparison owner.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open Chapter1.Section02.LocalModels LocalGeometry.Components
universe u v

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨a,ha⟩).property)

private def quotientEquivOfCenterless {A : Type*} [Group A]
    (hz : center A = ⊥) : (A ⧸ center A) ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

/-- The full characteristic-two list loses Ree and both triality rows
once the actual central quotient satisfies the proved FF restrictions. -/
theorem lie_rankTwo_quotient {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    {n : ℕ} (hn : 0 < n) (h : CentralQuotientRestrictions (A ⧸ center A))
    (hm : LieOvergroup A n) :
    (Source.IsSL A 3 (2 ^ n) ∨ ClassicalGroup.IsPSL A 3 (2 ^ n)) ∨
      Source.IsSp A 2 (2 ^ n) ∨ ClassificationModels.IsG2At A (2 ^ n) := by
  cases hm with
  | sl3 hm => exact .inl (.inl hm)
  | psl3 hm => exact .inl (.inr hm)
  | sp4 hm => exact .inr (.inl hm)
  | g2 hm => exact .inr (.inr hm)
  | ree m hm _ he =>
    obtain ⟨d,⟨e⟩⟩ := he
    let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    have hz := ExceptionalActors.ree_center_eq_bot_of_perfect hm d
    exact (h.not_ree m (by omega)
      ⟨((quotientEquivOfCenterless (center_bot_transport e hz)).trans e).trans d.modelEquiv⟩).elim
  | triality he =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A n hn).mp he
    have hz := center_bot_transport e (Triality.Standard.binaryCarrier_center_eq_bot n hn)
    exact (h.not_triality n hn (he.of_mulEquiv (quotientEquivOfCenterless hz))).elim
  | trialityCube m hm _ he =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A m (by omega)).mp he
    have hz := center_bot_transport e (Triality.Standard.binaryCarrier_center_eq_bot m (by omega))
    exact (h.not_triality m (by omega) (he.of_mulEquiv (quotientEquivOfCenterless hz))).elim

private theorem linearThree_of_irreducible
    {Q : Type u} [Group Q] [Finite Q] {W : Type v} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hfit : K = generalizedFitting Q)
    (hK : IsQuasisimple K) (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp K.subtype)) (hff : IsFFModule ρ)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n)) :
    Source.IsSL K 3 (2 ^ n) := by
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  obtain ⟨F,hF,⟨e⟩,_⟩ := ChapterK.Linear.SourceFF.source_of_bestOffender
    ρ hsq hfit hK hf hi n hn hm A hA
  exact ⟨F.Carrier,inferInstance,inferInstance,hF ▸ F.card_eq,⟨e.groupEquiv⟩⟩

/-- The central PSL₃ quotient of any full B.5.1 row determines the whole
SL₃ component, retaining the original field even for reducible actions. -/
theorem linearThree_of_source
    {Q : Type u} [Group Q] [Finite Q] {W : Type v} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n)) :
    Source.IsSL K 3 (2 ^ n) := by
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact linearThree_of_irreducible hsq c.fitting_eq hK hf hi hff hn hm

private theorem linearThree_central_quotient {A : Type*} [Group A] [IsQuasisimple A]
    {q : ℕ} (hm : Source.IsSL A 3 q ∨ ClassicalGroup.IsPSL A 3 q) :
    ClassicalGroup.IsPSL (A ⧸ center A) 3 q := by
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F) := e.injective.nontrivial
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective).trans
        (quotientEquivOfCenterless (Group.IsPerfect.center_quotient_center_eq_bot _))⟩⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The Lie branch of 11.1.1 gives the three precise rank-two action images
of 11.4.2. The original quotient map and field parameter are preserved. -/
theorem rankTwo_image_of_lie
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E))
    (hm : LieOvergroup (E.Kz ⧸ pCore 2 E.Kz) E.input.field.degree) : RankTwoModel E := by
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  have hn := E.input.nonbinary
  rcases lie_rankTwo_quotient (by omega : 0 < E.input.field.degree)
    (centralQuotientRestrictions E h hf hne hstar hcent hff) hm with hl | hs | hg
  · obtain ⟨hK,⟨d⟩⟩ := source_classification E h hf hne hstar hcent hff
    let : IsQuasisimple (offenderComponent E) :=
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hK).symm
    have hq := (linearThree_central_quotient hl).of_mulEquiv
      (offenderCentralQuotientEquiv E h hK)
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := linearThree_of_source d (offenderGroup_sqtk E h)
      inferInstance (offenderAction_ff E hff) (by omega) hq
    exact Or.inl ⟨F,inferInstance,inferInstance,hF,
      ⟨(subgroupOfEquivOfLe hK).symm.trans e⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hs
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hz := center_bot_transport e
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot (F := F))
    exact Or.inr (Or.inl ⟨F,inferInstance,inferInstance,hF,
      ⟨(componentQuotientImageEquiv E h hz).symm.trans e⟩⟩)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hg
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
    have hz := center_bot_transport e
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge)
    exact Or.inr (Or.inr ⟨F,inferInstance,inferInstance,hF,
      ⟨(componentQuotientImageEquiv E h hz).symm.trans e⟩⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
