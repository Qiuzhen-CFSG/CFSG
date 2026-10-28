module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.CentralQuotients
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FullNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitOffenders
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OrbitTransport

/-!
# Full-normalizer FF comparisons on the actual overcomponent modules

An offender in the full linear normalizer is adjoined to the actual
component image. The proved B.5.1 conclusion and the two-group quotient
transfer the negative central-quotient restrictions back through the
literal supplement projection. The original J/O2(J) quotient is compared
only after passing to central quotients; its action kernel is not discarded.

The seed application uses its genuine Irr+ structure. The doubled-orbit
application uses the proved two-core calculation for its two different
simple constituents. No seed/orbit equality or irreducibility of the whole
doubled space is assumed. ModuleExclusions supplies the chosen-flag consumer.
Source: Aschbacher--Smith 11.4.2, p.776, and B.4.2/B.5.1, pp.86,99.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
open Quasisimple.Classification ChapterB.QuasisimpleSource
universe u

/-- The full-normalizer conclusion restricts the original component's
central quotient, through its literal supplement projection. -/
theorem restrictions_of_normalizerConclusion
    {P W : Type u} [Group P] [Finite P] [IsQuasisimple P]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (σ : Representation (ZMod 2) P W) (hf : Function.Injective σ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple P)
    (A : Subgroup (linearNormalizer σ))
    (hA : IsOffender (normalizerRepresentation σ) A)
    (hc : Chapter12.Section02.ModuleClassification.NormalizerConclusion σ A) :
    CentralQuotientRestrictions (P ⧸ center P) := by
  have hk : σ.ker ≤ center P := by
    rw [σ.ker_eq_bot_iff.mpr hf]
    exact bot_le
  let := component_quasisimple σ hk A
  let := component_normal σ A
  let := supplement_finite σ A
  let C := component σ A
  let I := offenderSubgroup (linearAction (supplement σ A))
  let K := C.subgroupOf I
  let ρ := (linearAction (supplement σ A)).comp I.subtype
  let e : P ≃* C := MulEquiv.ofBijective (projection σ A)
    ⟨fun _ _ he => hf (congrArg (fun k : C => linearAction (supplement σ A) k) he),
      projection_surjective σ A⟩
  have hq : IsPGroup 2 (supplement σ A ⧸ C) := by
    let B := A.map (linearNormalizer σ).subtype
    let := hA.1.2
    have hb : IsPGroup 2 (B.subgroupOf (supplement σ A)) :=
      (IsElementaryAbelian.isPGroup (p := 2) (G := A)).map _ |>.comap_subtype
    exact quotient_isPGroup_of_sup_eq_top (B.subgroupOf (supplement σ A)) C hb
      (by rw [sup_comm]; exact (codisjoint_subgroupOf_sup (actionImage σ) B).eq_top)
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IrreducibleBranch.sqtk_of_twoGroup_quotient
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups
      C hq ((IsSQTK.equiv e).mp hsq)).subgroup I
  let eK : P ≃* K := e.trans (subgroupOfEquivOfLe hc.1).symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK
  have hff : IsFFModule ρ := by
    obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender _).mp (supplement_ff σ A hA)
    exact ⟨B.subgroupOf I, (hB.subgroupOf _ (hB.le_offenderSubgroup _)).isOffender _⟩
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact (centralQuotientRestrictions_of_source hc.2.some hsqI inferInstance hff).of_mulEquiv
    (IsQuasisimple.centralQuotientEquiv eK.toMonoidHom eK.surjective)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {J W : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T J W)

/-- B.5.1 on the unchanged seed excludes models via its actual action
quotient, including any covering center killed by the action. -/
theorem seed_restrictions
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    CentralQuotientRestrictions ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  have hff' := D.chosen_normalizer_ff_iff_seedComponent.mp hff
  obtain ⟨A,hA,hc⟩ := D.full_normalizer_source_conclusion h hff'
  let := D.componentImage_quasisimple h.quasisimple
  have hf : Function.Injective D.seedComponentAction :=
    (subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective
  exact (restrictions_of_normalizerConclusion D.seedComponentAction hf
    ((D.seed_sqtk h (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)).subgroup D.componentImage)
    A hA hc).of_mulEquiv (D.componentCentralQuotientEquiv h.quasisimple)

/-- The doubled orbit uses the already proved distinct-constituent two-core
calculation. No equality between the seed and its orbit is assumed. -/
theorem doubled_restrictions
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hd : D.MarkedDoubled) (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    CentralQuotientRestrictions ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  obtain ⟨A,hA,hc⟩ := D.doubledOrbit_full_normalizer_source h hd hff
  let := D.orbitComponent_quasisimple h
  have hf : Function.Injective (D.orbitRepresentation.comp D.orbitComponent.subtype) :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  exact (restrictions_of_normalizerConclusion _ hf
    ((D.sourceOrbit_sqtk h).subgroup D.orbitComponent) A hA hc).of_mulEquiv
    (D.orbitCentralQuotientEquiv h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
