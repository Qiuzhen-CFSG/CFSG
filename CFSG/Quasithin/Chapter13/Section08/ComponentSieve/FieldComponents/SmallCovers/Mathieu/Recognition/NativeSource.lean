module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyTwo
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictM22Cocode
/-!
# Source recognition for the M22 central quotient in Chapter 13

For an arbitrary faithful FF-module, B.1.11 supplies a faithful irreducible
central section with the same generalized Fitting group. The proved native
M22 source classification excludes its FF action. For a small quadratic
irreducible section, the actual source marking is code, cocode, or triple
cover. The strict native cocode bound excludes cocode, and the component's
trivial center excludes the triple cover. The code intertwiner is retained
on the literal generalized-Fitting restriction.

These proofs discharge both generic contracts used by the original Mathieu
central-witness construction. They use the full known-simple catalogue and
require no universal B.4.2 or B.4.5 premise. The F.9.18 selection remains with
the field-sieve owner; qt-d-1381-source supplies the original local setup.
Source: Aschbacher–Smith, B.1.11, B.4.2/B.4.5, K.4.4 and 13.8.21(2).
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
universe u v
private theorem not_ff_of_irreducible {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (e : generalizedFitting D ≃* M22) : ¬ IsFFModule ρ := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  intro hff
  have hc := (isFFModule_iff_cubicRatio_le_one ρ).mp hff
  have he : Nonempty ((generalizedFitting D ⧸ center (generalizedFitting D)) ≃* M22) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (ModelSieve.SectionImages.center_eq_bot e)).trans
      QuotientGroup.quotientBot).trans e⟩
  exact ChapterK.SporadicCatalogue.SourceFF.not_ff_m22
    ⟨hyp.sqtk, rfl, hyp.quasisimple, hyp.faithful, hyp.irreducible,
      hc.trans (by norm_num)⟩ he hff

/-- Every faithful finite module of an SQTK actor with generalized Fitting
group M22 fails to be an FF-module, without an irreducibility assumption. -/
theorem noFaithfulFF : Recognition.NoFaithfulFF.{u} KnownSimple.IsKnownSimple := by
  intro D _ _ V _ _ _ ρ hD hfaith he hff
  obtain ⟨e⟩ := he
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple (generalizedFitting D) := ModelSieve.SectionImages.quasisimple e
  obtain ⟨A, hA, hLA⟩ := ModelSieve.SectionImages.bestOffender_commutator ρ e hff
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hker⟩ :=
    ChapterB.source_lemma_B_1_11 ρ hfaith (generalizedFitting D) A hLA hA
  let σ := centralSectionRepresentation ρ (generalizedFitting D) H I hHI
    le_normalizer_of_normal
  let : Finite (centralQuotient ρ (generalizedFitting D) I) :=
    Finite.of_surjective ((fixedSpace ρ (generalizedFitting D)).comap I.subtype).mkQ
      (Submodule.mkQ_surjective _)
  have hyp := ModelSieve.SectionImages.section_hypotheses ρ hD e H hLH I hI hHI
    (hker.trans inf_le_right)
  let f : generalizedFitting H ≃* M22 :=
    (MulEquiv.subgroupCongr (ModelSieve.SectionImages.overgroup_fitting e H hLH)).trans
      ((subgroupOfEquivOfLe hLH).trans e)
  exact not_ff_of_irreducible σ hyp f
    (ModelSieve.SectionImages.ff_of_faithful_image σ hyp.faithful hFF)

/-- Actual source recognition and the strict native cocode bound select the code action. -/
theorem smallQuadraticCode :
    Recognition.SmallQuadraticCode.{u} KnownSimple.IsKnownSimple := by
  intro D _ _ V _ _ _ ρ hyp hq he
  obtain ⟨e⟩ := he
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hquot : Nonempty ((generalizedFitting D ⧸ center (generalizedFitting D)) ≃* M22) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (ModelSieve.SectionImages.center_eq_bot e)).trans
      QuotientGroup.quotientBot).trans e⟩
  have hs : ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.SourceHypotheses
      ρ (generalizedFitting D) :=
    ⟨hyp.sqtk, rfl, hyp.quasisimple, hyp.faithful, hyp.irreducible,
      (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq, hquot⟩
  rcases ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.source_markedModels
      ρ (generalizedFitting D) hs with hc | hc | hc
  · obtain ⟨model⟩ := hc
    refine ⟨model.componentEquiv, model.equivalence.toLinearEquiv, ?_⟩
    intro g v
    have h := LinearMap.congr_fun (model.equivalence.isIntertwining' g.val) v
    change model.equivalence (ρ g.val v) =
      MathieuCode.m22OuterCodeRepresentation (model.embedding g.val) (model.equivalence v) at h
    rw [model.on_component g] at h
    exact h
  · obtain ⟨model⟩ := hc
    have hle := quadraticRatio_le_of_injective_equivariant ρ
      MathieuCode.m22OuterCocodeRepresentation model.embedding model.injective
      model.equivalence.toLinearEquiv
      (fun g v => LinearMap.congr_fun (model.equivalence.isIntertwining' g) v)
    exact (not_lt_of_ge (hle.trans hq)
      MathieuCode.QuadraticActors.StrictM22Cocode.m22OuterCocode_quadraticRatio_gt_two).elim
  · obtain ⟨model⟩ := hc
    have hc := Nat.card_congr (centerCongr model.componentEquiv).toEquiv
    rw [ModelSieve.SectionImages.center_eq_bot e, Subgroup.card_bot,
      M22TripleCover.center_card] at hc
    omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
