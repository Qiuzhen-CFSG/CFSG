module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts.Irreducible

/-!
# The source B.4 inputs for the M₂₂ exclusion

The legacy `FullB42` uses a vector line in the triple-six offender clause.
The source's F₄-line is a projective line, hence a vector plane, as K.1.3
specifies. Here the universal B.4.2 implication uses the existing corrected
full action list; every other clause and every alternative is retained.
The legacy interface and its conditional theorems remain unchanged.

The M₂₂ model comparisons do not use that offender clause. They exclude
every B.4.2 component, after B.1.11 constructs the actual faithful central
section of an arbitrary FF-module. The full B.4.5 table then selects the
native code action, with the cocode removed by its strict quadratic bound.
These two deductions discharge the contracts consumed by `F918Source`.
The universal B.4 implications themselves remain earlier source inputs.

Source: Aschbacher–Smith, B.4.2/B.4.5, pp.86–87, K.1.3, p.453,
and 13.8.21(2), p.956 (combined manuscript, 1 March 2004).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.SourceB4

universe u v

/-- The universal B.4.2 implication with the source projective-line convention.
This retains the full action list, not a prefiltered M₂₂ exclusion. -/
def FullB42 (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type v)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D),
    B42Hypotheses 𝒦 ρ A →
      ProjectiveLine.IrreducibleActionCase ρ (generalizedFitting D) (offenderSubgroup ρ)

private theorem not_ff_of_irreducible {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hyp : B4Hypotheses 𝒦 ρ)
    (e : generalizedFitting D ≃* M22) : ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨A, hA⟩ := hyp.exists_bestOffender hff
  exact ModelSieve.not_quasisimpleModel e ((hB42 D V ρ A hA).model ρ)

/-- B.1.11 supplies a faithful irreducible central section of every faithful
FF-module. Its actual M₂₂ generalized Fitting subgroup contradicts the
corrected full B.4.2 list, including for actors with an outer supplement. -/
theorem noFaithfulFF {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,u} 𝒦) :
    Recognition.NoFaithfulFF 𝒦 := by
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
  exact not_ff_of_irreducible hB42 σ hyp f
    (ModelSieve.SectionImages.ff_of_faithful_image σ hyp.faithful hFF)

/-- The full B.4.5 alternatives recognize the actual generalized-Fitting
restriction as the code module. All model and action comparisons are proved
by `ModelSieve`; only the source classification implications remain inputs. -/
theorem smallQuadraticCode {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,u} 𝒦) (hB45 : FullB45.{u,u} 𝒦) :
    Recognition.SmallQuadraticCode 𝒦 := by
  intro D _ _ V _ _ _ ρ hyp hq he
  obtain ⟨e⟩ := he
  cases hB45 D V ρ (hyp.with_quadratic_bound hq) with
  | ff cubic =>
    exact (not_ff_of_irreducible hB42 ρ hyp e
      (isFFModule_of_cubicRatio_le_one ρ cubic)).elim
  | table _ _ row => exact ModelSieve.code_of_table ρ e hq row
  | boundary _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.SourceB4
