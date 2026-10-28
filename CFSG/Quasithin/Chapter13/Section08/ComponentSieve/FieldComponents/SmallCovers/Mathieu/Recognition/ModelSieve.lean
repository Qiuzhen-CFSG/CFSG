module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve.Comparisons
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve.SectionImages
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# M₂₂ recognition from the full B.4 alternatives

The actual M₂₂ order and center exclude all eleven B.4.2 alternatives.
For a faithful action whose generalized Fitting subgroup acts irreducibly,
this proves absence of FF offenders. Applying the full B.4.5 implication,
the quadratic bound removes the boundary cases and all strict-ratio table
rows, including the M₂₂ cocode. The remaining non-Mathieu rows are removed
by concrete group comparisons. The surviving code row supplies its actual
intertwining linear equivalence, proving `Recognition.SmallQuadraticCode`.

For an arbitrary faithful FF-module, B.1.11 constructs an invariant Irr⁺
section whose action image is an FF-module. Its kernel centralizes M₂₂
and is therefore trivial. The stabilizing overgroup still has the marked
M₂₂ as its entire generalized Fitting subgroup, so the irreducible exclusion
applies. This proves `Recognition.NoFaithfulFF`, retaining outer supplements.

The universal B.4.2 and B.4.5 implications remain explicit earlier inputs.
Only actual generalized-Fitting model identifications are used from the
B.4.2 conclusion.

Source: Aschbacher–Smith, B.4.2/B.4.5, printed pp.86–87, and their use
in 13.8.21(2), p.956 (1 March 2004 manuscript).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open BenderSuzuki.MatrixGroups Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve

universe u v

/-- Every actual generalized-Fitting model in the full B.4.2 list is
incompatible with an M₂₂ marking. -/
theorem not_quasisimpleModel {L : Type*} [Group L] (e : L ≃* M22) :
    ¬ QuasisimpleModel L := by
  intro h
  cases h with
  | linearTwo F f => exact not_linear_two e F.Carrier f
  | linearThree F f => exact not_linear_three e F.Carrier f
  | symplecticFour F f => exact not_symplectic_four e F.Carrier f
  | g2 F f => exact not_g2 e F.Carrier f
  | alternatingSix f => exact not_small_alternating e 6 (Or.inl rfl) f
  | alternatingSeven f => exact not_small_alternating e 7 (Or.inr rfl) f
  | tripleSix c _ => exact not_center_three e c
  | g2DerivedTwo f => exact not_g2_derived_two e f
  | linearFourTwo f => exact not_binary_linear e 4 (Or.inl rfl) f
  | linearFiveTwo f => exact not_binary_linear e 5 (Or.inr rfl) f

variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

/-- The genuine irreducible B.4 hypotheses and the universal B.4.2
implication exclude FF modules with generalized Fitting group M₂₂. -/
theorem not_ff_of_irreducible {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 ρ) (e : generalizedFitting D ≃* M22) :
    ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨A, hA⟩ := hyp.exists_bestOffender hff
  exact not_quasisimpleModel e ((hB42 D V ρ A hA).model ρ)

/-- B.1.11's actual section outputs are incompatible with the full B.4.2
classification. The arbitrary-module exclusion below constructs these outputs
from the original faithful FF-module. -/
theorem not_ff_central_section {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (hD : IsSQTK 𝒦 D) (e : generalizedFitting D ≃* M22)
    (H : Subgroup D) (hLH : generalizedFitting D ≤ H)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ (generalizedFitting D) I)
    (hHI : H ≤ subspaceStabilizer ρ I)
    (hker : (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
      le_normalizer_of_normal).ker.map H.subtype ≤
        centralizer (generalizedFitting D : Set D)) :
    ¬ IsFFModule (imageRepresentation
      (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
        le_normalizer_of_normal)) := by
  let σ := centralSectionRepresentation ρ (generalizedFitting D) H I hHI
    le_normalizer_of_normal
  let : Finite (centralQuotient ρ (generalizedFitting D) I) :=
    Finite.of_surjective ((fixedSpace ρ (generalizedFitting D)).comap I.subtype).mkQ
      (Submodule.mkQ_surjective _)
  have hyp := SectionImages.section_hypotheses ρ hD e H hLH I hI hHI hker
  let f : generalizedFitting H ≃* M22 :=
    (MulEquiv.subgroupCongr (SectionImages.overgroup_fitting e H hLH)).trans
      ((subgroupOfEquivOfLe hLH).trans e)
  intro hff
  exact not_ff_of_irreducible σ hB42 hyp f
    (SectionImages.ff_of_faithful_image σ hyp.faithful hff)

/-- An arbitrary finite faithful FF-module yields a B.1.11 central section.
Its faithful action and actual generalized Fitting subgroup contradict B.4.2. -/
theorem not_ff_of_faithful {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (hD : IsSQTK 𝒦 D) (hfaith : Function.Injective ρ)
    (e : generalizedFitting D ≃* M22) : ¬ IsFFModule ρ := by
  intro hff
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple (generalizedFitting D) := SectionImages.quasisimple e
  obtain ⟨A, hA, hLA⟩ := SectionImages.bestOffender_commutator ρ e hff
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hker⟩ :=
    ChapterB.source_lemma_B_1_11 ρ hfaith (generalizedFitting D) A hLA hA
  exact not_ff_central_section ρ hB42 hD e H hLH I hI hHI
    (hker.trans inf_le_right) hFF

/-- Discharge the published contract for every finite faithful module,
without an irreducibility premise on the original representation. -/
theorem noFaithfulFF {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,u} 𝒦) :
    Recognition.NoFaithfulFF 𝒦 := by
  intro D _ _ V _ _ _ ρ hD hfaith he
  obtain ⟨e⟩ := he
  exact not_ff_of_faithful ρ hB42 hD hfaith e

omit [Finite D] [Finite V] in
/-- All fourteen full table rows are considered. The code intertwiner
is retained; in particular the cocode is eliminated by its strict bound. -/
theorem code_of_table (e : generalizedFitting D ≃* M22)
    (hq : quadraticRatio ρ ≤ 2) (h : TableB45 ρ (generalizedFitting D)) :
    MathieuCode.IsM22Code (ρ.comp (generalizedFitting D).subtype) := by
  cases h with
  | alternatingSeven action _ _ _ =>
    exact (not_small_alternating e 7 (Or.inr rfl) action.groupEquiv).elim
  | orthogonal _ F _ actor _ _ _ _ =>
    exact (not_projective_two e F.Carrier actor).elim
  | unitary F n large degree J conjugation action _ _ _ =>
    exact (not_unitary_three e F n large degree J conjugation action.groupEquiv).elim
  | suzuki k positive action _ _ _ =>
    have ht : 3 ∣ Nat.card (SuzukiMatrixGroup k) := by
      rw [← Nat.card_congr action.groupEquiv.toEquiv, card_of_equiv_m22 e]
      norm_num
    exact (suzukiMatrixGroup_three_free k positive ht).elim
  | linearThree _ _ _ _ _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | g2Derived action _ _ _ => exact (not_g2_derived_two e action.groupEquiv).elim
  | mathieuTwelve _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | tripleMathieuTwentyTwo centerEquiv _ _ _ _ => exact (not_center_three e centerEquiv).elim
  | mathieuTwentyTwoCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyTwoCode action _ _ _ =>
    exact ⟨action.groupEquiv, action.linearEquiv, action.intertwines⟩
  | mathieuTwentyThreeCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyThreeCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

/-- The full source implications give the actual code identification;
no prefiltered M₂₂ table or FF-exclusion premise is used. -/
theorem code_of_full_classification {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 ρ) (hq : quadraticRatio ρ ≤ 2)
    (e : generalizedFitting D ≃* M22) :
    MathieuCode.IsM22Code (ρ.comp (generalizedFitting D).subtype) := by
  cases hB45 D V ρ (hyp.with_quadratic_bound hq) with
  | ff cubic =>
    exact (not_ff_of_irreducible ρ hB42 hyp e
      (isFFModule_of_cubicRatio_le_one ρ cubic)).elim
  | table _ _ row => exact code_of_table ρ e hq row
  | boundary _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

/-- Discharge the published small-quadratic-code contract. -/
theorem smallQuadraticCode {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,u} 𝒦) (hB45 : FullB45.{u,u} 𝒦) :
    Recognition.SmallQuadraticCode 𝒦 := by
  intro D _ _ V _ _ _ ρ hyp hq he
  obtain ⟨e⟩ := he
  exact code_of_full_classification ρ hB42 hB45 hyp hq e

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve
