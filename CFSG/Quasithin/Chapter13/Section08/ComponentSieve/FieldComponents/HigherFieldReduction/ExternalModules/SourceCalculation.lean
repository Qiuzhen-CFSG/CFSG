module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Natural
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Sections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Critical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Generation

/-!
# External source assembly with the repaired local interface

Source: Aschbacher–Smith, proof of 13.8.20(a), printed pp.954–955.
The minimal earlier data construct the structural inputs. Actual Borel
centralization excludes both natural families. In the moved exceptional
branch the genuine selected critical pair, rank and quadraticity combine
with the marked parabolic calculation to give the contradiction.

The old conditional family remains unchanged. This family has no obsolete
covered centralizer formula, local index, full-L₁ commutator premise, W = U,
or assumed faithfulness on W. Borel centralization is a separate intermediate
result to be supplied by the full-product source-alternative calculation.
The source supplement theorem discharges generation in both local cases.
For the covered case it uses the actual elementary-nine quotient and the
SQTK three-rank bound, retaining the two-core and star-map kernels.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
universe u
variable {G : Type u} [Group G] [Finite G]

section Sections
variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f in
/-- Both L₂ parities and both independently oriented L₃ layer alternatives
are impossible once the actual source Borel centralization has been proved. -/
theorem natural_sections_impossible
    (hVH : V ≤ H)
    (hcentral : borelResidual (borelLift H K f.component_le
      (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤ centralizer (V : Set G))
    (hne : Source.starImage H K ≠ ⊥)
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hnat : LinearTwoSections ρ (Source.starImage H K)
        (SylowBorel.relativeBorel (Source.starImage H K) S) ∨
      LinearThreeSections ρ (Source.starImage H K) s hs
        (SylowBorel.relativeBorel (Source.starImage H K) S)) : False := by
  have hz := f.setup.fixes_line.trans (Subgroup.centralizer_le_normalizer _)
  have hKnorm := le_normalizer_of_normal_subgroupOf f.component_le
  have hseedH := f.setup.seed_le.trans hVH
  let B₀ := SylowBorel.relativeBorel (Source.starImage H K) S
  have hB₀ : B₀ ≤ Source.starImage H K := SylowBorel.relativeBorel_le _ S
  rcases hnat with ⟨F, hn, e, hmark, C, W, hC, hW, ⟨layer⟩⟩ |
    ⟨F, hn, ho, e, hmark, C, W, hC, hσ, ⟨layer⟩, htail⟩
  · exact sl2_natural_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
      hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn F.card_eq e hmark hcentral
      C.toSubmodule W.toSubmodule hC hW layer
  · rcases htail with hW | ⟨D, hτ, ⟨second⟩, hD⟩
    · exact psl3_odd_one_layer_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn ho F.card_eq e hmark
        hcentral _ hσ C.toSubmodule W.toSubmodule hC hW layer
    · exact psl3_odd_two_layers_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn ho F.card_eq e hmark
        hcentral _ hσ _ hτ C.toSubmodule W.toSubmodule D.toSubmodule hC hD layer second

include f d in
/-- With the source actor generation, only the actual moved exceptional
module remains. Its coordinates exclude transvections on the original U. -/
theorem external_moved_reduction_of_supplement_generation
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcentral : borelResidual (borelLift H K f.component_le
      (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤ centralizer (V : Set G))
    (hactorGeneration : Source.starImage H K ⊔
      (Source.starImage H X ⊔ (P : Subgroup (Source.Hstar H))) = ⊤)
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥) :
    (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) ∧
      ∃ s : S₃ →* Source.Hstar H,
        AdequateExternalInputs H K X (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ ρ s ∧
        MovedFiveSection ρ (Source.starImage H K) s := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  obtain ⟨s, a⟩ := source_ff_inputs H K X L V V₃ V₁ M T ρ P f S d ha hmodel hfit
  let B₀ := SylowBorel.relativeBorel (Source.starImage H K) S
  have hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K)) :=
    comap_map_eq_self_of_injective (Source.starImage H K).subtype_injective _
  rcases source_alternatives_of_supplement_generation H K X L (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁)
    V V₃ V₁ T ρ P s f a d.fitting_cases hfit hF918 hB42 A hA hAquad hbound hAfaith S B₀ hB hactorGeneration
      with hnat | hmoved
  · have hne : Source.starImage H K ≠ ⊥ := by
      intro hb
      have hc := a.model.three_dvd_card
      rw [hb, card_bot] at hc
      norm_num at hc
    exact (natural_sections_impossible H K L V V₃ V₁ T ρ P f S
      hVH hcentral hne s a.commuting hnat).elim
  · obtain ⟨W, hW, ⟨c⟩⟩ := hmoved
    exact ⟨c.no_transvection_on_ambient W, s, a, W, hW, ⟨c⟩⟩


end Sections

section Endpoint
variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁)
    (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f d in
/-- The critical witness and parabolic placement are discharged here. The
remaining supplement generation and Borel centralization are explicit
intermediate inputs, not additional fields in the source hypothesis record. -/
theorem external_impossible_of_supplement_generation
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcentral : borelResidual (borelLift H K f.component_le
      (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤ centralizer (V : Set G))
    (hactorGeneration : Source.starImage H K ⊔
      (Source.starImage H X ⊔ (P : Subgroup (Source.Hstar H))) = ⊤)
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (initial : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (e : CriticalInputs.EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ) : False := by
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  obtain ⟨_, s, _, W, hW, ⟨c⟩⟩ := external_moved_reduction_of_supplement_generation
    H K X L V V₃ V₁ M T ρ P f S d ha hVH hmodel hfit hcentral hactorGeneration
    hF918 hB42 A hA hAquad hbound hAfaith
  obtain ⟨w, hplace, _, hcore, hTK⟩ := exists_critical_witness
    H K X L V V₃ V₁ M T ρ P f S d ha hVH initial e s W hW c
  have hgen : H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) := by
    rw [f.generation, f.single_component, f.overlap, sup_assoc]
  exact LinearTwo.FiveReconstruction.tensor_branch_impossible_on_moved H K
    (one L (T : Subgroup G) V₁) V₃ V₁ w.pair.Vgamma w.alpha ((T : Subgroup G) ⊓ K)
    T ρ s W f.conjugation hgen c (fun _ _ _ => w.rank_gt_one)
    w.actor_le w.conjugator rfl hplace hcore hTK w.quadratic

include f d in
/-- In the ordinary local case the source supplement generation is proved
from X = L₁; only the separately produced Borel centralization is passed in. -/
theorem ordinary_external_impossible
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcentral : borelResidual (borelLift H K f.component_le
      (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤ centralizer (V : Set G))
    (hX : X = one L (T : Subgroup G) V₁)
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (initial : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (e : CriticalInputs.EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ) : False := by
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  have hg := ordinary_star_generation H K X (one L (T : Subgroup G) V₁)
    (T : Subgroup G) hgen hX (P : Subgroup (Source.Hstar H)) f.sylow_image
  exact external_impossible_of_supplement_generation H K X L V V₃ V₁ M T ρ P f S d
    ha hVH hmodel hfit hcentral hg hF918 hB42 A hA hAquad hbound hAfaith initial e

include f d in
/-- The complete external source contradiction, with supplement generation,
the selected critical witness and its parabolic placement all discharged.
Actual Borel centralization is the separate intermediate result supplied by
the full-product field reduction; the earlier F.9.18, B.4.2 and geometric
inputs retain their original scope. -/
theorem external_impossible
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcentral : borelResidual (borelLift H K f.component_le
      (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤ centralizer (V : Set G))
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (initial : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (e : CriticalInputs.EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ) : False := by
  have hg := source_supplement_generation H K X L V V₃ V₁ M T ρ P f S d ha hmodel
  exact external_impossible_of_supplement_generation H K X L V V₃ V₁ M T ρ P f S d
    ha hVH hmodel hfit hcentral hg hF918 hB42 A hA hAquad hbound hAfaith initial e

end Endpoint

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

end
