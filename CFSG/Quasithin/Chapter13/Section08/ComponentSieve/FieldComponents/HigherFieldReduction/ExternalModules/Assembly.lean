module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

/-!
# Connecting the external source structure and module branches

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20(a), printed pp.954–955; local notation 13.2.1–2, p.877, and
13.7.3(9), p.936; F.9.18, pp.325–326; B.4.2, pp.86–87.

The actual local marks select the cubic residual and prove solvability of
L₁T and cubic commutator generation. The ambient SQTK bound and the full
seven-entry higher-field list give the three surviving component carriers.
The constructed commuting S₃ action then feeds the FF constituent and orbit
calculation, including its actual quotient and multiplicity maps.

Both natural families are excluded here. In even-degree L₂, the marked local
geometry derives the covered case and B_C ≤ K, so the source index-three
identity gives B-centralization. In odd degree the concrete Borel orders give
that centralization. The one/two-layer fixed-space arguments retain the
literal U_H/V₁ and independently oriented natural/dual L₃ factors.

Thus the existing FF route leaves only full marked tensor coordinates on the
actual moved module W = [U,K*], and these exclude transvections on U. The
conditional final connection preserves the genuine critical conjugate and
its quadraticity. It uses the previously proved solvable-quotient/Fitting
argument for faithfulness on W, without assuming W = U.

This is not yet the complete external-X exclusion. The full-L₁ commutator
premise used by the orbit API still needs source justification or an adequate
supplement-generation replacement, especially in the covered local case.
The critical-pair rank, actual conjugation and placement in K* must also be
supplied from the earlier geometry. The local Borel identities and the full
earlier F.9.18/B.4.2 implications are explicit parent inputs. All earlier
conditional whole-U APIs remain unchanged.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Earlier marked local data, with the source Borel lifted inside the actual K.
The residual, centralizer and index statements are the precise local Borel inputs;
no centralization by B, classified module or critical rank conclusion is included. -/
structure LocalData (H K X L T V V₃ V₁ M : Subgroup G) (hKH : K ≤ H)
    (S : Sylow 2 (Source.starImage H K)) : Prop where
  local_cases : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
    (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁)
  ordinary_card : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3
  covered_action : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    Nonempty (LocalAction.NaturalSetup L T V V₁ V₃)
  covered_factor : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    one L T V₁ = plus L T V₁ ⊔ zero L
  seed_commutator : V₃ = ⁅V₃, one L T V₁⁆
  theta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  solvable_overgroups : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J →
    J ≤ normalizer (V₁ : Set G) → Group.IsSolvable J → J ≤ M
  sylow : Chapter1.IsSylowIn 2 T H
  sylow_inter : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
    Source.starImage H T ⊓ Source.starImage H K
  residual_le : let B := borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    residualIn 3 B ≤ centralizingResidual B (one L T V₁) L
  centralizes : let B := borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    centralizingResidual B (one L T V₁) L ≤ centralizer (V : Set G)
  normalizes : let B := borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    B ⊔ one L T V₁ ≤ normalizer (L : Set G)
  covered_formula : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    let B := borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    centralizingResidual B (one L T V₁) L = residualIn 3 B ⊔ zero L
  covered_index : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    let B := borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    (centralizingResidual B (one L T V₁) L ⊔ B.pCoreIn 2).relIndex (B ⊔ X) = 3

namespace LocalData
variable {H K X L T V V₃ V₁ M : Subgroup G} {hKH : K ≤ H}
  {S : Sylow 2 (Source.starImage H K)} (d : LocalData H K X L T V V₃ V₁ M hKH S)

omit [Finite G] in
include d in
theorem marked_cases :
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁) :=
  d.local_cases.imp id (fun h => h.2)

omit [Finite G] in
include d in
theorem fitting_cases :
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = plus L T V₁) :=
  d.local_cases.imp id (fun h => ⟨h.1, h.2.2⟩)
end LocalData

variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : LocalData H K X L (T : Subgroup G) V V₃ V₁ M f.component_le S)

include f d in
/-- Supply the FF section owner's structural contract from the ambient SQTK
bound, all seven higher-field carriers, the marked local data, and 13.8.14.
The full residual commutator identity for L₁ remains an explicit extra
premise: its covered-case source justification is still required. -/
theorem source_ff_inputs
    (ha : ExternalXAlternative H K X)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcomm : ⁅one L (T : Subgroup G) V₁, (T : Subgroup G)⁆ = one L (T : Subgroup G) V₁) :
    ∃ s : S₃ →* Source.Hstar H,
      SourceOrbit.ExternalInputs H K X (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ ρ s := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  obtain ⟨_, hp, hc, hsol, hseed⟩ := Structure.MarkedBorel.selected_local_inputs
    L (T : Subgroup G) V V₁ V₃ X T.isPGroup' f.setup.line_normalized d.marked_cases
    d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) : Subgroup G) := hsol
  have hselected := Structure.selected_fitting_alternative H L
    (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁) X d.fitting_cases hfit
  obtain ⟨hcstar, hnot, hn, hr⟩ := Structure.external_cubic_rank 𝒦 H K X
    f.sqtk f.component_le f.component hp hc ha
  have hrs : primeRank 3 (Source.starImage H K) ≤ 1 := by
    rw [← Structure.threeRank_eq_star H K f.component_le f.component.subnormal]
    exact hr
  obtain ⟨model, hz, _, _⟩ := hmodel.external_structure hrs
  obtain ⟨s, hi, hs, hm, hg, _⟩ := Structure.source_cubic_action H K X
    (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ hgen hc ha hz hselected ρ f.conjugation hseed
  exact ⟨s, {
    component_normal := inferInstance
    centerless := hz
    component_rank := hr
    model := model
    solvable := hsol
    one_twoPerfect := residual_isPPerfect _
    one_commutator := hcomm
    fitting := hselected
    cubic_card := hcstar
    cubic_normal := hn
    embedding := hi
    commuting := fun k g => hs ⟨g, rfl⟩ k k.property
    mark := hm
    cubic_generation := hg }⟩
include f d in

/-- Eliminate both natural families from their constructed section coordinates.
The even L₂ branch derives the covered case and B_C placement; the odd branches
use the actual three-prime Borel orders. Both L₃ orientations are retained. -/
theorem natural_sections_impossible
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hne : Source.starImage H K ≠ ⊥)
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hnat : LinearTwoSections ρ (Source.starImage H K)
        (SylowBorel.relativeBorel (Source.starImage H K) S) ∨
      LinearThreeSections ρ (Source.starImage H K) s hs
        (SylowBorel.relativeBorel (Source.starImage H K) S)) : False := by
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  have hz := f.setup.fixes_line.trans (Subgroup.centralizer_le_normalizer _)
  have hKnorm := le_normalizer_of_normal_subgroupOf f.component_le
  have hseedH := f.setup.seed_le.trans hVH
  let B₀ := SylowBorel.relativeBorel (Source.starImage H K) S
  let B := borelResidual (borelLift H K f.component_le B₀)
  let BC := centralizingResidual B (one L (T : Subgroup G) V₁) L
  have hB₀ : B₀ ≤ Source.starImage H K := SylowBorel.relativeBorel_le _ S
  rcases hnat with ⟨F, hn, e, hmark, C, W, hC, hW, ⟨layer⟩⟩ |
    ⟨F, hn, ho, e, hmark, C, W, hC, hσ, ⟨layer⟩, htail⟩
  · rcases Nat.even_or_odd F.degree with he | ho
    · have hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ F.degree) :=
        ⟨F.Carrier, inferInstance, inferInstance, F.card_eq,
          ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
      obtain ⟨_, hcov, _, hCK, hCJ⟩ := Structure.MarkedBorel.source_placements
        H K L (T : Subgroup G) V V₁ V₃ M X f.component_le hgen d.sylow hz
        d.marked_cases d.ordinary_card d.covered_action d.covered_factor
        d.seed_commutator d.theta d.solvable_overgroups ha S d.sylow_inter hn hmodel he d.covered_formula
      exact sl2_index_natural_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn F.card_eq e hmark
        (one L (T : Subgroup G) V₁) L X ha hCK hCJ d.normalizes
        (d.covered_index hcov) d.centralizes C.toSubmodule W.toSubmodule hC hW layer
    · exact sl2_odd_natural_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn ho F.card_eq e hmark
        BC d.residual_le d.centralizes C.toSubmodule W.toSubmodule hC hW layer
  · rcases htail with hW | ⟨D, hτ, ⟨second⟩, hD⟩
    · exact psl3_odd_one_layer_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn ho F.card_eq e hmark
        BC d.residual_le d.centralizes _ hσ C.toSubmodule W.toSubmodule hC hW layer
    · exact psl3_odd_two_layers_impossible H K V V₃ V₁ f.component_le hseedH f.setup.seed_le
        hKnorm hz f.kernel hne ρ f.conjugation B₀ hB₀ hn ho F.card_eq e hmark
        BC d.residual_le d.centralizes _ hσ _ hτ C.toSubmodule W.toSubmodule D.toSubmodule
        hC hD layer second


open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

include f d in
/-- Construct the only remaining external alternative and prove absence of
transvections on the original U. The natural branches and the unitary family
are discharged; the remaining exceptional critical geometry is not assumed. -/
theorem external_moved_reduction
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcomm : ⁅one L (T : Subgroup G) V₁, (T : Subgroup G)⁆ = one L (T : Subgroup G) V₁)
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥) :
    (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) ∧
      ∃ s : S₃ →* Source.Hstar H,
        SourceOrbit.ExternalInputs H K X (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ ρ s ∧
        MovedFiveSection ρ (Source.starImage H K) s := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  obtain ⟨s, a⟩ := source_ff_inputs H K X L V V₃ V₁ M T ρ P f S d ha hmodel hfit hcomm
  let B₀ := SylowBorel.relativeBorel (Source.starImage H K) S
  have hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K)) :=
    comap_map_eq_self_of_injective (Source.starImage H K).subtype_injective _
  rcases source_alternatives H K X L (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁)
    V V₃ V₁ T ρ P s f a d.fitting_cases hfit hF918 hB42 A hA hAquad hbound hAfaith S B₀ hB
      with hnat | hmoved
  · have hne : Source.starImage H K ≠ ⊥ := by
      intro hb
      have hc := a.model.three_dvd_card
      rw [hb, card_bot] at hc
      norm_num at hc
    exact (natural_sections_impossible H K X L V V₃ V₁ M T ρ P f S d
      ha hVH hne s a.commuting hnat).elim
  · obtain ⟨W, hW, ⟨c⟩⟩ := hmoved
    exact ⟨c.no_transvection_on_ambient W, s, a, W, hW, ⟨c⟩⟩

include f d in
/-- Final connection to the moved tensor endpoint, conditional on the exact
earlier critical geometry. These geometric premises must still be supplied
from the source; this conditional connection is not the completed 13.8.20. -/
theorem external_impossible_of_critical_inputs
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H))
    (hcomm : ⁅one L (T : Subgroup G) V₁, (T : Subgroup G)⁆ = one L (T : Subgroup G) V₁)
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (Vγ Vα T₀ : Subgroup G)
    (earlier_13_8_18_4 : SeedAction.IsConjugation H V₃ V₁ ρ →
      H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      1 < rank (Source.starImage H Vγ))
    (hVγH : Vγ ≤ H) (h : H)
    (hconj : Vγ.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Source.starImage H Vα ≤ Source.starImage H T₀)
    (hcore : Source.starImage H T₀ =
      (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2)
    (hT₀K : Source.starImage H T₀ ≤ Source.starImage H K)
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  obtain ⟨_, s, _, W, _, ⟨c⟩⟩ := external_moved_reduction H K X L V V₃ V₁ M T ρ P f S d
    ha hVH hmodel hfit hcomm hF918 hB42 A hA hAquad hbound hAfaith
  have hgen : H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) := by
    rw [f.generation, f.single_component, f.overlap, sup_assoc]
  exact LinearTwo.FiveReconstruction.tensor_branch_impossible_on_moved H K
    (one L (T : Subgroup G) V₁) V₃ V₁ Vγ Vα T₀ T ρ s W f.conjugation hgen c
    earlier_13_8_18_4 hVγH h hconj hplace hcore hT₀K hquad

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules

end
