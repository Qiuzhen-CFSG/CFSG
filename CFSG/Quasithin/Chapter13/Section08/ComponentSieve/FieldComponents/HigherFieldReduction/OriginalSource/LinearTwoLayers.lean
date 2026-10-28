module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeLayers

/-!
# The original external PSL₂ natural-layer alternative

Apply the corrected constituent recognition to the literal inverter-fixed
multiplicity of an H-orbit of an Irr⁺ constituent. OriginalSource.LinearTwo
derives the moved-space equality from SourceContext, and the normal cubic
supplies commutator generation. The actual Borel marking and both action
coordinate maps are retained in the natural-layer output; the exceptional
output is the marked S₅ constituent and field exponent two.

F.9.18's construction of the faithful FF multiplicity action, and the
subsequent natural/five contradictions, remain with qt-d-138-fields-source.
Neither the legacy universal B.4.2 statement nor W=U is used.
Source: Aschbacher–Smith, 13.8.20(a), printed p.954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open ExternalModules ExternalModules.FFSections ExternalModules.FFSections.LinearTwo
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v w
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)] [(Source.starImage H K).Normal]

/-- Original-source natural or marked-five recognition, with the component
moved-space identity and cubic generation discharged. -/
theorem source_external_linearTwo_layer_or_five
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆)
    (s : S₃ →* Source.Hstar H)
    (hcomm : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlus act.representation (Source.starImage H K) I)
    (W : Subrepresentation act.representation)
    (hW : W.toSubmodule = orbitSpan act.representation ⊤ I)
    {E : Type u} [Group E] [Finite E]
    {N : Type v} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N)
    (hσ : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (b : (Source.starImage H K) ≃* generalizedFitting E)
    (a : SectionMultiplicity act.representation s (centralBottom act.representation (Source.starImage H K) W) W ≃ₗ[ZMod 2] N)
    (ha' : ∀ k v, a (sectionMultiplicityAction act.representation ((Source.starImage H K)).subtype s hcomm (centralBottom act.representation (Source.starImage H K) W) W k v) =
      σ (b k) (a v))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2^n))
    (S : Sylow 2 (Source.starImage H K)) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K))) :
    (∃ F : BinaryField, F.degree = n ∧ ∃ e : (Source.starImage H K) ≃* SL(2,F.Carrier),
      (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F.Carrier ∧
      (centralBottom act.representation (Source.starImage H K) W).toSubmodule ≤ Representation.invariants (act.representation.comp (Source.starImage H K).subtype) ∧
      (∀ (g : (Source.starImage H K)) (u : SeedAction.Space H V₃ V₁), (act.representation.comp (Source.starImage H K).subtype) g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer (act.representation.comp (Source.starImage H K).subtype) (linearNatural F 2) e (centralBottom act.representation (Source.starImage H K) W).toSubmodule W.toSubmodule)) ∨
    (n = 2 ∧ Nonempty (MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hmoved := source_external_linearTwo_moved c act X ha hs hseed e I hI W hW
  obtain ⟨_,_,_,_,hgen,_,_⟩ := source_external_cubic_action act X ha hs hseed
  exact NativeRecognition.source_layer_or_five_constituent H K X V₃ V₁
    act.representation s hcomm W σ hσ hff b a ha' hn ⟨F,hF,hfin,hcard,⟨e⟩⟩
    hmark hgen hmoved S B₀ hB
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
