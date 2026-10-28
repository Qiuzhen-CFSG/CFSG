module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

/-!
# Native recognition on the literal external PSL₂ layer

The corrected constituent classification is applied to the faithful FF action
on the actual inverter-fixed multiplicity space. Its original component map
and intertwining map give either the naturally marked Borel layer or the
marked S₅ constituent, with exponent two in the latter case.

OriginalSource.LinearTwo supplies the moved-space equality on actual source
orbit spans. F.9.18 still supplies the multiplicity action and its FF
hypotheses; their construction and the terminal exclusions remain with
qt-d-138-fields-source. No universal legacy B.4.2 premise is retained here.
Source: Aschbacher–Smith, B.4.2 and 13.8.20(a), pp.86 and 954.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
open LinearTwo

universe u v w
variable {G : Type w} [Group G] [Finite G]
    (H K X V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (W : Subrepresentation ρ)

local notation "Kstar" => Source.starImage H K
local notation "C" => centralBottom ρ Kstar W
local notation "κ" => MonoidHom.comp ρ (Subgroup.subtype (Source.starImage H K))

/-- Construct the literal natural layer or retain the full marked S₅ constituent.
The corrected native B.4.2 theorem supplies classification.
The faithful constituent hypotheses and compatibility maps are the intermediate
SourceOrbit output; the still-needed moved-space equality is displayed explicitly. -/
theorem source_layer_or_five_constituent
    {E : Type u} [Group E] [Finite E]
    {N : Type v} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N)
    (hσ : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (b : Kstar ≃* generalizedFitting E)
    (a : SectionMultiplicity ρ s C W ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v) =
      σ (b k) (a v))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL Kstar 2 (2^n))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ Kstar)
    (S : Sylow 2 Kstar) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf Kstar = normalizer (S : Set Kstar)) :
    (∃ F : BinaryField, F.degree = n ∧ ∃ e : Kstar ≃* SL(2,F.Carrier),
      (B₀.subgroupOf Kstar).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F.Carrier ∧
      (C).toSubmodule ≤ Representation.invariants κ ∧
      (∀ (g : Kstar) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer κ (linearNatural F 2) e (C).toSubmodule W.toSubmodule)) ∨
    (n = 2 ∧ Nonempty (MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) := by
  have hm' : ClassicalGroup.IsPSL (generalizedFitting E) 2 (2^n) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact ⟨F, inferInstance, inferInstance, hF, ⟨b.symm.trans e⟩⟩
  cases linearTwo_constituent σ hσ hff hn hm' with
  | natural F hF _ e =>
    left
    have ha' : ∀ k v,
        (a.trans e.linearEquiv) (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v) =
          HigherFieldBorelFixedSpaces.binaryNatural 2 ((b.trans e.groupEquiv) k)
            ((a.trans e.linearEquiv) v) := by
      intro k v
      change e.linearEquiv (a (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v)) = _
      rw [ha]
      exact e.intertwines (b k) (a v)
    obtain ⟨e', hB', hc, hq, layer⟩ := natural_layer ρ Kstar W s hs S
      (B₀.subgroupOf Kstar) hB (by rw [hmark]; exact hgen) hW
      (b.trans e.groupEquiv) (a.trans e.linearEquiv) ha'
    exact ⟨F, hF, e', hB', hc, hq, layer⟩
  | five hn e => exact Or.inr ⟨hn, ⟨e⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
