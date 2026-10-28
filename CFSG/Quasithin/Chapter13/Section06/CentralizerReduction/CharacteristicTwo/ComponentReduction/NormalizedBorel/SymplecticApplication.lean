module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.SourceReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.SymplecticInputs

/-!
# Passing the normalized component to the symplectic source argument

The normalized-component reduction constructs the actual symplectic image
and excludes the signed-three extensions. Its original (i)/(ii) provenance
is precisely what the later symplectic argument needs to recover Lᵥ ≤ K.
This application supplies those outputs to the existing whole-component,
Sylow, Borel and torus argument. The exact I.1.3 universal-kernel conclusion
remains explicit; it belongs to the independent multiplier theorem.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928; I.1.3.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module PerfectCentralCovering
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- An actual application to the sibling symplectic exclusion. No symplectic
isomorphism, Borel placement, or two-case provenance is an input here. The
multiplier premise is kept at its exact independent source boundary. -/
theorem false_of_normalized_component_and_multiplier
    {κ : GroupClass} {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (flag : FlagSource T L V V₁ V₂)
    (d : InitialSieve.Setup κ T flag.flag.module)
    (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃
      (markedZ flag.flag.module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ flag.flag.module)
    (K : Subgroup (Gv (markedV flag.flag.module)))
    (hK : IsComponent (Gv (markedV flag.flag.module)) K)
    (a : InitialSieve.ActionData flag.flag.module (T : Subgroup G) K)
    {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hEK : EStar flag.flag.module K a.a_normalizes a.z_normalizes ≤
      NormalizerAction.componentImage K)
    (halt : ModelPlacement.Alternatives flag.flag.module K m)
    (hTN : localT (T : Subgroup G) (markedV flag.flag.module) ≤ X K)
    (hI13 : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      Nat.card F = 2 ^ m → (universalProjection (Sp F)).ker = ⊥) : False := by
  have hk : IsPGroup 2 flag.flag.module.action.ker := by
    rw [flag.flag.action_kernel]
    exact pCore_isPGroup
  obtain ⟨hcases, ⟨b⟩⟩ := source_symplectic_borel d K hK a hm hmodel hEK halt
    hk earlier.T_normalizes_L hTN
  exact SymplecticInputs.false_of_symplectic_component_image flag V₃ earlier hcounter hfusion
    K hK b.marking.componentEquiv b.cardinality hm (hI13 b.F b.cardinality) hTN hcases

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
