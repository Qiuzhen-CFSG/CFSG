module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransportAlgebra
public import Stellmacher.Recognition.Parrott.NormalizerCosetReflection
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionOrbit

/-!
# Assembly of the normalizer involution transport

The geometric construction has two inputs: an involution moving yF to wF,
and the saturation of the appropriate eight-element involution orbit in wF.
The latter selects the exact image wuvz. The commutator deductions then
complete the transport data while retaining the supplied e, n, and f.

The final theorem constructs the coset reflection from the original recognition
hypotheses and applies the proved eight-element orbit census. Thus it supplies
all transport fields without any additional geometric premise.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, “Generators and relations for N”.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottCentralizerGeneratorData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Assemble the coset reflection and involution-orbit selection. Both
geometric premises retain the literal supplied frame. -/
public theorem exists_normalizer_transport_of_coset_movement
    (f : ParrottCentralizerGeneratorData n)
    (hmove : ∃ s₀ : G, s₀ ∈ normalizer (e.F : Set G) ∧
      s₀ ∉ (e.sylow : Subgroup G) ∧ s₀ ^ 2 = 1 ∧
      f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F)
    (horbit : ∀ s₀ : G, s₀ ∈ normalizer (e.F : Set G) →
      s₀ ∉ (e.sylow : Subgroup G) → s₀ ^ 2 = 1 →
      f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F →
      ∃ s : G, s ∈ normalizer (e.F : Set G) ∧ s ^ 2 = 1 ∧
        s⁻¹ * f.y * s = f.w * f.u * n.v * z) :
    Nonempty (ParrottNormalizerTransportData f) := by
  obtain ⟨s₀, hs₀N, hs₀T, hs₀, hcos⟩ := hmove
  obtain ⟨s, hsN, hs, hy⟩ := horbit s₀ hs₀N hs₀T hs₀ hcos
  exact ⟨f.normalizerTransportOfYConj s hsN hs hy⟩

/-- Construct the normalizer transport involution on the literal supplied frame.
The coset reflection and its eight-element involution orbit select the image
of y; the commutator deductions supply the required images of t and v. -/
public theorem exists_normalizer_transport
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottNormalizerTransportData f) :=
  f.exists_normalizer_transport_of_coset_movement
    (f.exists_normalizer_coset_reflection hns hN h)
    (f.exists_normalizer_involution_y_image h)

end Stellmacher.Recognition.ParrottCentralizerGeneratorData
