module

public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed
public import Stellmacher.Recognition.Parrott.CentralizerCoreOrientationSeed
public import Stellmacher.Recognition.Parrott.CentralizerCoreFirstImage
public import Stellmacher.Recognition.Parrott.CentralizerCoreActionRigidity

/-!
# Assembly of Parrott's oriented core action

The actual outer involution supplied by the odd-rotation argument can be
conjugated by powers of x without changing the supplied Sylow frame or its
fifth-power relation. The assembly theorem obtains the full core action from
two geometric inputs: selection of the aE-image by such a power and rigidity
of the bE,cE-images after aE maps to dE. Involutivity supplies the dE-image.
The final theorem discharges both inputs using the five-point orbit and the
intrinsic triple-commutator tensor, producing the oriented involution on the
original frame without any coordinate change.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, centralizer-generator paragraph, and p.681, equation (23).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Assemble the oriented action on the original frame once the power-selection
and rigidity obligations have been discharged. The seed is constructed here;
it is not supplied as an existence assumption. -/
public theorem ParrottSylowGeneratorData.exists_outer_involution_core_action_of_orientation
    (f : ParrottSylowGeneratorData n) [Finite G]
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ r : G, r ∈ H → r ∉ e.sylow → r ^ 2 = 1 → (r * f.y) ^ 5 = 1 →
      ∃ i : Fin 4, f.d⁻¹ *
        (((f.x ^ i.val)⁻¹ * r * f.x ^ i.val)⁻¹ * f.a *
          ((f.x ^ i.val)⁻¹ * r * f.x ^ i.val)) ∈ E) →
    (∀ r : G, r ∈ H → r ^ 2 = 1 → f.d⁻¹ * (r⁻¹ * f.a * r) ∈ E →
      (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ E ∧
      (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈ E) →
    ∃ r : G, r ∈ H ∧ r ∉ e.sylow ∧ r ^ 2 = 1 ∧ (r * f.y) ^ 5 = 1 ∧
      f.d⁻¹ * (r⁻¹ * f.a * r) ∈ E ∧
      (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ E ∧
      (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈ E ∧
      f.a⁻¹ * (r⁻¹ * f.d * r) ∈ E := by
  dsimp only
  intro hselect hrigid
  obtain ⟨r, hrH, hrT, hrorder, _, hry, _⟩ := f.exists_outer_involution_fifth_power h
  have hr : r ^ 2 = 1 := hrorder ▸ pow_orderOf_eq_one r
  obtain ⟨i, hi⟩ := hselect r hrH hrT hr hry
  obtain ⟨hrH', hrT', hr', hry'⟩ := f.core_orientation_seed_xpow r i.val hrH hrT hr hry
  obtain ⟨hb, hc⟩ := hrigid _ hrH' hr' hi
  exact ⟨_, hrH', hrT', hr', hry', hi, hb, hc,
    f.core_orientation_d_image_of_a_image _ hrH' hr' hi⟩

/-- An actual outer involution has Parrott's full oriented action on the core
abelianization and satisfies the fifth-power relation with the supplied y.
The original Sylow frame is retained literally. -/
public theorem ParrottSylowGeneratorData.exists_outer_involution_core_action
    (f : ParrottSylowGeneratorData n) [Finite G]
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ r : G, r ∈ H ∧ r ∉ e.sylow ∧ r ^ 2 = 1 ∧ (r * f.y) ^ 5 = 1 ∧
      f.d⁻¹ * (r⁻¹ * f.a * r) ∈ E ∧
      (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ E ∧
      (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈ E ∧
      f.a⁻¹ * (r⁻¹ * f.d * r) ∈ E := by
  exact f.exists_outer_involution_core_action_of_orientation h
    (f.core_orientation_first_image_xpow h)
    (f.core_orientation_remaining_images h)

end Stellmacher.Recognition
