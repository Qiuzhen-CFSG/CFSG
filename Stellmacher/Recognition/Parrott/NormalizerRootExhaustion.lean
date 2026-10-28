module

public import Stellmacher.Recognition.Parrott.NormalizerRootCenters
public import Stellmacher.Recognition.Parrott.NormalizerRootCosetCounts
public import Stellmacher.Recognition.Parrott.NormalizerRootGeometry

/-!
# Assembly of Parrott's root exhaustion and involution census

The elementary-coset equivalences count eight roots in each of mF and m⁻¹F
once |C_F(m)| = 8. If m² is outside F and these two cosets exhaust the
core root fiber, the total is sixteen. The involution-image inclusion is
proved in `NormalizerRootSets`; a lower census of sixteen images therefore
identifies that image set with the whole root fiber.
The central generator required for each outside involution is constructed
in `NormalizerRootCenters`, using Sylow conjugacy and the known Sylow center.

The general two-coset geometry is proved in `NormalizerRootGeometry`, so
the three root counts below hold unconditionally for the supplied frame.
The separate involution-image equality is only a conditional saturation
lemma: no lower bound on that image set is asserted here.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The three root counts from the exact local geometric conditions.
The covering assertion is an explicit premise, not inferred from the two
individual coset counts. -/
public theorem normalizer_root_counts_of_two_cosets
    (e : ParrottSecondElementaryData z) (m : G)
    (hm : m ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype)
    (hfour : m ^ 4 = 1) (hsq : m ^ 2 ∉ e.F)
    (hcentral : Nat.card (e.F ⊓ centralizer ({m} : Set G) : Subgroup G) = 8)
    (hcover : ∀ g ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype,
      g ^ 2 = m ^ 2 → m⁻¹ * g ∈ e.F ∨ m * g ∈ e.F) :
    (e.normalizerCoreRoots m).ncard = 16 ∧
      {g : G | m⁻¹ * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 ∧
      {g : G | m * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 := by
  let _ := e.elementary
  refine ⟨?_, ?_, ?_⟩
  · change {g : G | g ∈ (pCore 2 (normalizer (e.F : Set G))).map
        (normalizer (e.F : Set G)).subtype ∧ g ^ 2 = m ^ 2}.ncard = 16
    rw [ncard_square_roots_of_two_cosets e.F _ e.le_normalizer_core m hm hfour hsq
      hcover, hcentral]
  · rw [ncard_square_coset, hcentral]
  · rw [ncard_square_inverse_coset e.F m hfour, hcentral]

/-- A sixteen-image lower census saturates a sixteen-root fiber, giving the
precise source orbit-set equality including its central twists. -/
public theorem normalizerRootInvolutionImages_eq_of_census
    (e : ParrottSecondElementaryData z) (m : G)
    (hm : m ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype)
    (hfour : m ^ 4 = 1)
    (hroots : (e.normalizerCoreRoots m).ncard = 16)
    (himages : 16 ≤ (e.normalizerRootInvolutionImages m).ncard) :
    e.normalizerCoreRoots m = e.normalizerRootInvolutionImages m := by
  symm
  apply Set.eq_of_subset_of_ncard_le
    (e.normalizerRootInvolutionImages_subset m hm hfour)
  rwa [hroots]

end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Every order-four element outside omega has sixteen square roots in the
normalizer core, eight in each of its two elementary cosets. The ordered-word
geometry discharges both the covering and centralizer-count hypotheses. -/
public theorem ParrottSylowGeneratorData.normalizer_root_counts
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    let U := (omega₁ (pCore 2 N) (p := 2)).map (N.subtype.comp (pCore 2 N).subtype)
    ∀ m ∈ K, m ∉ U → orderOf m = 4 →
      (e.normalizerCoreRoots m).ncard = 16 ∧
        {g : G | m⁻¹ * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 ∧
        {g : G | m * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 := by
  intro N K U m hm hU ho
  obtain ⟨hsq, hc, hcover⟩ := f.normalizer_root_geometry h m hm hU ho
  exact e.normalizer_root_counts_of_two_cosets m hm
    (by simpa only [ho] using pow_orderOf_eq_one m) hsq hc hcover

/-- The complete sixteen-root census for the literal supplied centralizer
frame, without an orbit-image or normalizer-seed assumption. -/
public theorem ParrottCentralizerGeneratorData.normalizer_root_counts
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    let U := (omega₁ (pCore 2 N) (p := 2)).map (N.subtype.comp (pCore 2 N).subtype)
    ∀ m ∈ K, m ∉ U → orderOf m = 4 →
      (e.normalizerCoreRoots m).ncard = 16 ∧
        {g : G | m⁻¹ * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 ∧
        {g : G | m * g ∈ e.F ∧ g ^ 2 = m ^ 2}.ncard = 8 :=
  f.toParrottSylowGeneratorData.normalizer_root_counts h

end Stellmacher.Recognition
