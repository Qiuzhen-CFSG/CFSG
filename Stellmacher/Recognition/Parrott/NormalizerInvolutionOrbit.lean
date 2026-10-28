module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionOrbitCensus

/-!
# Saturation of the eight-element involution image set

The upper bound in wF and a lower census of involution images in
T₂ = ⟨s₀,K⟩ imply equality of these finite sets. In particular, wuvz,
which is conjugate to y by the supplied centralizer frame, is reached
by an involution in the actual normalizer. The lower census constructs
eight distinct images by conjugating the supplied reflection by x and a;
the final theorems discharge the census premise and retain every supplied
coordinate. No construction of the initial reflection is assumed here.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, “Generators and relations for N”.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The eight involution images saturate all of the y-class in wF. -/
public theorem ParrottCentralizerGeneratorData.secondSylowInvolutionImages_eq_of_census
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (s₀ : G) (hcensus : 8 ≤ (f.secondSylowInvolutionImages s₀).ncard) :
    f.secondSylowInvolutionImages s₀ =
      {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} := by
  have hsub : f.secondSylowInvolutionImages s₀ ⊆
      {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} := by
    rintro g ⟨hcos, s, _, _, _, hs⟩
    exact ⟨hcos, isConj_iff.mpr ⟨s⁻¹, by simpa only [inv_inv] using hs⟩⟩
  exact Set.eq_of_subset_of_ncard_le hsub
    ((f.w_coset_y_class_ncard_le_eight h).trans hcensus)

/-- Select the exact required image of y from the lower involution census.
The supplied F, fusion data and centralizer coordinates are unchanged. -/
public theorem ParrottCentralizerGeneratorData.exists_normalizer_involution_of_census
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (s₀ : G) (hs₀N : s₀ ∈ normalizer (e.F : Set G))
    (hcensus : 8 ≤ (f.secondSylowInvolutionImages s₀).ncard) :
    ∃ s : G, s ∈ normalizer (e.F : Set G) ∧ s ^ 2 = 1 ∧
      s⁻¹ * f.y * s = f.w * f.u * n.v * z := by
  have huF : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hR : f.w * f.u * n.v * z ∈ f.secondSylowInvolutionImages s₀ := by
    rw [f.secondSylowInvolutionImages_eq_of_census h s₀ hcensus]
    refine ⟨?_, f.y_isConj_wuvz⟩
    simpa only [mul_assoc, inv_mul_cancel_left] using
      e.F.mul_mem (e.F.mul_mem huF n.v_mem_inf.2) e.z_mem_inf.2
  obtain ⟨_, s, hsT₂, _, hs, hy⟩ := hR
  have hT₂N : (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype ⊔ zpowers s₀ ≤
        normalizer (e.F : Set G) :=
    sup_le (map_subtype_le _) (zpowers_le.mpr hs₀N)
  exact ⟨s, hT₂N hsT₂, hs, hy⟩

/-- For every supplied reflection moving yF to wF, the involution image
set in its second Sylow subgroup has exactly eight elements. -/
public theorem ParrottCentralizerGeneratorData.secondSylowInvolutionImages_ncard
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (s₀ : G) (hs₀T : s₀ ∉ (e.sylow : Subgroup G)) (hs₀ : s₀ ^ 2 = 1)
    (hcos : f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F) :
    (f.secondSylowInvolutionImages s₀).ncard = 8 := by
  have hlow := f.secondSylowInvolutionImages_ncard_ge_eight h s₀ hs₀T hs₀ hcos
  apply le_antisymm _ hlow
  rw [f.secondSylowInvolutionImages_eq_of_census h s₀ hlow]
  exact f.w_coset_y_class_ncard_le_eight h

/-- All ambient y-conjugates in wF are reached by involutions outside K
in the literal subgroup ⟨s₀,K⟩. -/
public theorem ParrottCentralizerGeneratorData.secondSylowInvolutionImages_eq
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (s₀ : G) (hs₀T : s₀ ∉ (e.sylow : Subgroup G)) (hs₀ : s₀ ^ 2 = 1)
    (hcos : f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F) :
    f.secondSylowInvolutionImages s₀ =
      {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} :=
  f.secondSylowInvolutionImages_eq_of_census h s₀
    (f.secondSylowInvolutionImages_ncard_ge_eight h s₀ hs₀T hs₀ hcos)

/-- Select the exact required image from any supplied normalizer reflection.
All hypotheses about simplicity and N₂ have already been discharged in
the supplied frame and fusion data; this selection needs only those data. -/
public theorem ParrottCentralizerGeneratorData.exists_normalizer_involution_y_image
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (s₀ : G) (hs₀N : s₀ ∈ normalizer (e.F : Set G))
    (hs₀T : s₀ ∉ (e.sylow : Subgroup G)) (hs₀ : s₀ ^ 2 = 1)
    (hcos : f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F) :
    ∃ s : G, s ∈ normalizer (e.F : Set G) ∧ s ^ 2 = 1 ∧
      s⁻¹ * f.y * s = f.w * f.u * n.v * z :=
  f.exists_normalizer_involution_of_census h s₀ hs₀N
    (f.secondSylowInvolutionImages_ncard_ge_eight h s₀ hs₀T hs₀ hcos)

end Stellmacher.Recognition
