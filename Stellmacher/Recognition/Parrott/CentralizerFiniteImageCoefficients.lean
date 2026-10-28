module

public import Stellmacher.Recognition.Parrott.CentralizerFiniteActionFamily
public import Stellmacher.Recognition.Parrott.CentralizerCommutatorCoefficients

/-!
# Finite image coefficients for the centralizer involution

The involution-stage action has four core images.  The a-image has the
four-coordinate form supplied by `a_image_four_coefficients`; involutivity then
gives the corrected d-image formula.  The two remaining core discrepancies lie
in the actual derived subgroup, so `derived_binary_expansion` gives their five
Boolean coefficients in the fixed ordered frame `(w,u,v,t,z)`.  This wrapper
keeps all coordinates from the supplied `ParrottCentralizerInvolutionData` and
does not introduce the older action-parameter interface.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680--681, equations (20)--(22) and the alternatives preceding (23).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottCentralizerInvolutionData

/-- The four images admit a finite Boolean coefficient description in the
fixed supplied frame.  The d-row is the involutivity-corrected row. -/
public theorem finite_image_coefficients [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ ω α β δ : Bool,
      ∃ p q r s t i j k l m : Bool,
        f.r⁻¹ * f.a * f.r =
            f.d * f.w ^ ω.toNat * f.u ^ α.toNat * n.v ^ β.toNat * z ^ δ.toNat ∧
        f.r⁻¹ * f.d * f.r =
            f.a * f.u ^ (α.xor β).toNat * n.v ^ (ω.xor β).toNat *
              n.t ^ ω.toNat * z ^ (ω.xor δ).toNat ∧
        f.r⁻¹ * f.b * f.r =
            f.d * f.c * f.b * f.w ^ p.toNat * f.u ^ q.toNat *
              n.v ^ r.toNat * n.t ^ s.toNat * z ^ t.toNat ∧
        f.r⁻¹ * f.c * f.r =
            f.c * f.d * f.a * f.w ^ i.toNat * f.u ^ j.toNat *
              n.v ^ k.toNat * n.t ^ l.toNat * z ^ m.toNat := by
  obtain ⟨α, β, κ, δ, ha⟩ := f.a_image_four_coefficients h
  obtain ⟨_, hbE, hcE, _⟩ := f.core_images_mod_derived h
  obtain ⟨p, q, r, s, t, hbexp⟩ := f.derived_binary_expansion h hbE
  obtain ⟨i, j, k, l, m, hcexp⟩ := f.derived_binary_expansion h hcE
  have hd := f.d_image_of_a_four_coefficients α β κ δ ha
  have hb : f.r⁻¹ * f.b * f.r =
      f.d * f.c * f.b * f.w ^ p.toNat * f.u ^ q.toNat *
        n.v ^ r.toNat * n.t ^ s.toNat * z ^ t.toNat := by
    calc
      f.r⁻¹ * f.b * f.r = (f.d * f.c * f.b) *
          ((f.d * f.c * f.b)⁻¹ * (f.r⁻¹ * f.b * f.r)) := by group
      _ = (f.d * f.c * f.b) *
          (f.w ^ p.toNat * f.u ^ q.toNat * n.v ^ r.toNat *
            n.t ^ s.toNat * z ^ t.toNat) := by rw [hbexp]
      _ = f.d * f.c * f.b * f.w ^ p.toNat * f.u ^ q.toNat *
          n.v ^ r.toNat * n.t ^ s.toNat * z ^ t.toNat := by
        simp only [mul_assoc]
  have hc : f.r⁻¹ * f.c * f.r =
      f.c * f.d * f.a * f.w ^ i.toNat * f.u ^ j.toNat *
        n.v ^ k.toNat * n.t ^ l.toNat * z ^ m.toNat := by
    calc
      f.r⁻¹ * f.c * f.r = (f.c * f.d * f.a) *
          ((f.c * f.d * f.a)⁻¹ * (f.r⁻¹ * f.c * f.r)) := by group
      _ = (f.c * f.d * f.a) *
          (f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat *
            n.t ^ l.toNat * z ^ m.toNat) := by rw [hcexp]
      _ = f.c * f.d * f.a * f.w ^ i.toNat * f.u ^ j.toNat *
          n.v ^ k.toNat * n.t ^ l.toNat * z ^ m.toNat := by
        simp only [mul_assoc]
  exact ⟨α, β, κ, δ, p, q, r, s, t, i, j, k, l, m, ha, hd, hb, hc⟩

/-- The corrected finite coefficient certificate.  The commutator table and
involutivity reduce the four rows to seven Boolean coefficients; the supplied
fifth-power relation is retained in the certificate for downstream case
elimination. -/
public theorem finite_corrected_image_coefficients [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ i j k m jb mb mc : Bool,
      f.r⁻¹ * f.a * f.r =
          f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat ∧
      f.r⁻¹ * f.d * f.r =
          f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat *
            n.t ^ i.toNat * z ^ (i.xor m).toNat ∧
      f.r⁻¹ * f.b * f.r =
          f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ jb.toNat *
            n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat ∧
      f.r⁻¹ * f.c * f.r =
          f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (jb.xor (j.xor k)).toNat *
            n.v ^ i.toNat * n.t ^ (i.xor k).toNat * z ^ mc.toNat ∧
      (f.r * f.y) ^ 5 = 1 := by
  obtain ⟨i, j, k, m, jb, mb, mc, ha, hd, hb, hc⟩ :=
    f.core_image_seven_coefficients h
  exact ⟨i, j, k, m, jb, mb, mc, ha, hd, hb, hc, f.eq20_ry⟩

end ParrottCentralizerInvolutionData
end Stellmacher.Recognition
