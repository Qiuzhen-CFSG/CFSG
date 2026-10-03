module

public import Stellmacher.Recognition.Parrott.CentralizerFiniteActionFamily

/-!
# Binary coefficients of the transported core images

The rigidity theorem identifies the four transported core generators modulo the
actual derived subgroup.  The derived subgroup is elementary abelian on the
ordered tail `w,u,v,t,z`; expanding each error therefore gives a finite binary
coefficient certificate.  The theorem below keeps the supplied frame and
records the certificate explicitly.  The later compatibility calculation may
specialize these coefficients (in particular, the c-image u coefficient is
the xor of the two coefficients occurring in the a-image).

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.680--681, equations (20)--(23).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottCentralizerInvolutionData

set_option maxHeartbeats 400000 in
/-- The four core images admit ordered binary expansions of their derived
errors.  This is the coefficient-level form of `core_images_mod_derived` and
does not alter any of the supplied Sylow or normalizer data. -/
public theorem core_image_binary_coefficients [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ ia ja ka la ma ib jb kb lb mb ic jc kc lc mc id jd kd ld md : Bool,
      f.r⁻¹ * f.a * f.r =
          f.d * f.w ^ ia.toNat * f.u ^ ja.toNat * n.v ^ ka.toNat *
            n.t ^ la.toNat * z ^ ma.toNat ∧
      f.r⁻¹ * f.b * f.r =
          f.d * f.c * f.b * f.w ^ ib.toNat * f.u ^ jb.toNat * n.v ^ kb.toNat *
            n.t ^ lb.toNat * z ^ mb.toNat ∧
      f.r⁻¹ * f.c * f.r =
          f.c * f.d * f.a * f.w ^ ic.toNat * f.u ^ jc.toNat * n.v ^ kc.toNat *
            n.t ^ lc.toNat * z ^ mc.toNat ∧
      f.r⁻¹ * f.d * f.r =
          f.a * f.w ^ id.toNat * f.u ^ jd.toNat * n.v ^ kd.toNat *
            n.t ^ ld.toNat * z ^ md.toNat := by
  obtain ⟨ha, hb, hc, hd⟩ := f.core_images_mod_derived h
  obtain ⟨ia, ja, ka, la, ma, hia⟩ := f.derived_binary_expansion h ha
  obtain ⟨ib, jb, kb, lb, mb, hib⟩ := f.derived_binary_expansion h hb
  obtain ⟨ic, jc, kc, lc, mc, hic⟩ := f.derived_binary_expansion h hc
  obtain ⟨id, jd, kd, ld, md, hid⟩ := f.derived_binary_expansion h hd
  refine ⟨ia, ja, ka, la, ma, ib, jb, kb, lb, mb, ic, jc, kc, lc, mc,
    id, jd, kd, ld, md, ?_⟩
  have ha' := congrArg (fun q : G => f.d * q) hia
  have hb' := congrArg (fun q : G => f.d * f.c * f.b * q) hib
  have hc' := congrArg (fun q : G => f.c * f.d * f.a * q) hic
  have hd' := congrArg (fun q : G => f.a * q) hid
  constructor
  · simpa only [mul_assoc, mul_inv_cancel_left] using ha'
  constructor
  · simpa only [mul_assoc, mul_inv_cancel_left] using hb'
  constructor
  · simpa only [mul_assoc, mul_inv_cancel_left] using hc'
  · simpa only [mul_assoc, mul_inv_cancel_left] using hd'

set_option maxHeartbeats 400000 in
/-- The a- and d-images can be recorded with the shorter four-coefficient
forms.  The second equation is the involutivity calculation for `r`; the
remaining b- and c-errors are still supplied by the five-bit certificate
above. -/
public theorem core_image_binary_coefficients_with_involutivity [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ ia ja ka ma ib jb kb lb mb ic jc kc lc mc : Bool,
      f.r⁻¹ * f.a * f.r =
          f.d * f.w ^ ia.toNat * f.u ^ ja.toNat * n.v ^ ka.toNat * z ^ ma.toNat ∧
      f.r⁻¹ * f.d * f.r =
          f.a * f.u ^ (ja.xor ka).toNat * n.v ^ (ia.xor ka).toNat *
            n.t ^ ia.toNat * z ^ (ia.xor ma).toNat ∧
      f.r⁻¹ * f.b * f.r =
          f.d * f.c * f.b * f.w ^ ib.toNat * f.u ^ jb.toNat * n.v ^ kb.toNat *
            n.t ^ lb.toNat * z ^ mb.toNat ∧
      f.r⁻¹ * f.c * f.r =
          f.c * f.d * f.a * f.w ^ ic.toNat * f.u ^ jc.toNat * n.v ^ kc.toNat *
            n.t ^ lc.toNat * z ^ mc.toNat ∧
      (f.r * f.y) ^ 5 = 1 := by
  obtain ⟨ia, ja, ka, ma, ha⟩ := f.a_image_four_coefficients h
  obtain ⟨_, _, _, _, _, ib, jb, kb, lb, mb, ic, jc, kc, lc, mc, _, _, _, _, _, hbc⟩ :=
    f.core_image_binary_coefficients h
  have hd := f.d_image_of_a_four_coefficients ia ja ka ma ha
  exact ⟨ia, ja, ka, ma, ib, jb, kb, lb, mb, ic, jc, kc, lc, mc,
    ha, hd, hbc.2.1, hbc.2.2.1, f.eq20_ry⟩

end ParrottCentralizerInvolutionData
end Stellmacher.Recognition
