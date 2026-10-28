module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeed

/-!+# Assembly of Parrott's normalizer generator

Once the conjugation and cubic equations have been established on the supplied
centralizer coordinates, the actual normalizer order proves generation and the
original-core fusion proves the required involution class. This module assembles
those consequences without adding generation or fusion to the equation inputs.

The construction of a reduced candidate and the proof of its remaining
equations are separate obligations. The constructor below is conditional on
those equations and does not assert unconditional existence of the generator.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.681–682, equations (25)–(26).
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottCentralizerGeneratorData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Complete the structural fields from the local equations. The resulting
normalizer generator is literally the supplied element s. -/
public def normalizerGeneratorDataOfEquations (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) (s : G)
    (hsN : s ∈ normalizer (e.F : Set G)) (hs : s ^ 2 = 1)
    (hts : s⁻¹ * n.t * s = z)
    (hvs : s⁻¹ * n.v * s = n.v * n.t * z)
    (hys : s⁻¹ * f.y * s = f.w * f.u * n.v * z)
    (hws : s⁻¹ * f.w * s = f.y * f.a * n.v * z)
    (has : s⁻¹ * f.a * s = f.u)
    (hbs : s⁻¹ * f.b * s = f.b * f.a * f.u * n.v * z)
    (hcs : s⁻¹ * f.c * s = f.x * f.y * f.a * f.u * n.v * n.t)
    (hxs : s⁻¹ * f.x * s = f.c * f.a * f.w * n.t * z)
    (hcube : (s * f.d * n.v * z) ^ 3 = 1) : ParrottNormalizerGeneratorData f where
  s := s
  normalizer_generators := n.normalizer_generated_of_t_conjugate h s hsN hts
  s_order := orderOf_eq_prime_iff.mpr ⟨hs, by
    intro heq
    have htz : n.t = z := by simpa only [heq, inv_one, one_mul, mul_one] using hts
    exact n.t_not_mem_zpowers (by rw [htz]; exact mem_zpowers z)⟩
  s_conjugate := f.toParrottSylowGeneratorData.isConj_v_of_cube h s hs hcube
  s_sq := hs
  eq25_ts := hts
  eq25_vs := hvs
  eq25_ys := hys
  eq25_ws := hws
  eq25_as := has
  eq25_bs := hbs
  eq25_cs := hcs
  eq25_xs := hxs
  eq26 := hcube

end Stellmacher.Recognition.ParrottCentralizerGeneratorData
