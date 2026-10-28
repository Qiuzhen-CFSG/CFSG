module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData

/-!
# Stages of the centralizer generator construction

The involution stage records equations (20)–(22) on a normalized Sylow
frame. The action stage also records the unprimed equations (23). Neither
stage asserts existence. Both retain the supplied second elementary subgroup
and normalizer-fusion witnesses, so F,T,z,t,v remain the actual original
objects. The Sylow coordinates may change when the action is normalized.

These interfaces separate the geometric choice of the outer involution from
the subsequent changes of coordinates and the word calculation giving (24).
The recognition owner must construct both stages from the original hypotheses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, including the alternatives preceding (23) and (23′).
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}

/-- The actual centralizer involution, with its action on the elementary
derived subgroup normalized as in equations (20)–(22). -/
public structure ParrottCentralizerInvolutionData (n : ParrottNormalizerFusionData e)
    extends ParrottSylowGeneratorData n where
  r : G
  centralizer_generators : (e.sylow : Subgroup G) ⊔ zpowers r = centralizer ({z} : Set G)
  r_order : orderOf r = 2
  r_conjugate : IsConj r z
  comm_zr : Commute z r
  eq20_r : r ^ 2 = 1
  eq20_ry : (r * y) ^ 5 = 1
  eq20_tr : r⁻¹ * n.t * r = w * u * n.v * z
  eq21_vr : r⁻¹ * n.v * r = u * n.v
  eq22_ur : r⁻¹ * u * r = u
  eq22_wr : r⁻¹ * w * r = n.v * n.t * z

/-- A fully normalized action on the original core. Equation (24) is an
output of the discrepancy calculation, rather than part of this input. -/
public structure ParrottCentralizerActionData (n : ParrottNormalizerFusionData e)
    extends ParrottCentralizerInvolutionData n where
  eq23_ar : r⁻¹ * a * r = d * u
  eq23_dr : r⁻¹ * d * r = a * u
  eq23_cr : r⁻¹ * c * r = c * d * a * u
  eq23_br : r⁻¹ * b * r = d * c * b * n.v * n.t

end Stellmacher.Recognition
