module

public import Stellmacher.Recognition.Parrott.CentralizerActionParameters

/-!
# Centralizer action parameters compatible with the core commutators

The second alternative for aʳ requires a corresponding change in the u
coefficient of cʳ. Transporting [b,c] = uv forces that coefficient to be
α xor β; see `c_action_exponent_constraint` in CentralizerFiniteActionFamily.
This interface records that corrected family without changing the earlier
`HasActionParameters` API. For β = false the interfaces agree, and their
distinguished values give the unprimed equations (23).

Parameter existence and normalization of the entire Sylow frame remain
separate proof obligations. In particular, this definition asserts neither.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, the alternatives preceding (23). The corrected coefficient
is dictated by the checked Sylow commutators, rather than taken from (23′).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottCentralizerInvolutionData

/-- Candidate core images with the c-image coefficient forced by [b,c] = uv. -/
@[expose] public def HasCompatibleActionParameters (f : ParrottCentralizerInvolutionData n)
    (α β δ γ : Bool) : Prop :=
  f.r⁻¹ * f.a * f.r = f.d * f.u ^ α.toNat * n.v ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.d * f.r = f.a * f.u ^ (α.xor β).toNat * n.v ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.c * f.r = f.c * f.d * f.a * f.w ^ β.toNat * f.u ^ (α.xor β).toNat *
    n.t ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.b * f.r = f.d * f.c * f.b * f.w ^ (!α).toNat *
    (n.v * n.t) ^ (α.xor β).toNat * z ^ γ.toNat

/-- The first alternative agrees with the original parameter interface. -/
public theorem compatible_action_parameters_false_iff (f : ParrottCentralizerInvolutionData n)
    (α δ γ : Bool) :
    f.HasCompatibleActionParameters α false δ γ ↔ f.HasActionParameters α false δ γ := by
  simp only [HasCompatibleActionParameters, HasActionParameters, Bool.xor_false]

/-- The distinguished compatible parameters give the actual unprimed action. -/
public def toActionDataOfCompatibleParameters (f : ParrottCentralizerInvolutionData n)
    (hp : f.HasCompatibleActionParameters true false false false) :
    ParrottCentralizerActionData n :=
  f.toActionDataOfParameters ((f.compatible_action_parameters_false_iff true false false).mp hp)

end ParrottCentralizerInvolutionData
end Stellmacher.Recognition
