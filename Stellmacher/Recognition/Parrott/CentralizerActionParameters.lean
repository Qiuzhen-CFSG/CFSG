module

public import Stellmacher.Recognition.Parrott.CentralizerActionData

/-!
# A finite interface for the remaining centralizer action

The four binary parameters separate the two noncentral choices of the core
action from its two central signs. The first two parameters encode the u- and
v-factors in aʳ; the last two encode its z-factor and the z-factor in bʳ.
The special values (true,false,false,false) give exactly the unprimed (23).

This module defines the interface and checks that special case. It does not
assert that an arbitrary involution frame has these parameters or that the
other cases admit a compatible change of the entire Sylow frame. Those are
separate obligations, allowing the finite calculation and the coordinate
changes to be proved independently.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, the alternatives preceding (23). The formula for bʳ follows
the displayed expression preceding (23); the literal v in the final entry
of printed (23′) is not assumed as a relation here.
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottCentralizerInvolutionData

/-- An explicit finite family of candidate actions. Existence of these
parameters is a theorem to be proved from the involution-stage data. -/
@[expose] public def HasActionParameters (f : ParrottCentralizerInvolutionData n)
    (α β δ γ : Bool) : Prop :=
  f.r⁻¹ * f.a * f.r = f.d * f.u ^ α.toNat * n.v ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.d * f.r = f.a * f.u ^ (α.xor β).toNat * n.v ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.c * f.r = f.c * f.d * f.a * f.w ^ β.toNat * f.u ^ α.toNat *
    n.t ^ β.toNat * z ^ δ.toNat ∧
  f.r⁻¹ * f.b * f.r = f.d * f.c * f.b * f.w ^ (!α).toNat *
    (n.v * n.t) ^ (α.xor β).toNat * z ^ γ.toNat

/-- The distinguished parameter values are the four unprimed equations (23). -/
public def toActionDataOfParameters (f : ParrottCentralizerInvolutionData n)
    (hp : f.HasActionParameters true false false false) :
    ParrottCentralizerActionData n where
  toParrottCentralizerInvolutionData := f
  eq23_ar := by simpa only [HasActionParameters, Bool.toNat_true, Bool.toNat_false,
    pow_one, pow_zero, mul_one] using hp.1
  eq23_dr := by simpa using hp.2.1
  eq23_cr := by simpa using hp.2.2.1
  eq23_br := by simpa [mul_assoc] using hp.2.2.2

end ParrottCentralizerInvolutionData
end Stellmacher.Recognition
