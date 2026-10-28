module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation

/-!
# Central norms for the minus extraspecial five-point action

This certificate uses the existing five-bit multiplication and generator-word
encoding. It checks all generator images satisfying the quaternion and dihedral
relations. If the resulting action is involutive and moves four singular points,
no twisted norm is the nonidentity central element (bit 1).

The pruning and coordinates follow `MinusExtraspecialA5Fusion.Calculation`.
The exploratory Python check in the parent task is not used as evidence by Lean:
`decide +kernel` proves the complete finite statement. A representative first
image took 52.5 seconds and 2.0 GB peak RSS including imports; the full check took
165.8 seconds and 4.6 GB. The certificate is compiled once and reused by the
model transport and source application.

Source: Aschbacher, *Sporadic Groups* (1994), the w = 2 argument of 46.8,
46.11, and the local five-normalizer assertion in 47.1, printed pp.253–260.
-/

@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.Reflection
open Outside

def calculation (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → Outside.invol u v r s → moved u v r s = 4 →
  ∀ d : B, mul d (word u v r s d) ≠ 2
set_option synthInstance.maxSize 1024 in
instance (u : B) : Decidable (calculation u) := by unfold calculation; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calculation_all : ∀ u : B, calculation u := by decide +kernel
end MinusExtraspecial.FixedFourCalculation.Reflection
