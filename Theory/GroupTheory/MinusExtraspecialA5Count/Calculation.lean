module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation
/-!
# Local counts for a minus-extraspecial A₅ extension

For an involutive automorphism moving four singular points, there are eight
involution cocycles and eight core involutions whose product with an outside
involution has the central involution in its rotation subgroup. The latter
test uses the square of that product, namely `d * a d`, in the actual core.

The certificate uses the existing five-bit coordinates and prunes generator
images by their defining relations. The companion model module transports
these finite tests to the actual group; no ambient group order is assumed.
Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.259.
-/

@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.Outside.Count
open MinusExtraspecial.FixedFourCalculation MinusExtraspecial.FixedFourCalculation.Outside

def cocycles (u v r s : B) : Nat :=
  all.countP fun d => mul d (word u v r s d) == 0

def compatible (u v r s : B) : Nat :=
  all.countP fun d => mul d d == 0 && d != 0 &&
    (mul d (word u v r s d) == 2 ||
      mul (mul d (word u v r s d)) (mul d (word u v r s d)) == 2)

def calculation (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → invol u v r s → moved u v r s = 4 →
  cocycles u v r s = 8 ∧ compatible u v r s = 8
set_option synthInstance.maxSize 1024 in
instance (u : B) : Decidable (calculation u) := by unfold calculation; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calculation_all : ∀ u : B, calculation u := by decide +kernel
end MinusExtraspecial.FixedFourCalculation.Outside.Count
