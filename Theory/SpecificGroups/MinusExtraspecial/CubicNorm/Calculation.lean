module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation

/-!
# Norm-four certificate for a cubic inverter

Use the established five-bit coordinates for Q₈ ∘ D₈. The standard cubic
cycles the quaternion factor and fixes the two reflection generators.
For an involution reversing that cubic and moving four singular points,
the norm of the first reflection has nonidentity square.

Reversal determines the second quaternion generator image from the first.
This removes one 32-element search dimension before checking the relations.
The last group of implications has a separate decidability instance so
instance synthesis does not expand the whole nested decision tree.
Only kernel reduction certifies the finite calculation.

Source: Aschbacher, *Sporadic Groups* (1994), the local-normalizer step
in 47.3, p.262, and the quaternion–dihedral coordinates on p.265.
-/

@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.CubicNorm
open Outside

def cycleBits (x : B) : B := word 5 3 8 16 x

def second (u : B) : B := mul (cycleBits (cycleBits u)) (inv u)

def reverses (u v r s : B) : Bool :=
  gens.all fun g => word u v r s (cycleBits g) == cycleBits (cycleBits (word u v r s g))

def lastConditions (u v r s : B) : Prop :=
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → Outside.invol u v r s →
  moved u v r s = 4 → reverses u v r s →
    mul (mul 8 r) (mul 8 r) ≠ 0
set_option synthInstance.maxSize 1024 in
instance lastConditionsDecidable (u v r s : B) : Decidable (lastConditions u v r s) := by
  unfold lastConditions
  infer_instance

def candidate (u v : B) : Prop :=
  mul u u ≠ 0 →
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  lastConditions u v r s
set_option synthInstance.maxSize 1024 in
instance candidateDecidable (u v : B) : Decidable (candidate u v) := by
  unfold candidate
  infer_instance

def calculation (u : B) : Prop := candidate u (second u)
instance (u : B) : Decidable (calculation u) := candidateDecidable u (second u)

theorem calculation_all : ∀ u : B, calculation u := by decide +kernel

end MinusExtraspecial.FixedFourCalculation.CubicNorm
