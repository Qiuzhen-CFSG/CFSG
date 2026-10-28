module
public import Theory.SpecificGroups.MinusExtraspecial.ModelFixedFourCalculation
/-!
# Cocycle calculation for the minus extraspecial group

Use the five-bit multiplication and generator-word encoding of
`MinusExtraspecial.ModelFixedFourCalculation`. For involutive automorphisms
moving four of the five singular points, every twisted cocycle is a
coboundary. The generator relations prune the finite check before testing
involutivity, the action on singular points, and the cocycles.

This is the finite model calculation for Aschbacher, *Sporadic Groups*
(1994), Lemma 46.11, printed p.255. The companion `Model` module relates
every test to the actual group and its intrinsic action; no unverified
external enumeration is used in the proof.
-/

@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.Outside
open FixedFourCalculation

def points : List B := [8,16,25,28,29]
def invol (u v r s : B) : Bool :=
  gens.all fun g => word u v r s (word u v r s g) == g
def moved (u v r s : B) : Nat :=
  points.countP fun x => (word u v r s x &&& 29) != x

def calculation (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → invol u v r s → moved u v r s = 4 →
  ∀ d : B, mul d (word u v r s d) = 0 →
    ∃ q : B, d = mul q (inv (word u v r s q))
set_option synthInstance.maxSize 1024 in
instance (u : B) : Decidable (calculation u) := by unfold calculation; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calculation_all : ∀ u : B, calculation u := by decide +kernel
end MinusExtraspecial.FixedFourCalculation.Outside
