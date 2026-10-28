module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights

/-!
# Character pullback through the left embedding

These are formal transport lemmas for actual torus morphisms. Finite geometry
producers must supply their raw torus restriction equations; no representation
conclusion is an input. Coordinate pullback retains the chosen forward or
inverse permutation, and power pullback multiplies coordinates.
Source: GLS3 2.8.3--4, with the convention bridge from Steinberg (6.1).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.LeftWeights
universe u
variable {k : Type u} [Field k]
variable {T : Variety k} [AlgebraicGroup T]

theorem character_pow_point (χ : TorusCharacter T) (n : ℕ) (t : Variety.Point T) :
    (χ ^ n).pointCharacter t = χ.pointCharacter t ^ n := by
  induction n with
  | zero =>
    change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = _
    rw [dPointEquiv_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    change (dPointEquiv 1 ((χ ^ n).onPoints t * χ.onPoints t) 0 : k) = _
    rw [dPointEquiv_mul]
    change (χ ^ n).pointCharacter t * χ.pointCharacter t = _
    rw [ih, pow_succ]

/-- A raw pullback equation for all weights transports through negation. -/
theorem pullback_embedding_of_raw (e : Multiplicative Weight ≃* TorusCharacter T)
    (f : Theory.AlgebraicGroup.Morphism T T) (p : Weight → Weight)
    (hp : ∀ a, p (-a) = -p a)
    (he : ∀ a, TorusCharacter.pullback f (e (Multiplicative.ofAdd a)) =
      e (Multiplicative.ofAdd (p a))) (a : Weight) :
    TorusCharacter.pullback f (embedding e a) = embedding e (p a) := by
  change TorusCharacter.pullback f (e (Multiplicative.ofAdd (-a))) = _
  rw [he, hp]
  rfl

/-- A geometric torus power map gives the exact scaled left character. -/
theorem pullback_embedding_power (e : Multiplicative Weight ≃* TorusCharacter T)
    (f : Theory.AlgebraicGroup.Morphism T T) (r : ℕ)
    (hf : ∀ t, f.onPoints t = t ^ r) (a : Weight) :
    TorusCharacter.pullback f (embedding e a) = embedding e (r • a) := by
  rw [embedding_nsmul]
  apply TorusCharacter.pointCharacter_injective
  ext t
  change (embedding e a).pointCharacter (f.onPoints t) = _
  rw [hf, map_pow, character_pow_point]

end Triality.RestrictedWeights.SteinbergTensors.LeftWeights

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup.StandardRootSystem
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A finite geometry producer supplies the actual torus map and its raw equation. -/
theorem Geometry.leftWeightEmbedding_pullback (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (π : Fin 4 → Fin 4)
    (hf : ∀ a, TorusCharacter.pullback f (S.coordinateEmbedding a) =
      S.coordinateEmbedding (a ∘ π)) (a : Weight) :
    TorusCharacter.pullback f (S.leftWeightEmbedding a) = S.leftWeightEmbedding (a ∘ π) :=
  LeftWeights.pullback_embedding_of_raw S.weight f (fun a => a ∘ π) (fun _ => rfl) hf a

theorem Geometry.leftWeightEmbedding_pullback_power (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (r : ℕ) (hf : ∀ t, f.onPoints t = t ^ r) (a : Weight) :
    TorusCharacter.pullback f (S.leftWeightEmbedding a) = S.leftWeightEmbedding (r • a) :=
  LeftWeights.pullback_embedding_power S.weight f r hf a

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
