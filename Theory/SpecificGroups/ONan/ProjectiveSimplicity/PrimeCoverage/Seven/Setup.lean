module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.Setup
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Coordinates

/-!
# Fixed words for a candidate O'Nan seven-subgroup

These three words were obtained from the explicit local generators by GAP's
Sylow and word-factorization routines. The first and third words are used as
noncentral generators; the quotient of the second by the third is the central
generator. This file defines their three-coordinate evaluation, without
asserting that it is injective, multiplicative, or a subgroup enumeration.
Those claims must be checked against the actual matrices.

The matrix source and attribution are in `refs/original/onan/README.md`.
The local generator words are attributed in `ProjectiveOrder/Setup.lean`.
GAP was only a witness producer, not a trusted proof procedure.
-/

namespace ONan.Simplicity.Seven

open ONan.OrderCertificate

/-- An explicit word in the two local generators. -/
@[expose] public def generatorX : Model :=
  localB * localA * localB⁻¹ * localA * localB⁻¹ * localA * localB⁻¹ *
    localA * localB⁻¹ * localA * localB * localA * localB * localA *
    localB⁻¹ * localA * localB⁻¹ * localA * localB⁻¹ * localA * localB⁻¹ *
    localA * localB * localA * localB⁻¹ * localA * localB * localA *
    localB * localA

/-- An explicit word in the two local generators. -/
@[expose] public def auxiliaryY : Model :=
  localB * localB * localA * localB * localA * localB * localB *
    localA * localB⁻¹ * localA * localB * localA * localB⁻¹ * localA *
    localB⁻¹ * localA * localB⁻¹ * localA * localB * localB * localA *
    localB * localA * localB * localA * localB * localA * localB

/-- An explicit word in the two local generators. -/
@[expose] public def generatorY : Model :=
  localB⁻¹ * localA * localB * localB * localA * localB * localB *
    localA * localB⁻¹ * localA * localB⁻¹ * localA * localB * localA *
    localB * localA * localB * localB * localA * localB * localB *
    localA * localB * localA * localB * localA * localB⁻¹ * localA

/-- The candidate central generator in the coordinate convention. -/
@[expose] public def generatorZ : Model := auxiliaryY * generatorY⁻¹

/-- Evaluation of the fixed normal forms in the actual projective model. -/
@[expose] public def evaluate (t : Coordinates) : Model :=
  generatorX ^ t.a.val * generatorY ^ t.b.val * generatorZ ^ t.c.val

public theorem evaluate_one : evaluate 1 = 1 := by
  change generatorX ^ 0 * generatorY ^ 0 * generatorZ ^ 0 = 1
  simp

public theorem evaluate_x : evaluate ⟨1, 0, 0⟩ = generatorX := by
  change generatorX ^ 1 * generatorY ^ 0 * generatorZ ^ 0 = generatorX
  simp

public theorem evaluate_y : evaluate ⟨0, 1, 0⟩ = generatorY := by
  change generatorX ^ 0 * generatorY ^ 1 * generatorZ ^ 0 = generatorY
  simp

/-- Turn a multiplication certificate into a homomorphism. -/
@[expose] public def coordinateHom
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t) : Coordinates →* Model where
  toFun := evaluate
  map_one' := evaluate_one
  map_mul' := hmul

/-- Only multiplication and one noncommutation test are needed for cardinality. -/
public theorem coordinateHom_range_card
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t)
    (hne : generatorX * generatorY ≠ generatorY * generatorX) :
    Nat.card (coordinateHom hmul).range = 343 := by
  apply card_range_of_noncommuting (coordinateHom hmul) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
  simpa only [coordinateHom, MonoidHom.coe_mk, OneHom.coe_mk, evaluate_x, evaluate_y] using hne

end ONan.Simplicity.Seven
