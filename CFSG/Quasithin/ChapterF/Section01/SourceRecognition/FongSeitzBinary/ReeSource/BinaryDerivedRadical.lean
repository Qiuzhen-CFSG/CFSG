module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.DerivedRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinarySections

/-!
# The binary derived-radical module on the source octagon

At `m = 0` the Suzuki actor is the solvable group `Sz(2)`, so the positive
parameter simplicity argument cannot be used for the literal derived radical.
The source order-five movement argument does apply once its movement witness
on the actual derived section has been established.  This leaf packages that
argument without changing the section, quotient, or actor: it gives faithful
effectivity, the transported binary representation, and the resulting
four-dimensional Frattini bound.  The movement witness remains an explicit
premise for the later (6H) source case analysis.

Source: Fong--Seitz I (1973), the binary effective-section argument in the
proof of (6H), printed pp.52--53.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include hB in
theorem binary_derivedRadical_effectiveAction_injective
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    Function.Injective (derivedRadicalSection Q split i hV).effectiveAction := by
  exact binary_suzuki_section_effectiveAction_injective Q split i μ hB
    (derivedRadicalSection Q split i hV) c hc hmove

include hB in
theorem binary_derivedRadical_effectiveRepresentation_injective
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    Function.Injective (derivedRadicalSection Q split i hV).effectiveRepresentation :=
  (derivedRadicalSection Q split i hV).effectiveRepresentation_injective
    (binary_derivedRadical_effectiveAction_injective Q split i hV μ hB c hc hmove)

/-- The literal binary actor on the actual derived section. -/
def binarySuzukiDerivedRepresentation
    (c : rankOne Q split i) (_hc : orderOf c = 5)
    (_hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    Representation (ZMod 2) (SuzukiMatrixGroup 0)
      (Additive (derivedRadicalSection Q split i hV).EffectiveCarrier) :=
  (derivedRadicalSection Q split i hV).effectiveRepresentation.comp
    (suzukiActorEquiv Q split i 0 μ hB).symm.toMonoidHom

include hB in
theorem binarySuzukiDerivedRepresentation_injective
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    Function.Injective (binarySuzukiDerivedRepresentation Q split i hV μ hB c hc hmove) :=
  (binary_derivedRadical_effectiveRepresentation_injective Q split i hV μ hB c hc hmove).comp
    (suzukiActorEquiv Q split i 0 μ hB).symm.injective

include hB in
theorem binary_derivedRadical_frattini_finrank_ge
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    4 ≤ Module.finrank (ZMod 2)
      (Additive (derivedRadicalSection Q split i hV).EffectiveCarrier) := by
  let ρ := binarySuzukiDerivedRepresentation Q split i hV μ hB c hc hmove
  have hρ : Function.Injective ρ :=
    binarySuzukiDerivedRepresentation_injective Q split i hV μ hB c hc hmove
  have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
    (show 5 ∣ Nat.card (SuzukiMatrixGroup 0) by rw [suzukiZero_card]; decide)
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five] using hh

include hB in
theorem binary_derivedRadical_frattini_card_ge
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    2^4 ≤ Nat.card
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⧸
        frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) := by
  let d := derivedRadicalSection Q split i hV
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  rw [Nat.card_zmod] at he
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
    (binary_derivedRadical_frattini_finrank_ge Q split i hV μ hB c hc hmove)
  rw [← he] at hh
  have hh' : 2^4 ≤ Nat.card d.EffectiveCarrier := by
    simpa only [Nat.mul_one,
      Nat.card_congr (Additive.toMul : Additive d.EffectiveCarrier ≃ _)] using hh
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^4 ≤ Nat.card (d.numerator ⧸ d.effectiveDenominator) at hh'
  change 2^4 ≤ Nat.card (d.numerator ⧸ frattini d.numerator)
  rwa [hd] at hh'

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
