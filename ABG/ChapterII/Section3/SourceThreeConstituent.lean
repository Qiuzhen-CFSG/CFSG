module

public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import Theory.FieldTheory.OddQuadraticCoefficientLift

/-!
# The actual SL₂(GF(3)) constituent of source characteristic three

A finite group with trivial odd core and source characteristic power three
contains a normal subgroup isomorphic to the actual SL₂ over GF(3). The
source predicate supplies a characteristic SL₂ constituent in the odd-core
quotient over an arbitrary finite field of order three. The trivial quotient
equivalence brings it into the original group; finite-field uniqueness
replaces that field by GF(3).

This shared reduction preserves the original group universe and requires
no Q-group or Sylow-shape hypothesis. It is the source-to-matrix step in
both the linear and unitary characteristic-three model arguments.
Source: ABG II.3 Definition 1, article p. 23, together with the trivial
quotient equivalence and uniqueness of finite fields of a given order.
-/

namespace ABG
open GorensteinWalter

/-- A core-free source characteristic-three group has an actual normal SL₂(GF(3)) constituent. -/
public theorem exists_normal_sl2_three_of_sourceCharacteristicPower
    {H : Type*} [Group H] [Finite H]
    (hcore : pPrimeCore 2 H = ⊥) (hq : HasSourceQCharacteristicPower H 3) :
    ∃ M : Subgroup H, M.Normal ∧
      Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) := by
  classical
  obtain ⟨F, iF, fF, _, hFc, L0, hL0, ⟨eL0⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  let : L0.Characteristic := hL0
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let M := L0.map eQ.toMonoidHom
  have hM : M.Normal := (inferInstance : L0.Normal).map _ eQ.surjective
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F := (eQ.subgroupMap L0).symm.trans eL0
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 3 1)
  let eF : F ≃+* GaloisField 3 1 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide), pow_one] using hFc)
  exact ⟨M, hM, ⟨eM.trans (sl2RingEquiv eF)⟩⟩

end ABG
