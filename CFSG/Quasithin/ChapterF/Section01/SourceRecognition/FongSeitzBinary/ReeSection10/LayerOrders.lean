module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LayerCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PositiveCharts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RadicalDegree
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exact orders and binary dimensions of the Section 10 Suzuki layers

The five independent factors in (10.3) have order q, hence the Frattini
subgroup has order q^5. Its intersection with the perpendicular Suzuki root
is the latter's Omega, of order q, so T2 has order q^6. Carter's radical
order q^10 gives |V2| = q^4. The center identity in (10.3)(iii) similarly
gives |Phi(U_s2)/Z(U_s2)| = q^4. Both binary dimensions are 4(2m+1).

These are the literal quotients constructed in SuzukiLayers, including m=0.
Their faithfulness and natural-module identification are separate arguments.
Source: Fong--Seitz II (1974), printed pp.221 and 224, before (10.4), (10.11).
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem linear_positiveRoot_card (i : Fin 4) :
    Nat.card (positiveRoot Q split (.inl i)) = 2^(2*m+1) := by
  rw [←Nat.card_congr (positiveChart Q split c (RingEquiv.refl _) (.inl i))]
  exact GaloisField.card 2 (2*m+1) (by omega)

include c in
theorem suzuki_positiveRoot_card (i : Fin 4) :
    Nat.card (positiveRoot Q split (.inr i)) = (2^(2*m+1))^2 := by
  rw [←Nat.card_congr (positiveChart Q split c (RingEquiv.refl _) (.inr i))]
  change Nat.card (CoefficientField m × CoefficientField m) = _
  rw [Nat.card_prod,GaloisField.card 2 (2*m+1) (by omega),pow_two]

include c in
theorem omega_positiveRoot_card (i : Fin 4) :
    Nat.card (omegaOneAmbient (positiveRoot Q split (.inr i))) = 2^(2*m+1) := by
  let e := (MulAut.conj (positiveLift Q split c (.inr i) : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = positiveRoot Q split (.inr i) := by
    rw [positiveRoot,positiveKind,rootAt_eq Q split 1 _ _ (positiveLift_class Q split c (.inr i))]
    simp only [rightConjugate,comap_equiv_eq_map_symm']
    rfl
  have ho := map_omegaOneAmbient_injective e.toMonoidHom e.injective (simpleRoot Q split 1)
  rw [he] at ho
  rw [←ho,card_map_of_injective e.injective]
  exact suzukiOmega_card Q split 1 m c.suzuki c.suzukiBorel

include c in
theorem phiRemainder_card : Nat.card (phi (simpleRemainder Q split 1)) = (2^(2*m+1))^5 := by
  rw [←Nat.card_congr (phiCoordinates Q split c),card_rootTuple]
  simp only [phiFactors,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    omega_positiveRoot_card Q split c,linear_positiveRoot_card Q split c,mul_one]
  ring

include c in
theorem T2_card : Nat.card (T2 Q split) = (2^(2*m+1))^6 := by
  have hn : perpendicularSuzuki Q split ≤ normalizer
      (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) :=
    (perpendicularSuzuki_le_remainder Q split c).trans
      ((simpleRemainder Q split 1).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _)))
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (phi (simpleRemainder Q split 1)) (perpendicularSuzuki Q split) hn
  rw [phi_inf_perpendicular Q split c,phiRemainder_card Q split c] at hh
  change (2^(2*m+1))^5 * Nat.card (positiveRoot Q split (.inr 1)) =
    Nat.card (omegaOneAmbient (positiveRoot Q split (.inr 1))) * Nat.card (T2 Q split) at hh
  rw [suzuki_positiveRoot_card Q split c,omega_positiveRoot_card Q split c] at hh
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^(2*m+1) by positivity)
  rw [←hh]
  ring

include c in
theorem suzukiRemainder_card : Nat.card (simpleRemainder Q split 1) = (2^(2*m+1))^10 := by
  rw [suzuki_octagon_radical_card Q split 1 0 m c.suzuki c.suzukiBorel
    c.rotation_eight (by decide)]
  have he : positiveRoot Q split (.inl 0) = simpleRoot Q split 0 := rootAt_one Q split 0
  rw [←he,linear_positiveRoot_card Q split c]
  ring

include c in
theorem V2_card : Nat.card (V2Section Q split c).Carrier = (2^(2*m+1))^4 := by
  have he := (V2Section Q split c).denominator.card_mul_index
  have hd : Nat.card (V2Section Q split c).denominator = Nat.card (T2 Q split) :=
    Nat.card_congr (subgroupOfEquivOfLe (T2_le_remainder Q split c)).toEquiv
  change Nat.card (V2Section Q split c).denominator * Nat.card (V2Section Q split c).Carrier =
    Nat.card (simpleRemainder Q split 1) at he
  rw [hd,T2_card Q split c,suzukiRemainder_card Q split c] at he
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2^(2*m+1))^6 by positivity)
  rw [he]
  ring

include c in
theorem phiCenter_card : Nat.card (phiCenterSection Q split c).Carrier = (2^(2*m+1))^4 := by
  have he := (phiCenterSection Q split c).denominator.card_mul_index
  have hd : Nat.card (phiCenterSection Q split c).denominator = 2^(2*m+1) := by
    rw [←card_map_of_injective (phiCenterSection Q split c).numerator.subtype_injective,
      phiCenterSection_denominator_image]
    exact omega_positiveRoot_card Q split c 1
  change Nat.card (phiCenterSection Q split c).denominator *
    Nat.card (phiCenterSection Q split c).Carrier = Nat.card (phi (simpleRemainder Q split 1)) at he
  rw [hd,phiRemainder_card Q split c] at he
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^(2*m+1) by positivity)
  rw [he]
  ring

include c in
theorem V2_finrank : Module.finrank (ZMod 2) (Additive (V2Section Q split c).Carrier) = 4*(2*m+1) := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (V2Section Q split c).Carrier)
  rw [Nat.card_zmod] at he
  have hc : Nat.card (Additive (V2Section Q split c).Carrier) = (2^(2*m+1))^4 :=
    (Nat.card_congr Additive.toMul).trans (V2_card Q split c)
  rw [hc,←pow_mul] at he
  exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he.symm).trans (Nat.mul_comm _ _)

include c in
theorem phiCenter_finrank : Module.finrank (ZMod 2) (Additive (phiCenterSection Q split c).Carrier) =
    4*(2*m+1) := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (phiCenterSection Q split c).Carrier)
  rw [Nat.card_zmod] at he
  have hc : Nat.card (Additive (phiCenterSection Q split c).Carrier) = (2^(2*m+1))^4 :=
    (Nat.card_congr Additive.toMul).trans (phiCenter_card Q split c)
  rw [hc,←pow_mul] at he
  exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he.symm).trans (Nat.mul_comm _ _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
