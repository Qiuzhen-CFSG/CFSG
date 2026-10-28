module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NaturalLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalLayers

/-!
# Natural coordinates on the original marked Suzuki sections

The exact quotient equivalences in OriginalLayers transport both faithful
natural Suzuki coordinates to the original endpoint two-core. They identify
O2(P2)/T2 and Phi(O2(P2))/Z(O2(P2)) with the four-dimensional natural matrix
module over the same field. The cardinalities, binary dimensions and actual
conjugation formulas follow for every m, including the binary case.

The general marking accepts both original and geometric amalgam isomorphisms.
Specializing to the original marking retains the literal Q.q on numerator
representatives and the inverse actor required for right conjugation. The
center denominator remains the exact subgroup identified in OriginalLayers.

These are applications of the conditional (6H) input, not a reconstruction
of the full source group. Root-line alignment and mixed coefficients remain.
Source: Fong--Seitz II (1974), printed pp.221--224, before (10.4) and (10.11).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- Exact original first-layer order, with the marked denominator. -/
theorem originalV2_card :
    Nat.card (pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c) = (2^(2*m+1))^4 :=
  (Nat.card_congr (originalV2Equiv Q e split c).toEquiv).trans (V2_card Q split c)

/-- Exact original Frattini/center-layer order. -/
theorem originalPhiCenter_card :
    Nat.card (frattini (pCore 2 (parabolic L S 1)) ⧸ originalPhiCenterDenominator Q e split c) =
      (2^(2*m+1))^4 :=
  (Nat.card_congr (originalPhiCenterEquiv Q e split c).toEquiv).trans (phiCenter_card Q split c)

/-- The original V2 quotient has actual natural coordinates on the common field. -/
def originalV2Coordinates :
    Additive (pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c) ≃ₗ[ZMod 2]
      Representation.SuzukiNatural.W m :=
  (LinearEquiv.ofBijective
    ((originalV2Equiv Q e split c).toMonoidHom.toAdditive.toZModLinearMap 2)
    (originalV2Equiv Q e split c).bijective).trans (V2Coordinates Q split c).toLinearEquiv

/-- The original Frattini/center quotient uses the same field and matrix model. -/
def originalPhiCenterCoordinates :
    Additive (frattini (pCore 2 (parabolic L S 1)) ⧸ originalPhiCenterDenominator Q e split c)
      ≃ₗ[ZMod 2] Representation.SuzukiNatural.W m :=
  (LinearEquiv.ofBijective
    ((originalPhiCenterEquiv Q e split c).toMonoidHom.toAdditive.toZModLinearMap 2)
    (originalPhiCenterEquiv Q e split c).bijective).trans
    (phiCenterCoordinates Q split c).toLinearEquiv

@[simp] theorem originalV2Coordinates_apply
    (v : pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c) :
    originalV2Coordinates Q e split c (Additive.ofMul v) =
      V2Coordinates Q split c (Additive.ofMul (originalV2Equiv Q e split c v)) := rfl

@[simp] theorem originalPhiCenterCoordinates_apply
    (v : frattini (pCore 2 (parabolic L S 1)) ⧸ originalPhiCenterDenominator Q e split c) :
    originalPhiCenterCoordinates Q e split c (Additive.ofMul v) =
      phiCenterCoordinates Q split c (Additive.ofMul (originalPhiCenterEquiv Q e split c v)) := rfl

theorem originalV2_finrank :
    Module.finrank (ZMod 2) (Additive (pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c)) =
      4*(2*m+1) :=
  (originalV2Coordinates Q e split c).finrank_eq.trans (Representation.SuzukiNatural.natural_finrank m)

theorem originalPhiCenter_finrank :
    Module.finrank (ZMod 2) (Additive (frattini (pCore 2 (parabolic L S 1)) ⧸
      originalPhiCenterDenominator Q e split c)) = 4*(2*m+1) :=
  (originalPhiCenterCoordinates Q e split c).finrank_eq.trans (Representation.SuzukiNatural.natural_finrank m)

/-- Original endpoint conjugation is the literal natural Suzuki action. -/
theorem originalV2Coordinates_conjugation
    (g : parabolic L S 1) (hg : endpointMap Q e 1 g ∈ rankOne Q split 1)
    (v : pCore 2 (parabolic L S 1)) :
    originalV2Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g v))) =
      Representation.SuzukiNatural.natural m
        (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel ⟨endpointMap Q e 1 g,hg⟩)
        (originalV2Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [originalV2Coordinates_apply,originalV2Coordinates_apply,
    ← originalV2Equiv_conjugation Q e split c g hg v,originalV2Equiv_mk]
  exact V2Coordinates_source Q split c _ _

/-- Characteristic conjugation on the original Frattini numerator gives the
same natural action, with its literal original center denominator. -/
theorem originalPhiCenterCoordinates_conjugation
    (g : parabolic L S 1) (hg : endpointMap Q e 1 g ∈ rankOne Q split 1)
    (v : frattini (pCore 2 (parabolic L S 1))) :
    originalPhiCenterCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk
      (MulAut.characteristic (frattini (pCore 2 (parabolic L S 1))) (MulAut.conjNormal g) v))) =
      Representation.SuzukiNatural.natural m
        (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel ⟨endpointMap Q e 1 g,hg⟩)
        (originalPhiCenterCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [originalPhiCenterCoordinates_apply,originalPhiCenterCoordinates_apply,
    ← originalPhiCenterEquiv_conjugation Q e split c g hg v,originalPhiCenterEquiv_mk]
  exact phiCenterCoordinates_source Q split c _ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The natural coordinates retain the literal original quotient map Q.q. -/
theorem originalV2Coordinates_quotient (v : pCore 2 (parabolic L S 1)) :
    originalV2Coordinates Q (originalMarkedIso Q) split c (Additive.ofMul (QuotientGroup.mk v)) =
      V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (⟨Q.q ⟨v,parabolic_le_generated 1 v.val.property⟩,
          by rw [← originalRadicalEquiv_quotient Q split 1 (remainder_le_kernel Q split c) v]
             exact (originalRadicalEquiv Q (originalMarkedIso Q) split 1
               (remainder_le_kernel Q split c) v).property⟩ : simpleRemainder Q split 1))) := by
  rw [originalV2Coordinates_apply,originalV2Equiv_quotient]
  rfl

/-- Source right conjugation uses the inverse marked actor and the same Q.q. -/
theorem V2Coordinates_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 1)
    (hv : Q.q v ∈ simpleRemainder Q split 1) :
    ∃ w : simpleRemainder Q split 1,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk w)) =
        Representation.SuzukiNatural.natural m
          (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel (⟨Q.q g,hg⟩ : rankOne Q split 1)⁻¹)
          (V2Coordinates Q split c
            (Additive.ofMul (QuotientGroup.mk (⟨Q.q v,hv⟩ : simpleRemainder Q split 1)))) := by
  obtain ⟨w,hw,he⟩ := originalV2_right_quotient Q split c g v hg hv
  refine ⟨w,hw,?_⟩
  exact (congrArg (fun z : (V2Section Q split c).Carrier =>
    V2Coordinates Q split c (Additive.ofMul z)) he).symm.trans
      (V2Coordinates_source Q split c _ _)

/-- The Frattini/center natural coordinates also use the original Q.q. -/
theorem originalPhiCenterCoordinates_quotient
    (v : frattini (pCore 2 (parabolic L S 1))) :
    originalPhiCenterCoordinates Q (originalMarkedIso Q) split c
      (Additive.ofMul (QuotientGroup.mk v)) =
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (⟨Q.q ⟨v.val.val,parabolic_le_generated 1 v.val.val.property⟩,
          by rw [← originalPhiRadicalEquiv_quotient Q split 1 (remainder_le_kernel Q split c) v]
             exact (originalPhiRadicalEquiv Q (originalMarkedIso Q) split 1
               (remainder_le_kernel Q split c) v).property⟩ : (phiCenterSection Q split c).numerator))) := by
  rw [originalPhiCenterCoordinates_apply,originalPhiCenterEquiv_mk]
  apply congrArg (fun w : (phiCenterSection Q split c).numerator =>
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk w)))
  exact Subtype.ext (originalPhiRadicalEquiv_quotient Q split 1 (remainder_le_kernel Q split c) v)

/-- Right conjugation on the second natural layer retains the actual quotient
representatives, including the inverse in the right-action convention. -/
theorem phiCenterCoordinates_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 1)
    (hv : Q.q v ∈ (phiCenterSection Q split c).numerator) :
    ∃ w : (phiCenterSection Q split c).numerator,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk w)) =
        Representation.SuzukiNatural.natural m
          (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel (⟨Q.q g,hg⟩ : rankOne Q split 1)⁻¹)
          (phiCenterCoordinates Q split c
            (Additive.ofMul (QuotientGroup.mk (⟨Q.q v,hv⟩ : (phiCenterSection Q split c).numerator)))) := by
  let w := (phiCenterSection Q split c).numeratorAction
    (⟨Q.q g,hg⟩ : rankOne Q split 1)⁻¹ ⟨Q.q v,hv⟩
  refine ⟨w,?_,phiCenterCoordinates_source Q split c _ _⟩
  change (Q.q g)⁻¹ * Q.q v * ((Q.q g)⁻¹)⁻¹ = Q.q (g⁻¹*v*g)
  rw [inv_inv,map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
