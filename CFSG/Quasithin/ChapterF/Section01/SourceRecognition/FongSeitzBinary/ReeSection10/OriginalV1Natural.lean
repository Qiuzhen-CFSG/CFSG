module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V1Natural

/-!
# Natural linear coordinates on the original characteristic section

The original first endpoint two-core modulo its literal X₁ denominator is
now identified with the natural two-dimensional module on the common field.
The intertwiner retains the original endpoint conjugation, both ordered
endpoint inclusion squares, and the literal original quotient map Q.q.
Right conjugation uses the inverse pinned actor. These statements accept
both the original and geometric marked amalgam equivalences and include q=2.

This is the conditional natural-action step of Fong--Seitz II, pp.222--223.
The root-basis alignment and the remaining presentation equations are still
needed to construct Section10Construction from the independent (6H) input.
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

local instance originalV1NaturalBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Natural coordinates on the original quotient, with its exact denominator. -/
def originalV1Coordinates :
    Additive (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) ≃ₗ[ZMod 2]
      (Fin 2 → ReeF4.CoefficientField m) :=
  (LinearEquiv.ofBijective
    ((originalV1Equiv Q e split c).toMonoidHom.toAdditive.toZModLinearMap 2)
    (originalV1Equiv Q e split c).bijective).trans (V1Coordinates Q split c).toLinearEquiv

@[simp] theorem originalV1Coordinates_apply
    (v : pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) :
    originalV1Coordinates Q e split c (Additive.ofMul v) =
      V1Coordinates Q split c (Additive.ofMul (originalV1Equiv Q e split c v)) := rfl

theorem originalV1_finrank :
    Module.finrank (ZMod 2) (Additive (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c)) =
      2*(2*m+1) :=
  (LinearEquiv.ofBijective
    ((originalV1Equiv Q e split c).toMonoidHom.toAdditive.toZModLinearMap 2)
    (originalV1Equiv Q e split c).bijective).finrank_eq.trans (V1_finrank Q split c)

/-- The original first endpoint acts by the actual pinned natural matrices. -/
theorem originalV1Coordinates_conjugation
    (g : parabolic L S 0) (hg : endpointMap Q e 0 g ∈ rankOne Q split 0)
    (v : pCore 2 (parabolic L S 0)) :
    originalV1Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g v))) =
      Representation.SL2.BinarySmall.natural
        ((linearPinning Q split c).symm ⟨endpointMap Q e 0 g,hg⟩)
        (originalV1Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [originalV1Coordinates_apply,originalV1Coordinates_apply,
    originalV1Equiv_conjugation Q e split c g hg v,originalV1Equiv_mk]
  exact V1Coordinates_source Q split c _ _

/-- Both original endpoint inclusions retain the same natural vector. -/
theorem originalV1Coordinates_endpoints (h : HypothesisF11 L S)
    (v : pCore 2 (parabolic L S 0)) :
    ∀ i : Fin 2, ∃ hi : (v.val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨v.val.val,hi⟩ = (originalV1NumeratorEquiv Q e split c v : X ⧸ Q.D) ∧
      originalV1Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk v)) =
        V1Coordinates Q split c (Additive.ofMul
          (QuotientGroup.mk (originalV1NumeratorEquiv Q e split c v))) := by
  intro i
  obtain ⟨hi,he,hv⟩ := originalV1Equiv_endpoints Q e split c h v i
  refine ⟨hi,he,?_⟩
  rw [originalV1Coordinates_apply,hv]
  rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

local instance originalV1NaturalQuotientBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Natural coordinates preserve the original quotient Q.q on each radical element. -/
theorem originalV1Coordinates_quotient (v : pCore 2 (parabolic L S 0)) :
    originalV1Coordinates Q (originalMarkedIso Q) split c (Additive.ofMul (QuotientGroup.mk v)) =
      V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (⟨Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩,
          by rw [←originalRadicalEquiv_quotient Q split 0 (linearRemainder_le_kernel Q split c) v]
             exact (originalV1NumeratorEquiv Q (originalMarkedIso Q) split c v).property⟩ :
          simpleRemainder Q split 0))) := by
  rw [originalV1Coordinates_apply,originalV1Equiv_quotient]
  rfl

/-- The source right-conjugation convention uses the inverse pinned actor. -/
theorem V1Coordinates_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 0)
    (hv : Q.q v ∈ simpleRemainder Q split 0) :
    ∃ w : simpleRemainder Q split 0,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk w)) =
        Representation.SL2.BinarySmall.natural
          ((linearPinning Q split c).symm (⟨Q.q g,hg⟩ : rankOne Q split 0)⁻¹)
          (V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk (⟨Q.q v,hv⟩ :
            simpleRemainder Q split 0)))) := by
  let r : rankOne Q split 0 := ⟨Q.q g,hg⟩
  let a : (V1Section Q split c).numerator := ⟨Q.q v,hv⟩
  let w := (V1Section Q split c).numeratorAction r⁻¹ a
  refine ⟨w,?_,V1Coordinates_source Q split c r⁻¹ a⟩
  change (Q.q g)⁻¹ * Q.q v * ((Q.q g)⁻¹)⁻¹ = Q.q (g⁻¹*v*g)
  rw [inv_inv,map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
