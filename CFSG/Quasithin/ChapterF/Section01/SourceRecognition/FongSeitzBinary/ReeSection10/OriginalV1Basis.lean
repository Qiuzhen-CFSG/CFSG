module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V1Basis

/-!
# The printed linear basis on the original characteristic quotient

The normalized natural intertwiner and both literal source basis points
are transported along the original radical equivalence. The maps retain
original endpoint conjugation, both ordered endpoint inclusion squares,
and the literal quotient Q.q, including m=0. The representatives map to
the corrected Suzuki point u₂(1,0) and its conjugate by the supplied s₁.

This applies the proved root-vector assertion (10.6) to the actual source;
the additive field labels still require the subsequent commutator comparison.
Source: Fong--Seitz II (1974), printed pp.222--223.
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

local instance originalV1BasisBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Natural coordinates on the original quotient, with its exact denominator. -/
def originalV1BasisCoordinates :
    Additive (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) ≃ₗ[ZMod 2]
      (Fin 2 → ReeF4.CoefficientField m) :=
  (LinearEquiv.ofBijective
    ((originalV1Equiv Q e split c).toMonoidHom.toAdditive.toZModLinearMap 2)
    (originalV1Equiv Q e split c).bijective).trans (V1BasisCoordinates Q split c).toLinearEquiv

@[simp] theorem originalV1BasisCoordinates_apply
    (v : pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) :
    originalV1BasisCoordinates Q e split c (Additive.ofMul v) =
      V1BasisCoordinates Q split c (Additive.ofMul (originalV1Equiv Q e split c v)) := rfl

/-- The original first endpoint acts by the actual pinned natural matrices. -/
theorem originalV1BasisCoordinates_conjugation
    (g : parabolic L S 0) (hg : endpointMap Q e 0 g ∈ rankOne Q split 0)
    (v : pCore 2 (parabolic L S 0)) :
    originalV1BasisCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g v))) =
      Representation.SL2.BinarySmall.natural
        ((linearPinning Q split c).symm ⟨endpointMap Q e 0 g,hg⟩)
        (originalV1BasisCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [originalV1BasisCoordinates_apply,originalV1BasisCoordinates_apply,
    originalV1Equiv_conjugation Q e split c g hg v,originalV1Equiv_mk]
  exact V1BasisCoordinates_source Q split c _ _

/-- Both original endpoint inclusions retain the same natural vector. -/
theorem originalV1BasisCoordinates_endpoints (h : HypothesisF11 L S)
    (v : pCore 2 (parabolic L S 0)) :
    ∀ i : Fin 2, ∃ hi : (v.val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨v.val.val,hi⟩ = (originalV1NumeratorEquiv Q e split c v : X ⧸ Q.D) ∧
      originalV1BasisCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk v)) =
        V1BasisCoordinates Q split c (Additive.ofMul
          (QuotientGroup.mk (originalV1NumeratorEquiv Q e split c v))) := by
  intro i
  obtain ⟨hi,he,hv⟩ := originalV1Equiv_endpoints Q e split c h v i
  refine ⟨hi,he,?_⟩
  rw [originalV1BasisCoordinates_apply,hv]
  rfl


/-- Original radical representatives of the two literal source basis vectors. -/
def originalV1BasisPoint (i : Fin 2) : pCore 2 (parabolic L S 0) :=
  (originalV1NumeratorEquiv Q e split c).symm (V1BasisPoint Q split c i)

@[simp] theorem originalV1BasisPoint_image (i : Fin 2) :
    originalV1NumeratorEquiv Q e split c (originalV1BasisPoint Q e split c i) =
      V1BasisPoint Q split c i :=
  (originalV1NumeratorEquiv Q e split c).apply_symm_apply _

theorem originalV1BasisPoint_coordinates (i : Fin 2) :
    originalV1BasisCoordinates Q e split c
      (Additive.ofMul (QuotientGroup.mk (originalV1BasisPoint Q e split c i))) =
      ![![0,1],![1,0]] i := by
  rw [originalV1BasisCoordinates_apply,originalV1Equiv_mk,originalV1BasisPoint_image]
  exact V1BasisPoint_coordinates Q split c i

/-- Each printed vector retains both endpoint inclusions in the original amalgam. -/
theorem originalV1BasisPoint_endpoints (h : HypothesisF11 L S) (j : Fin 2) :
    ∀ i : Fin 2, ∃ hi : ((originalV1BasisPoint Q e split c j).val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨(originalV1BasisPoint Q e split c j).val.val,hi⟩ =
        (V1BasisPoint Q split c j : X ⧸ Q.D) ∧
      originalV1BasisCoordinates Q e split c
        (Additive.ofMul (QuotientGroup.mk (originalV1BasisPoint Q e split c j))) =
        ![![0,1],![1,0]] j := by
  intro i
  obtain ⟨hi,he,_⟩ := originalV1BasisCoordinates_endpoints Q e split c h
    (originalV1BasisPoint Q e split c j) i
  exact ⟨hi,by simpa only [originalV1BasisPoint_image] using he,
    originalV1BasisPoint_coordinates Q e split c j⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

local instance originalV1BasisQuotientBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Natural coordinates preserve the original quotient Q.q on each radical element. -/
theorem originalV1BasisCoordinates_quotient (v : pCore 2 (parabolic L S 0)) :
    originalV1BasisCoordinates Q (originalMarkedIso Q) split c (Additive.ofMul (QuotientGroup.mk v)) =
      V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (⟨Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩,
          by rw [←originalRadicalEquiv_quotient Q split 0 (linearRemainder_le_kernel Q split c) v]
             exact (originalV1NumeratorEquiv Q (originalMarkedIso Q) split c v).property⟩ :
          simpleRemainder Q split 0))) := by
  rw [originalV1BasisCoordinates_apply,originalV1Equiv_quotient]
  rfl

/-- The source right-conjugation convention uses the inverse pinned actor. -/
theorem V1BasisCoordinates_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 0)
    (hv : Q.q v ∈ simpleRemainder Q split 0) :
    ∃ w : simpleRemainder Q split 0,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk w)) =
        Representation.SL2.BinarySmall.natural
          ((linearPinning Q split c).symm (⟨Q.q g,hg⟩ : rankOne Q split 0)⁻¹)
          (V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk (⟨Q.q v,hv⟩ :
            simpleRemainder Q split 0)))) := by
  let r : rankOne Q split 0 := ⟨Q.q g,hg⟩
  let a : (V1Section Q split c).numerator := ⟨Q.q v,hv⟩
  let w := (V1Section Q split c).numeratorAction r⁻¹ a
  refine ⟨w,?_,V1BasisCoordinates_source Q split c r⁻¹ a⟩
  change (Q.q g)⁻¹ * Q.q v * ((Q.q g)⁻¹)⁻¹ = Q.q (g⁻¹*v*g)
  rw [inv_inv,map_mul,map_mul,map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
