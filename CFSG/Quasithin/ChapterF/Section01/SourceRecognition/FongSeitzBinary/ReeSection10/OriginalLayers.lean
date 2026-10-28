module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.SuzukiLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalFrattiniRadical

/-!
# Section 10 Suzuki layers on the original marked endpoints

The existing actual two-core equivalence transports T₂ and the center
layer through the same second endpoint map. We construct isomorphisms
from O₂(P₂)/T₂ and Φ(O₂(P₂))/Z(O₂(P₂)) to the source sections and prove
that they intertwine original conjugation on representatives. The center
denominator is identified with the literal original center, with normality
relative to the Frattini numerator. Both quotients are elementary.

For the original generated carrier, the representative and right-conjugation
formulas retain exactly Q.q. The general marked endpoint construction also
accepts the geometric marked isomorphism. Every m, including zero, is retained.

Source: Fong--Seitz II (1974), Section 10, printed pp.221--224.
These transport proofs consume explicit ReeSixHData. They do not identify
the layers with natural field modules or supply the remaining coordinates.
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

/-- The exact numerator type used by the source V₂ quotient. -/
def originalV2NumeratorEquiv : pCore 2 (parabolic L S 1) ≃* (V2Section Q split c).numerator :=
  originalRadicalEquiv Q e split 1 (remainder_le_kernel Q split c)

/-- The denominator inside the original second endpoint two-core. -/
def originalT2 : Subgroup (pCore 2 (parabolic L S 1)) :=
  (V2Section Q split c).denominator.comap
    (originalV2NumeratorEquiv Q e split c).toMonoidHom

instance originalT2_normal : (originalT2 Q e split c).Normal :=
  inferInstanceAs (Subgroup.Normal ((V2Section Q split c).denominator.comap
    (originalV2NumeratorEquiv Q e split c).toMonoidHom))

theorem mem_originalT2 (v : pCore 2 (parabolic L S 1)) :
    v ∈ originalT2 Q e split c ↔ endpointMap Q e 1 v ∈ T2 Q split := Iff.rfl

/-- The literal original V₂ quotient and its marked source quotient agree. -/
def originalV2Equiv :
    (pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c) ≃* (V2Section Q split c).Carrier :=
  QuotientGroup.congr _ _ (originalV2NumeratorEquiv Q e split c)
    (Subgroup.map_comap_eq_self_of_surjective
      (originalV2NumeratorEquiv Q e split c).surjective _)

@[simp] theorem originalV2Equiv_mk (v : pCore 2 (parabolic L S 1)) :
    originalV2Equiv Q e split c (QuotientGroup.mk v) =
      QuotientGroup.mk (originalRadicalEquiv Q e split 1 (remainder_le_kernel Q split c) v) := rfl

instance originalV2_elementary :
    IsElementaryAbelian 2 (pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split c) :=
  IsElementaryAbelian.of_surjective (originalV2Equiv Q e split c).symm.toMonoidHom
    (originalV2Equiv Q e split c).symm.surjective

/-- The source action is the original endpoint conjugation on every core representative. -/
theorem originalV2Equiv_conjugation
    (g : parabolic L S 1) (hg : endpointMap Q e 1 g ∈ rankOne Q split 1)
    (v : pCore 2 (parabolic L S 1)) :
    (V2Section Q split c).action ⟨endpointMap Q e 1 g, hg⟩
      (originalV2Equiv Q e split c (QuotientGroup.mk v)) =
      originalV2Equiv Q e split c (QuotientGroup.mk (MulAut.conjNormal g v)) := by
  change QuotientGroup.mk' (V2Section Q split c).denominator
      ((V2Section Q split c).numeratorAction ⟨endpointMap Q e 1 g, hg⟩
        (originalV2NumeratorEquiv Q e split c v)) =
    QuotientGroup.mk' (V2Section Q split c).denominator
      (originalV2NumeratorEquiv Q e split c (MulAut.conjNormal g v))
  apply congrArg (QuotientGroup.mk' (V2Section Q split c).denominator)
  apply Subtype.ext
  change endpointMap Q e 1 g * endpointMap Q e 1 v * (endpointMap Q e 1 g)⁻¹ =
    endpointMap Q e 1 (g*v.val*g⁻¹)
  rw [map_mul, map_mul, map_inv]

/-- The exact numerator type used by the source Frattini/center quotient. -/
def originalPhiNumeratorEquiv : frattini (pCore 2 (parabolic L S 1)) ≃*
    (phiCenterSection Q split c).numerator :=
  originalPhiRadicalEquiv Q e split 1 (remainder_le_kernel Q split c)

/-- The original Φ(Uₛ₂)/Z(Uₛ₂) denominator, with the same endpoint marking. -/
def originalPhiCenterDenominator : Subgroup (frattini (pCore 2 (parabolic L S 1))) :=
  (phiCenterSection Q split c).denominator.comap
    (originalPhiNumeratorEquiv Q e split c).toMonoidHom

instance originalPhiCenterDenominator_normal : (originalPhiCenterDenominator Q e split c).Normal :=
  inferInstanceAs (Subgroup.Normal ((phiCenterSection Q split c).denominator.comap
    (originalPhiNumeratorEquiv Q e split c).toMonoidHom))

theorem mem_originalPhiCenterDenominator (v : frattini (pCore 2 (parabolic L S 1))) :
    v ∈ originalPhiCenterDenominator Q e split c ↔
      endpointMap Q e 1 v.val.val ∈ zeta (simpleRemainder Q split 1) := Iff.rfl

/-- This transported denominator is exactly the original center, relative to Φ(O₂(P₂)). -/
theorem originalPhiCenterDenominator_eq : originalPhiCenterDenominator Q e split c =
    (center (pCore 2 (parabolic L S 1))).subgroupOf (frattini (pCore 2 (parabolic L S 1))) := by
  ext v
  rw [mem_originalPhiCenterDenominator]
  let a := originalRadicalEquiv Q e split 1 (remainder_le_kernel Q split c)
  change ((a v.val : simpleRemainder Q split 1) : X ⧸ Q.D) ∈
    (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ↔
    v.val ∈ center (pCore 2 (parabolic L S 1))
  exact (Subgroup.mem_map_iff_mem (K := center (simpleRemainder Q split 1))
    (x := a v.val) (simpleRemainder Q split 1).subtype_injective).trans
      (MulEquivClass.apply_mem_center_iff a)

def originalPhiCenterEquiv :
    (frattini (pCore 2 (parabolic L S 1)) ⧸ originalPhiCenterDenominator Q e split c) ≃*
      (phiCenterSection Q split c).Carrier :=
  QuotientGroup.congr _ _ (originalPhiNumeratorEquiv Q e split c)
    (Subgroup.map_comap_eq_self_of_surjective
      (originalPhiNumeratorEquiv Q e split c).surjective _)

@[simp] theorem originalPhiCenterEquiv_mk (v : frattini (pCore 2 (parabolic L S 1))) :
    originalPhiCenterEquiv Q e split c (QuotientGroup.mk v) =
      QuotientGroup.mk (originalPhiRadicalEquiv Q e split 1 (remainder_le_kernel Q split c) v) := rfl

instance originalPhiCenter_elementary : IsElementaryAbelian 2
    (frattini (pCore 2 (parabolic L S 1)) ⧸ originalPhiCenterDenominator Q e split c) :=
  IsElementaryAbelian.of_surjective (originalPhiCenterEquiv Q e split c).symm.toMonoidHom
    (originalPhiCenterEquiv Q e split c).symm.surjective

theorem originalPhiCenterEquiv_conjugation
    (g : parabolic L S 1) (hg : endpointMap Q e 1 g ∈ rankOne Q split 1)
    (v : frattini (pCore 2 (parabolic L S 1))) :
    (phiCenterSection Q split c).action ⟨endpointMap Q e 1 g, hg⟩
      (originalPhiCenterEquiv Q e split c (QuotientGroup.mk v)) =
      originalPhiCenterEquiv Q e split c
        (QuotientGroup.mk
          (MulAut.characteristic (frattini (pCore 2 (parabolic L S 1))) (MulAut.conjNormal g) v)) := by
  change QuotientGroup.mk' (phiCenterSection Q split c).denominator
      ((phiCenterSection Q split c).numeratorAction ⟨endpointMap Q e 1 g, hg⟩
        (originalPhiNumeratorEquiv Q e split c v)) =
    QuotientGroup.mk' (phiCenterSection Q split c).denominator
      (originalPhiNumeratorEquiv Q e split c
        (MulAut.characteristic (frattini (pCore 2 (parabolic L S 1))) (MulAut.conjNormal g) v))
  apply congrArg (QuotientGroup.mk' (phiCenterSection Q split c).denominator)
  apply Subtype.ext
  change endpointMap Q e 1 g * endpointMap Q e 1 v.val.val * (endpointMap Q e 1 g)⁻¹ =
    endpointMap Q e 1 (g*v.val.val*g⁻¹)
  rw [map_mul, map_mul, map_inv]

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

/-- The original V₂ representatives use precisely the original quotient Q.q. -/
theorem originalV2Equiv_quotient (v : pCore 2 (parabolic L S 1)) :
    originalV2Equiv Q (originalMarkedIso Q) split c (QuotientGroup.mk v) =
      QuotientGroup.mk (⟨Q.q ⟨v,parabolic_le_generated 1 v.val.property⟩,
        by rw [← originalRadicalEquiv_quotient Q split 1 (remainder_le_kernel Q split c) v]
           exact (originalRadicalEquiv Q (originalMarkedIso Q) split 1
             (remainder_le_kernel Q split c) v).property⟩ : simpleRemainder Q split 1) := by
  rw [originalV2Equiv_mk]
  congr 1
  exact Subtype.ext (originalRadicalEquiv_quotient Q split 1 (remainder_le_kernel Q split c) v)

/-- Right conjugation on V₂ retains both original quotient representatives. -/
theorem originalV2_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 1)
    (hv : Q.q v ∈ simpleRemainder Q split 1) :
    ∃ w : simpleRemainder Q split 1,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      (V2Section Q split c).action (⟨Q.q g,hg⟩ : rankOne Q split 1)⁻¹
        (QuotientGroup.mk (⟨Q.q v,hv⟩ : simpleRemainder Q split 1)) = QuotientGroup.mk w := by
  let w := (V2Section Q split c).numeratorAction
    (⟨Q.q g,hg⟩ : rankOne Q split 1)⁻¹ ⟨Q.q v,hv⟩
  refine ⟨w,?_,(V2Section Q split c).action_mk _ _⟩
  change (Q.q g)⁻¹ * Q.q v * ((Q.q g)⁻¹)⁻¹ = Q.q (g⁻¹*v*g)
  rw [inv_inv, map_mul, map_mul, map_inv]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
