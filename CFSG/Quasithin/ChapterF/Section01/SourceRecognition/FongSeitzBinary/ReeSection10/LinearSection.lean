module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearBinaryDerived
/-!
# The literal characteristic V₁ section and original action

The all-parameter characteristic denominator defines the actual section
V₁=U_s₁/X₁ and its rank-one conjugation representation. Its effective
Frattini denominator is still X₁, and its two barred endpoint coordinates
prove order q² and binary dimension 2(2m+1). These coordinates are a group
marking; faithfulness, irreducibility, and the natural basis (10.6) remain
subsequent obligations.

The original endpoint equivalence transports the denominator and quotient,
including characteristicity and the binary Omega-preimage identity. The
binary diagonal test and order-32 abelianization apply to the same original
radical. The conjugation comparison, both ordered endpoint inclusion squares,
and the literal Q.q formulas preserve the original and geometric markings.
Source: Fong--Seitz II (1974), printed pp.222--223, before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The actual characteristic section on the linear side of p.222. -/
def V1Section : RootSection Q split 0 where
  numerator := simpleRemainder Q split 0
  le_radical := le_rfl
  normalized := (rankOne_le_parabolic Q split 0).trans
    (remainder_parabolic_normalizes Q split 0
      (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
        (ReeSource.linear_normalizer_index c.linearSylow)))
  denominator := (X1 Q split).subgroupOf (simpleRemainder Q split 0)
  normal := linearX1Normal Q split c
  invariant r := by
    let : ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic :=
      X1_characteristic Q split c
    exact characteristic_iff_map_eq.mp inferInstance _

theorem V1Section_effectiveDenominator :
    (V1Section Q split c).effectiveDenominator = (V1Section Q split c).denominator := by
  rw [RootSection.effectiveDenominator_eq,sup_eq_right]
  exact map_le_iff_le_comap.mp (linearPhi_le_X1 Q split c)

instance V1Section_elementary : IsElementaryAbelian 2 (V1Section Q split c).Carrier := by
  let e := QuotientGroup.quotientMulEquivOfEq (V1Section_effectiveDenominator Q split c)
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

/-- This is a quotient group marking before identifying its natural action. -/
def V1BarEquiv : (V1Section Q split c).Carrier ≃*
    (Multiplicative (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2*m+1)) ×
     Multiplicative (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2*m+1))) := by
  let := linearX1Normal Q split c
  exact (QuotientGroup.quotientMulEquivOfEq (linearBarBoundary_kernel Q split c).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (linearBarBoundary Q split c)
      (linearBarBoundary_surjective Q split c))

@[simp] theorem V1BarEquiv_mk (v : simpleRemainder Q split 0) :
    V1BarEquiv Q split c (QuotientGroup.mk v) = linearBarBoundary Q split c v := by
  let := linearX1Normal Q split c
  change (QuotientGroup.quotientKerEquivOfSurjective (linearBarBoundary Q split c)
    (linearBarBoundary_surjective Q split c))
      (QuotientGroup.quotientMulEquivOfEq (linearBarBoundary_kernel Q split c).symm
        (QuotientGroup.mk v)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem V1_card : Nat.card (V1Section Q split c).Carrier = (2^(2*m+1))^2 :=
  X1_quotient_card Q split c

theorem V1_finrank : Module.finrank (ZMod 2) (Additive (V1Section Q split c).Carrier) =
    2*(2*m+1) := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (V1Section Q split c).Carrier)
  rw [Nat.card_zmod] at he
  have hc : Nat.card (Additive (V1Section Q split c).Carrier) = (2^(2*m+1))^2 := V1_card Q split c
  rw [hc,←pow_mul] at he
  have hh := Nat.pow_right_injective (by decide : 1 < 2) he
  omega

/-- Literal conjugation on U_s₁/X₁, with the binary denominator included. -/
def V1Representation : Representation (ZMod 2) (rankOne Q split 0)
    (Additive (V1Section Q split c).Carrier) where
  toFun r := ((V1Section Q split c).action r).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' r s := by ext x; simp only [map_mul]; rfl

@[simp] theorem V1Representation_mk (r : rankOne Q split 0)
    (v : simpleRemainder Q split 0) :
    V1Representation Q split c r (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk ((V1Section Q split c).numeratorAction r v)) := rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
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

theorem originalX1_characteristic : (originalX1 Q e split c).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f v hv
  let u := originalV1NumeratorEquiv Q e split c
  have hh := characteristic_iff_le_comap.mp (X1_characteristic Q split c) (MulAut.congr u f) hv
  change u (f (u.symm (u v))) ∈ (X1 Q split).subgroupOf (simpleRemainder Q split 0) at hh
  change u (f v) ∈ (X1 Q split).subgroupOf (simpleRemainder Q split 0)
  simpa only [MulEquiv.symm_apply_apply] using hh

/-- At q=2 the printed Omega preimage holds on the original radical itself. -/
theorem original_binaryX1_eq_omega_preimage (c₀ : ReeSixHData Q split n 0) :
    originalX1 Q e split c₀ =
      (omega₁ (Abelianization (pCore 2 (parabolic L S 0))) (p := 2)).comap Abelianization.of := by
  let u := originalV1NumeratorEquiv Q e split c₀
  ext v
  change u v ∈ (X1 Q split).subgroupOf (simpleRemainder Q split 0) ↔ _
  rw [binary_X1_eq_squareKernel Q split c₀]
  change (Abelianization.of (u v))^2 = 1 ↔ Abelianization.of v ∈ omega₁ _
  have hs : (Abelianization.of (u v))^2 = 1 ↔ (Abelianization.of v)^2 = 1 := by
    rw [←abelianizationCongr_of u,←map_pow]
    exact u.abelianizationCongr.map_eq_one_iff
  rw [hs]
  constructor
  · intro h
    apply Subgroup.subset_closure
    change (Abelianization.of v)^(2^1) = 1
    simpa only [pow_one] using h
  · intro h
    let : IsElementaryAbelian 2 (omega₁ (Abelianization (pCore 2 (parabolic L S 0))) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    exact elemPow_eq_one_of_isElementaryAbelian _ h

/-- The quotient comparison is induced by the same marked numerator map. -/
def originalV1Equiv : (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) ≃*
    (V1Section Q split c).Carrier :=
  QuotientGroup.congr _ _ (originalV1NumeratorEquiv Q e split c)
    (map_comap_eq_self_of_surjective (originalV1NumeratorEquiv Q e split c).surjective _)

@[simp] theorem originalV1Equiv_mk (v : pCore 2 (parabolic L S 0)) :
    originalV1Equiv Q e split c (QuotientGroup.mk v) =
      QuotientGroup.mk (originalV1NumeratorEquiv Q e split c v) := rfl

/-- Actual original conjugation intertwines the quotient action, for either
original or geometric endpoint marking. -/
theorem originalV1Equiv_conjugation
    (g : parabolic L S 0) (hg : endpointMap Q e 0 g ∈ rankOne Q split 0)
    (v : pCore 2 (parabolic L S 0)) :
    originalV1Equiv Q e split c (QuotientGroup.mk (MulAut.conjNormal g v)) =
      (V1Section Q split c).action ⟨endpointMap Q e 0 g,hg⟩
        (originalV1Equiv Q e split c (QuotientGroup.mk v)) := by
  change QuotientGroup.mk ((originalV1NumeratorEquiv Q e split c) (MulAut.conjNormal g v)) =
    QuotientGroup.mk ((V1Section Q split c).numeratorAction
      ⟨endpointMap Q e 0 g,hg⟩ ((originalV1NumeratorEquiv Q e split c) v))
  congr 1
  apply Subtype.ext
  change endpointMap Q e 0 (g*v.val*g⁻¹) =
    endpointMap Q e 0 g * endpointMap Q e 0 v.val * (endpointMap Q e 0 g)⁻¹
  rw [map_mul,map_mul,map_inv]

/-- The new section still uses both ordered endpoint inclusion squares. -/
theorem originalV1Equiv_endpoints (h : HypothesisF11 L S)
    (v : pCore 2 (parabolic L S 0)) :
    ∀ i : Fin 2, ∃ hi : (v.val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨v.val.val,hi⟩ = (originalV1NumeratorEquiv Q e split c v : X ⧸ Q.D) ∧
      originalV1Equiv Q e split c (QuotientGroup.mk v) =
        QuotientGroup.mk (originalV1NumeratorEquiv Q e split c v) := by
  intro i
  obtain ⟨hi,he,_⟩ := originalX1_endpoints Q e split c h v i
  exact ⟨hi,he,originalV1Equiv_mk Q e split c v⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n : ℕ} (c₀ : ReeSixHData Q split n 0)

/-- The binary diagonal description detects derived membership in the original
radical through its actual marked endpoint map. -/
theorem original_binaryDerived_membership
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split)
    (v : pCore 2 (parabolic L S 0)) :
    v ∈ commutator (pCore 2 (parabolic L S 0)) ↔
      endpointMap Q e 0 v.val ∈ binaryDerivedClosure Q split c₀ := by
  let u := originalV1NumeratorEquiv Q e split c₀
  have hu : Abelianization.of (u v) = 1 ↔ Abelianization.of v = 1 := by
    rw [←abelianizationCongr_of u]
    exact u.abelianizationCongr.map_eq_one_iff
  rw [←binary_linearDerived_eq_generated Q split c₀ hn]
  change v ∈ commutator (pCore 2 (parabolic L S 0)) ↔ (u v : X ⧸ Q.D) ∈ linearDerived Q split
  rw [←linearDerived_abelianization_iff Q split (u v),hu]
  change _ ↔ v ∈ (Abelianization.of : pCore 2 (parabolic L S 0) →*
    Abelianization (pCore 2 (parabolic L S 0))).ker
  rw [Abelianization.ker_of]

include e c₀ in
/-- The original radical's actual abelianization has order 2⁵ in the
binary noncontainment branch; no endpoint quotient is substituted for it. -/
theorem original_binaryAbelianization_card
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    Nat.card (Abelianization (pCore 2 (parabolic L S 0))) = 32 :=
  (Nat.card_congr (originalV1NumeratorEquiv Q e split c₀).abelianizationCongr.toEquiv).trans
    (binary_linearAbelianization_card Q split c₀ hn)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The section comparison uses the original Q.q on every numerator representative. -/
theorem originalV1Equiv_quotient (v : pCore 2 (parabolic L S 0)) :
    originalV1Equiv Q (originalMarkedIso Q) split c (QuotientGroup.mk v) =
      QuotientGroup.mk (⟨Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩,
        by rw [←originalRadicalEquiv_quotient Q split 0
          (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
            (ReeSource.linear_normalizer_index c.linearSylow)) v]
           exact (originalV1NumeratorEquiv Q (originalMarkedIso Q) split c v).property⟩ :
        simpleRemainder Q split 0) := by
  rw [originalV1Equiv_mk]
  congr 1
  exact Subtype.ext (originalRadicalEquiv_quotient Q split 0
    (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
      (ReeSource.linear_normalizer_index c.linearSylow)) v)

/-- The binary derived test retains the literal original quotient map. -/
theorem original_binaryDerived_quotient (c₀ : ReeSixHData Q split n 0)
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split)
    (v : pCore 2 (parabolic L S 0)) :
    v ∈ commutator (pCore 2 (parabolic L S 0)) ↔
      Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩ ∈ binaryDerivedClosure Q split c₀ := by
  rw [original_binaryDerived_membership Q (originalMarkedIso Q) split c₀ hn]
  exact Iff.of_eq (congrArg (fun x => x ∈ binaryDerivedClosure Q split c₀)
    (originalMarkedIso_left_apply Q v.val))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
