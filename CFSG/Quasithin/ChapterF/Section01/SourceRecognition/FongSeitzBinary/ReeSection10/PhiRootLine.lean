module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.RootLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFourSupport

/-!
# The first distinguished source line in Φ(Uₛ₂)/Z(Uₛ₂)

The literal Ω₁(U₂^(s₁s₂)) factor of (10.3) meets Z(Uₛ₂) trivially by
uniqueness of the five-factor product. The proved shifted-Omega commutator
identity places its image in the first natural Suzuki coordinate line.
Both have order q, so the coordinate is bijective, including q = 2, where
Omega remains different from the center of the cyclic Suzuki root.

Source: Fong--Seitz II (1974), printed p.224, the basis preceding (10.11).
This identifies a distinguished line, before comparing its field labels
with those of V₂ and the linear section.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem shiftedOmega_le_phi : omegaOneAmbient (positiveRoot Q split (.inr 3)) ≤
    phi (simpleRemainder Q split 1) := by
  intro x hx
  change x ∈ (phi (simpleRemainder Q split 1) : Set _)
  rw [←phiProduct_range Q split c]
  exact ⟨(⟨x,hx⟩,1,1,1,1,PUnit.unit),by
    simp only [phiFactors,rootProduct,OneMemClass.coe_one,mul_one]⟩

include c in
theorem shiftedOmega_disjoint_center :
    Disjoint (omegaOneAmbient (positiveRoot Q split (.inr 3)))
      (zeta (simpleRemainder Q split 1)) := by
  apply disjoint_def.mpr
  intro x hx hz
  have hz' : x ∈ omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
    have he := c.relations.ten_three_center_remainder 1
    have he' : omegaOneAmbient (positiveRoot Q split (.inr 1)) =
        zeta (simpleRemainder Q split 1) := by
      simpa [nConj,positiveRoot,positiveKind,positiveWord,Uat,
        Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using he
    rwa [he']
  let a : omegaOneAmbient (positiveRoot Q split (.inr 3)) := ⟨x,hx⟩
  let b : omegaOneAmbient (positiveRoot Q split (.inr 1)) := ⟨x,hz'⟩
  have he : rootProduct (phiFactors Q split) (a,1,1,1,1,PUnit.unit) =
      rootProduct (phiFactors Q split) (1,1,b,1,1,PUnit.unit) := by
    simp only [phiFactors,rootProduct,OneMemClass.coe_one,mul_one,one_mul]
    rfl
  exact congrArg (fun p => (p.1 : X ⧸ Q.D)) (phiProduct_injective Q split c he)

def phiShiftedOmega : omegaOneAmbient (positiveRoot Q split (.inr 3)) →*
    (phiCenterSection Q split c).Carrier :=
  (QuotientGroup.mk' (phiCenterSection Q split c).denominator).comp
    (inclusion (shiftedOmega_le_phi Q split c))

theorem phiShiftedOmega_injective : Function.Injective (phiShiftedOmega Q split c) := by
  apply (phiShiftedOmega Q split c).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : (x : X ⧸ Q.D) ∈ zeta (simpleRemainder Q split 1) := by
    change inclusion (shiftedOmega_le_phi Q split c) x ∈
      (QuotientGroup.mk' (phiCenterSection Q split c).denominator).ker at hx
    rw [QuotientGroup.ker_mk'] at hx
    exact hx
  exact Subtype.ext (disjoint_def.mp (shiftedOmega_disjoint_center Q split c) x.property hz)

include c in
theorem shiftedOmega_centralizes_suzukiRoot :
    ⁅omegaOneAmbient (positiveRoot Q split (.inr 3)),simpleRoot Q split 1⁆ = ⊥ :=
  source_shifted_omega_commute Q split 1 0 m c.suzuki c.suzukiBorel
    c.linear c.linearSylow c.linearBorel c.rotation_eight (by decide)

theorem phiCenterCoordinates_shiftedOmega
    (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c a)) =
      ![phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c a)) 0,0,0,0] := by
  apply Representation.SuzukiNatural.root_fixed_coordinates
  intro g hg
  let u := (suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel).symm ⟨g,hg⟩
  let r : rankOne Q split 1 := inclusion le_sup_left u
  let v : phi (simpleRemainder Q split 1) := inclusion (shiftedOmega_le_phi Q split c) a
  have hr : suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r = g := by
    change (suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel u : SuzukiMatrixGroup m) = g
    exact congrArg Subtype.val ((suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel).apply_symm_apply ⟨g,hg⟩)
  have hc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (shiftedOmega_centralizes_suzukiRoot Q split c) a.property) _ u.property
  have hv : (phiCenterSection Q split c).numeratorAction r v = v := by
    apply Subtype.ext
    change (u : X ⧸ Q.D) * a * (u : X ⧸ Q.D)⁻¹ = a
    rw [hc.eq, mul_inv_cancel_right]
  have h := phiCenterCoordinates_source Q split c r v
  rw [hr,hv] at h
  exact h.symm

def shiftedOmegaCoordinate (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    Representation.SuzukiNatural.F m :=
  phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c a)) 0

theorem shiftedOmegaCoordinate_injective : Function.Injective (shiftedOmegaCoordinate Q split c) := by
  intro a b hab
  apply phiShiftedOmega_injective Q split c
  apply (phiCenterCoordinates Q split c).injective
  change phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c a)) =
    phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c b))
  rw [phiCenterCoordinates_shiftedOmega Q split c a,
    phiCenterCoordinates_shiftedOmega Q split c b]
  funext i
  fin_cases i
  · exact hab
  all_goals rfl

theorem shiftedOmegaCoordinate_bijective : Function.Bijective (shiftedOmegaCoordinate Q split c) := by
  apply (shiftedOmegaCoordinate_injective Q split c).bijective_of_nat_card_le
  rw [GaloisField.card 2 (2*m+1) (by omega), omega_positiveRoot_card Q split c 3]

def shiftedOmegaLabelHom : omegaOneAmbient (positiveRoot Q split (.inr 3)) →*
    Multiplicative (Representation.SuzukiNatural.F m) where
  toFun a := Multiplicative.ofAdd (shiftedOmegaCoordinate Q split c a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c 1)) 0 = 0
    rw [map_one]
    change (phiCenterCoordinates Q split c).toLinearEquiv 0 0 = 0
    rw [map_zero]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c (a*b))) 0 =
      phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c a)) 0 +
      phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c b)) 0
    rw [map_mul]
    exact congrFun ((phiCenterCoordinates Q split c).toLinearEquiv.map_add
      (Additive.ofMul (phiShiftedOmega Q split c a))
      (Additive.ofMul (phiShiftedOmega Q split c b))) 0

def shiftedOmegaLabel : omegaOneAmbient (positiveRoot Q split (.inr 3)) ≃*
    Multiplicative (Representation.SuzukiNatural.F m) :=
  MulEquiv.ofBijective (shiftedOmegaLabelHom Q split c)
    (Multiplicative.ofAdd.bijective.comp (shiftedOmegaCoordinate_bijective Q split c))

/-- The shifted Omega parameter is the literal positive point with first
Suzuki parameter zero. -/
def shiftedOmegaPoint (b : CoefficientField m) :
    omegaOneAmbient (positiveRoot Q split (.inr 3)) :=
  ⟨positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,b),by
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
      (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (0,b)).property
    change positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,b) ^ 2 = 1
    rw [pow_two,positivePoint_quartet_mul]
    simpa only [zero_add,map_zero,zero_mul,add_zero,CharTwo.add_self_eq_zero] using
      positivePoint_quartet_zero Q split c (RingEquiv.refl _) 3⟩

def shiftedOmegaChartHom : Multiplicative (CoefficientField m) →*
    omegaOneAmbient (positiveRoot Q split (.inr 3)) where
  toFun b := shiftedOmegaPoint Q split c b.toAdd
  map_one' := Subtype.ext (positivePoint_quartet_zero Q split c (RingEquiv.refl _) 3)
  map_mul' a b := by
    apply Subtype.ext
    change positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,a.toAdd+b.toAdd) =
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,a.toAdd) *
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,b.toAdd)
    symm
    simpa only [zero_add,map_zero,zero_mul,add_zero] using
      positivePoint_quartet_mul Q split c (RingEquiv.refl _) 3 0 a.toAdd 0 b.toAdd

theorem shiftedOmegaChartHom_bijective : Function.Bijective (shiftedOmegaChartHom Q split c) := by
  apply Function.Injective.bijective_of_nat_card_le
  · intro a b he
    have he' := congrArg (fun z : omegaOneAmbient (positiveRoot Q split (.inr 3)) =>
      (z : X ⧸ Q.D)) he
    have h := positivePoint_injective Q split c (RingEquiv.refl _) (.inr 3)
      (a₁ := (0,a.toAdd)) (a₂ := (0,b.toAdd)) he'
    exact Multiplicative.toAdd.injective (congrArg Prod.snd h)
  · rw [omega_positiveRoot_card Q split c 3,
      Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 (2*m+1) (by omega)]

def shiftedOmegaChart : Multiplicative (CoefficientField m) ≃*
    omegaOneAmbient (positiveRoot Q split (.inr 3)) :=
  MulEquiv.ofBijective (shiftedOmegaChartHom Q split c) (shiftedOmegaChartHom_bijective Q split c)

/-- The field-label change for the second natural module is already additive;
its compatibility with the first layer is the later comparison (10.9). -/
def shiftedOmegaFieldLabel : CoefficientField m ≃+ CoefficientField m :=
  ((shiftedOmegaChart Q split c).trans (shiftedOmegaLabel Q split c)).toAdditive

theorem shiftedOmegaFieldLabel_coordinates (b : CoefficientField m) :
    phiCenterCoordinates Q split c
      (Additive.ofMul (phiShiftedOmega Q split c (shiftedOmegaPoint Q split c b))) =
        ![shiftedOmegaFieldLabel Q split c b,0,0,0] :=
  phiCenterCoordinates_shiftedOmega Q split c _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
