module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusSimpleActions
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.TorusCharts
/-!
# The full synchronized torus action on the positive roots

The two source rank-one torus tables give the action of their product on
all four linear and four whole Suzuki roots. The native character table,
after the proved change of torus parameters, has exactly these weights.
This proves the literal `SourceBorel.rootAction` equations for synchronized
charts, including each Suzuki center and the binary field.

Source: Fong--Seitz II (1974), (10.10)--(10.12), printed pp.223--224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open ReeF4.CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 RootPresentationRecognition Parabolics.RadicalCoordinates.FixedCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {m : ℕ}
private theorem pow_tits (x : CoefficientField m) : x^(2*2^m) = titsEnd m x := by
  rw [titsEnd_apply, pow_succ]
  congr 1
  exact Nat.mul_comm _ _
private theorem pow_twice_tits (x : CoefficientField m) : x^(4*2^m) = (titsEnd m x)^2 := by
  rw [←pow_tits, ←pow_mul]
  congr 1
  omega
private theorem half_tits (x : CoefficientField m) : (titsEnd m x)^(2^m) = x :=
  halfFrobenius_titsEnd m x
private theorem pow_tits' (x : CoefficientField m) : x^(2^m*2) = titsEnd m x := by
  rw [titsEnd_apply,pow_succ]

def sourcePairWeight (a b : (CoefficientField m)ˣ) : Fin 4 → CoefficientField m :=
  ![(a : CoefficientField m)⁻¹^2*((b : CoefficientField m)^(1+2^m))⁻¹,
    titsEnd m a*(b : CoefficientField m)^(1+2^m),
    (titsEnd m a)⁻¹*((b : CoefficientField m)^(2^m))⁻¹,
    (b : CoefficientField m)^(2^m)]

def sourceQuartetWeight (a b : (CoefficientField m)ˣ) : Fin 4 → CoefficientField m :=
  ![(a : CoefficientField m)*b,(titsEnd m a)⁻¹*(a : CoefficientField m),
    (a : CoefficientField m)⁻¹*((b : CoefficientField m)^(2^m))⁻¹,
    titsEnd m a*(a : CoefficientField m)⁻¹*(b : CoefficientField m)^(2^m)]

theorem sourcePairWeight_native (a b : (CoefficientField m)ˣ) (i : Fin 4) :
    (TorusCharts.character (torusCharacters (a⁻¹,b⁻¹)) (.inl i) : CoefficientField m) =
      sourcePairWeight a b i := by
  rw [TorusCharts.character_pair]
  fin_cases i <;>
    simp only [sourcePairWeight, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals simp only [
      torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv, inv_pow, pow_add, pow_one,
      pow_tits, pow_twice_tits, map_mul, map_inv₀, map_pow]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [pow_tits',half_tits]
  all_goals first | rfl | exact mul_comm _ _

theorem sourceQuartetWeight_native (a b : (CoefficientField m)ˣ) (i : Fin 4) :
    (TorusCharts.character (torusCharacters (a⁻¹,b⁻¹)) (.inr i) : CoefficientField m) =
      sourceQuartetWeight a b i := by
  rw [TorusCharts.character_quartet]
  fin_cases i <;>
    simp only [sourceQuartetWeight, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals simp only [
      torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv, inv_pow, pow_add, pow_one,
      pow_tits, map_mul, map_inv₀, map_pow]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [pow_tits',half_tits]

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n : ℕ}
  (c : ReeSixHData Q split n m)

private theorem point_simple_linear (x : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inl 0) x =
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) := by
  change (1 : X ⧸ Q.D)⁻¹ * _ * 1 = _
  simp only [inv_one,one_mul,mul_one,Equiv.trans_apply]
  rfl

private theorem point_simple_suzuki (x y : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr 0) (x,y) =
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) := by
  change (1 : X ⧸ Q.D)⁻¹ * _ * 1 = _
  simp only [inv_one,one_mul,mul_one]

theorem synchronizedTorus_pair_right (a b : (CoefficientField m)ˣ)
    (i : Fin 4) (x : CoefficientField m) :
    (synchronizedTorus Q split c (a,b))⁻¹ * synchronizedPositivePoint Q split c (.inl i) x *
        synchronizedTorus Q split c (a,b) =
      synchronizedPositivePoint Q split c (.inl i) (sourcePairWeight a b i*x) := by
  rw [synchronizedTorus_apply Q split c]
  calc
    _ = (synchronizedSuzukiTorus Q split c b)⁻¹ *
      ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inl i) x *
        synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b := by group
    _ = _ := by
      fin_cases i
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inl 0) x *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inl 0) (sourcePairWeight a b 0*x)
        rw [point_simple_linear Q split c, synchronizedLinearTorus_simple Q split c, synchronizedSuzukiTorus_linear Q split c,
          point_simple_linear Q split c]
        congr 2
        dsimp [sourcePairWeight]
        ac_rfl
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inl 1) x *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inl 1) (sourcePairWeight a b 1*x)
        rw [synchronizedLinearTorus_reflectedLinear Q split c, synchronizedSuzukiTorus_reflectedLinear Q split c]
        congr 1
        dsimp [sourcePairWeight]
        ac_rfl
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inl 2) x *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inl 2) (sourcePairWeight a b 2*x)
        rw [synchronizedLinearTorus_nextLinear Q split c, synchronizedSuzukiTorus_nextLinear Q split c]
        congr 1
        dsimp [sourcePairWeight]
        ac_rfl
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inl 3) x *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inl 3) (sourcePairWeight a b 3*x)
        rw [synchronizedLinearTorus_perpendicularLinear Q split c, synchronizedSuzukiTorus_perpendicularLinear Q split c]
        rfl

theorem synchronizedTorus_quartet_right (a b : (CoefficientField m)ˣ)
    (i : Fin 4) (x y : CoefficientField m) :
    (synchronizedTorus Q split c (a,b))⁻¹ * synchronizedPositivePoint Q split c (.inr i) (x,y) *
        synchronizedTorus Q split c (a,b) =
      synchronizedPositivePoint Q split c (.inr i)
        (sourceQuartetWeight a b i*x,sourceQuartetWeight a b i*titsEnd m (sourceQuartetWeight a b i)*y) := by
  rw [synchronizedTorus_apply Q split c]
  calc
    _ = (synchronizedSuzukiTorus Q split c b)⁻¹ *
      ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inr i) (x,y) *
        synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b := by group
    _ = _ := by
      fin_cases i
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inr 0) (x,y) *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inr 0) (sourceQuartetWeight a b 0*x,sourceQuartetWeight a b 0*titsEnd m (sourceQuartetWeight a b 0)*y)
        rw [point_simple_suzuki Q split c, synchronizedLinearTorus_suzuki Q split c, synchronizedSuzukiTorus_simple Q split c,
          point_simple_suzuki Q split c]
        dsimp [sourceQuartetWeight]
        simp only [map_mul]
        congr 2 <;> ring
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inr 1) (x,y) *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inr 1) (sourceQuartetWeight a b 1*x,sourceQuartetWeight a b 1*titsEnd m (sourceQuartetWeight a b 1)*y)
        rw [synchronizedLinearTorus_perpendicularSuzuki Q split c, synchronizedSuzukiTorus_perpendicular Q split c]
        rfl
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inr 2) (x,y) *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inr 2) (sourceQuartetWeight a b 2*x,sourceQuartetWeight a b 2*titsEnd m (sourceQuartetWeight a b 2)*y)
        rw [synchronizedLinearTorus_oppositeSuzuki Q split c, synchronizedSuzukiTorus_opposite Q split c]
        dsimp [sourceQuartetWeight]
        simp only [map_mul,map_inv₀]
        congr 2 <;> ring
      · change (synchronizedSuzukiTorus Q split c b)⁻¹ *
          ((synchronizedLinearTorus Q split c a)⁻¹ * synchronizedPositivePoint Q split c (.inr 3) (x,y) *
            synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b =
          synchronizedPositivePoint Q split c (.inr 3) (sourceQuartetWeight a b 3*x,sourceQuartetWeight a b 3*titsEnd m (sourceQuartetWeight a b 3)*y)
        rw [synchronizedLinearTorus_shiftedSuzuki Q split c, synchronizedSuzukiTorus_shifted Q split c]
        dsimp [sourceQuartetWeight]
        simp only [map_mul]
        congr 2 <;> ring


theorem normalizedSynchronizedTorus_pair (t : TorusParameter m)
    (i : Fin 4) (x : CoefficientField m) :
    normalizedSynchronizedTorus Q split c t * synchronizedPositivePoint Q split c (.inl i) x *
        (normalizedSynchronizedTorus Q split c t)⁻¹ =
      synchronizedPositivePoint Q split c (.inl i)
        ((TorusCharts.character t (.inl i) : CoefficientField m)*x) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (torusCharacterEquiv (m := m)).surjective t
  change normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) * _ *
      (normalizedSynchronizedTorus Q split c (torusCharacters (a,b)))⁻¹ =
    synchronizedPositivePoint Q split c (.inl i)
      ((TorusCharts.character (torusCharacters (a,b)) (.inl i) : CoefficientField m)*x)
  rw [normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply]
  have h := synchronizedTorus_pair_right Q split c a⁻¹ b⁻¹ i x
  have he : synchronizedTorus Q split c (a⁻¹,b⁻¹) =
      (synchronizedTorus Q split c (a,b))⁻¹ := map_inv _ (a,b)
  rw [he,inv_inv,←sourcePairWeight_native,inv_inv,inv_inv] at h
  exact h

theorem normalizedSynchronizedTorus_quartet (t : TorusParameter m)
    (i : Fin 4) (x y : CoefficientField m) :
    normalizedSynchronizedTorus Q split c t * synchronizedPositivePoint Q split c (.inr i) (x,y) *
        (normalizedSynchronizedTorus Q split c t)⁻¹ =
      synchronizedPositivePoint Q split c (.inr i)
        ((TorusCharts.character t (.inr i) : CoefficientField m)*x,
          (TorusCharts.character t (.inr i) : CoefficientField m)*
            titsEnd m (TorusCharts.character t (.inr i))*y) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (torusCharacterEquiv (m := m)).surjective t
  change normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) * _ *
      (normalizedSynchronizedTorus Q split c (torusCharacters (a,b)))⁻¹ =
    synchronizedPositivePoint Q split c (.inr i)
      ((TorusCharts.character (torusCharacters (a,b)) (.inr i) : CoefficientField m)*x,
        (TorusCharts.character (torusCharacters (a,b)) (.inr i) : CoefficientField m)*
          titsEnd m (TorusCharts.character (torusCharacters (a,b)) (.inr i))*y)
  rw [normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply]
  have h := synchronizedTorus_quartet_right Q split c a⁻¹ b⁻¹ i x y
  have he : synchronizedTorus Q split c (a⁻¹,b⁻¹) =
      (synchronizedTorus Q split c (a,b))⁻¹ := map_inv _ (a,b)
  rw [he,inv_inv,←sourceQuartetWeight_native,inv_inv,inv_inv] at h
  exact h

variable (d : SourcePositive.Charts Q split m)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)

include hd in
theorem normalizedSynchronizedTorus_action (t : TorusParameter m)
    (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    normalizedSynchronizedTorus Q split c t * SourceAngular.sourceRoot Q split d i a *
        (normalizedSynchronizedTorus Q split c t)⁻¹ =
      SourceAngular.sourceRoot Q split d i
        (SourceBorel.rootAction (fixedTorusEquiv m t) i a) := by
  rcases i with i|i
  · obtain ⟨x,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl i)).surjective a
    rw [TorusCharts.pair_action,SourceAngular.sourceRoot_field,SourceAngular.sourceRoot_field,hd,hd]
    exact normalizedSynchronizedTorus_pair Q split c t i x
  · obtain ⟨⟨x,y⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr i)).surjective a
    rw [TorusCharts.quartet_action,SourceAngular.sourceRoot_field,SourceAngular.sourceRoot_field,hd,hd]
    exact normalizedSynchronizedTorus_quartet Q split c t i x y

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
