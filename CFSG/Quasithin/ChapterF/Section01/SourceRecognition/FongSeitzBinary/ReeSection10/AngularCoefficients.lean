module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCentralCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients

/-!
# Five literal ordered Section 10 parameter equations

The synchronized Phi calculation supplies the complete next-linear action,
including its central coefficient a theta(y). The perpendicular action and
its reflection transports give four further short mixed equations. The
original supplied lifts preserve the synchronized field labels throughout.

The independently computed native vectors and angular-coordinate uniqueness
identify each result with the exact chosen angular table. This discharges
five whole-root cases of `OrderedRootPresentation.Equations` directly from
`ReeSixHData`, with no field-size restriction. The assembly theorem consumes
only the remaining 23 cases; it does not assume a model comparison.

Source: Fong--Seitz II (1974), printed pp.224--226, (10.11)(i), (10.13)(i)
and (10.15); GLS3 Table 2.4 and 2.4.5(d) for the native coefficients.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

private theorem batch_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh

private theorem batch_simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem batch_quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  have he : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [he,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]

/-- Literal forward conjugation, with both Suzuki coordinates retained. -/
theorem synchronized_short_conjugate (a b y : CoefficientField m) :
    S 0 a b * L 3 y * (S 0 a b)⁻¹ = S 3 0 (a*y) * L 3 y := by
  have h := synchronized_ten_eleven_i_commutator Q split c a b y
  rw [commutatorElement_def,←batch_simple_suzuki] at h
  have hh := congrArg (fun t => t * L 3 y) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The central term is retained in the literal ordered next-linear action. -/
theorem synchronized_next_conjugate (a b y : CoefficientField m) :
    S 0 a b * L 2 y * (S 0 a b)⁻¹ =
      S 3 0 ((b+titsEnd m a*a)*y) * L 3 (titsEnd m a*y) *
        S 1 0 (a*titsEnd m y) * L 2 y := by
  let d := pinnedInput Q split c
  let : IsElementaryAbelian 2 (phiCenterSection Q split d).numerator :=
    phiRemainder_elementary Q split d
  have h := synchronized_nextLinear_commutator Q split c a (b+titsEnd m a*a) y
  have h' := congrArg (fun v : (phiCenterSection Q split d).numerator =>
    (phiNextPoint Q split c y * v : (phiCenterSection Q split d).numerator)) h
  have he : phiNextPoint Q split c y *
      (phiCentralPoint Q split c (a*titsEnd m y) *
        (phiShiftedPoint Q split c ((b+titsEnd m a*a)*y) *
          phiPerpendicularPoint Q split c (titsEnd m a*y))) =
      phiShiftedPoint Q split c ((b+titsEnd m a*a)*y) *
        phiPerpendicularPoint Q split c (titsEnd m a*y) *
          phiCentralPoint Q split c (a*titsEnd m y) * phiNextPoint Q split c y := by ac_rfl
  rw [he] at h'
  have hv := congrArg (fun v : (phiCenterSection Q split d).numerator => (v : X ⧸ Q.D)) h'
  change L 2 y * (phiRightCommutator Q split d
    (suzukiChart Q split d (a,b+titsEnd m a*a)) (phiNextPoint Q split c y) : X ⧸ Q.D) = _ at hv
  rw [phiRightCommutator_val] at hv
  dsimp only [d] at hv
  rw [←batch_simple_suzuki] at hv
  change L 2 y * ((L 2 y)⁻¹ * (S 0 a (b+titsEnd m a*a))⁻¹ * L 2 y *
    S 0 a (b+titsEnd m a*a)) =
      S 3 0 ((b+titsEnd m a*a)*y) * L 3 (titsEnd m a*y) *
        S 1 0 (a*titsEnd m y) * L 2 y at hv
  rw [←batch_quartet_inv,inv_inv] at hv
  simpa only [mul_assoc,mul_inv_cancel_left] using hv

private theorem conjugate_reverse {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) (hz : z⁻¹ = z) : b*a*b⁻¹ = z*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = z⁻¹*a := by group
    _ = _ := by rw [hz]

private theorem short_opposite (a b y : CoefficientField m) :
    S 2 a b * L 3 y * (S 2 a b)⁻¹ = S 1 0 (a*y) * L 3 y := by
  have h := congrArg (MulAut.conj (W false)) (synchronized_short_conjugate Q split c a b y)
  simpa only [map_mul,map_inv,batch_quartet_reflection Q split c false 0 (by decide),
    batch_quartet_reflection Q split c false 3 (by decide),batch_pair_reflection Q split c false 3 (by decide),
    next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h

/-- Ordered angular positions 3 and 6: the reflected short equation. -/
theorem synchronized_short_reflected_conjugate (a b y : CoefficientField m) :
    L 3 y * S 2 a b * (L 3 y)⁻¹ = S 1 0 (a*y) * S 2 a b := by
  apply conjugate_reverse (short_opposite Q split c a b y)
  simpa only [map_zero,zero_mul,add_zero] using batch_quartet_inv Q split c 1 0 (a*y)

/-- Ordered angular positions 2 and 5: transport by the two supplied reflections. -/
theorem synchronized_short_shifted_conjugate (a b y : CoefficientField m) :
    S 3 a b * L 2 y * (S 3 a b)⁻¹ = S 1 0 (a*y) * L 2 y := by
  have h := congrArg (MulAut.conj (W true)) (short_opposite Q split c a b y)
  simpa only [map_mul,map_inv,batch_quartet_reflection Q split c true 2 (by decide),
    batch_quartet_reflection Q split c true 1 (by decide),batch_pair_reflection Q split c true 3 (by decide),
    next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h

/-- Ordered angular positions 1 and 4: the remaining short equation. -/
theorem synchronized_short_perpendicular_conjugate (a b y : CoefficientField m) :
    L 1 y * S 1 a b * (L 1 y)⁻¹ = S 3 0 (a*y) * S 1 a b := by
  have h := congrArg (MulAut.conj (W false)) (synchronized_short_shifted_conjugate Q split c a b y)
  have hh : S 1 a b * L 1 y * (S 1 a b)⁻¹ = S 3 0 (a*y) * L 1 y := by
    simpa only [map_mul,map_inv,batch_quartet_reflection Q split c false 3 (by decide),
      batch_quartet_reflection Q split c false 1 (by decide),batch_pair_reflection Q split c false 2 (by decide),
      next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  apply conjugate_reverse hh
  simpa only [map_zero,zero_mul,add_zero] using batch_quartet_inv Q split c 3 0 (a*y)

open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary

/-- The five nontrivial ordered root pairs computed in this module. Indices are
literal chart indices, with the native angular order retained. -/
def ComputedAngularPair (i j : PositiveTables.Root) : Prop :=
  (i = .inr 0 ∧ j = .inl 3) ∨
  (i = .inl 1 ∧ j = .inr 1) ∨
  (i = .inr 3 ∧ j = .inl 2) ∨
  (i = .inl 3 ∧ j = .inr 2) ∨
  (i = .inr 0 ∧ j = .inl 2)

instance (i j : PositiveTables.Root) : Decidable (ComputedAngularPair i j) :=
  by unfold ComputedAngularPair; infer_instance

/-- These are equations against the literal native angular table, with arbitrary
whole-root parameters. No positive-equation or comparison premise is used. -/
theorem synchronized_computedAngular_equation (i j : PositiveTables.Root)
    (h : ComputedAngularPair i j) (hj : j ∈ tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj u v) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 0)).surjective u
    obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 3)).surjective v
    rw [AngularCoefficients.table03,AngularCoefficients.tail03_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) (a,b),
      synchronizedSourceRoot_field Q split c (.inl 3) y,
      synchronizedSourceRoot_field Q split c (.inr 3) (0,a*y)]
    exact synchronized_short_conjugate Q split c a b y
  · obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 1)).surjective u
    obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 1)).surjective v
    rw [AngularCoefficients.table14,AngularCoefficients.tail14_word]
    rw [synchronizedSourceRoot_field Q split c (.inl 1) y,
      synchronizedSourceRoot_field Q split c (.inr 1) (a,b),
      synchronizedSourceRoot_field Q split c (.inr 3) (0,a*y)]
    exact synchronized_short_perpendicular_conjugate Q split c a b y
  · obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 3)).surjective u
    obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 2)).surjective v
    rw [AngularCoefficients.table25,AngularCoefficients.tail25_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 3) (a,b),
      synchronizedSourceRoot_field Q split c (.inl 2) y,
      synchronizedSourceRoot_field Q split c (.inr 1) (0,a*y)]
    exact synchronized_short_shifted_conjugate Q split c a b y
  · obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 3)).surjective u
    obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 2)).surjective v
    rw [AngularCoefficients.table36,AngularCoefficients.tail36_word]
    rw [synchronizedSourceRoot_field Q split c (.inl 3) y,
      synchronizedSourceRoot_field Q split c (.inr 2) (a,b),
      synchronizedSourceRoot_field Q split c (.inr 1) (0,a*y)]
    exact synchronized_short_reflected_conjugate Q split c a b y
  · obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 0)).surjective u
    obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 2)).surjective v
    rw [AngularCoefficients.table05,AngularCoefficients.tail05_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) (a,b),
      synchronizedSourceRoot_field Q split c (.inl 2) y,
      synchronizedSourceRoot_field Q split c (.inr 3) (0,(b+titsEnd m a*a)*y),
      synchronizedSourceRoot_field Q split c (.inl 3) (titsEnd m a*y),
      synchronizedSourceRoot_field Q split c (.inr 1) (0,a*titsEnd m y)]
    exact synchronized_next_conjugate Q split c a b y

/-- The still outstanding angular cases; the five computed cases are excluded.
This retains the exact native coefficients, including every binary correction. -/
def RemainingAngularEquations : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Actual assembly of the completed cases with the remaining 23 ordered pairs. -/
theorem synchronizedAngularEquations_of_remaining
    (h : RemainingAngularEquations Q split c) :
    OrderedRootPresentation.Equations (AngularPresentation.table m)
      (synchronizedSourceRoot Q split c) := by
  intro i j hj a b
  by_cases hij : ComputedAngularPair i j
  · exact synchronized_computedAngular_equation Q split c i j hij hj a b
  · exact h i j hij hj a b

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
