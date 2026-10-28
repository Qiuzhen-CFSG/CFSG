module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularShortCompletion

/-!
# The terminal short mixed ordered source equation

Conjugate the checked (1,4) equation by the supplied Suzuki reflection, then
reverse conjugation. The correction lies on the opposite Omega root and is
an involution, so its exact coefficient a*y is retained, including at q=2.
The native tail calculation identifies the literal angular table entry.
Together with the four prior short cases, this completes that equation family.

Source: Fong--Seitz II (1974), Section 10, (10.11)(i) and its Weyl transforms.
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


private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) : b*a*b⁻¹ = z⁻¹*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = _ := by group

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,synchronizedPositivePoint_quartet_zero]


/-- The last short mixed source relation, with the literal Omega parameter. -/
theorem synchronized_short_terminal_conjugate (a b y : CoefficientField m) :
    S 1 a b * L 0 y * (S 1 a b)⁻¹ = S 2 0 (a*y) * L 0 y := by
  have h := congrArg (MulAut.conj (W true))
    (synchronized_short_perpendicular_conjugate Q split c a b y)
  have hh : L 0 y * S 1 a b * (L 0 y)⁻¹ = S 2 0 (a*y) * S 1 a b := by
    simpa only [map_mul,map_inv,batch_pair_reflection Q split c true 1 (by decide),
      batch_quartet_reflection Q split c true 1 (by decide),
      batch_quartet_reflection Q split c true 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [omega_inv] using reverse_conjugate hh

open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary

/-- The literal native-table equation at angular positions 4 and 7. -/
theorem synchronized_terminalAngular_equation
    (hj : (.inl 0 : PositiveTables.Root) ∈ tail sourceOrder (.inr 1))
    (u : AngularPresentation.Parameter m (.inr 1))
    (v : AngularPresentation.Parameter m (.inl 0)) :
    synchronizedSourceRoot Q split c (.inr 1) u * synchronizedSourceRoot Q split c (.inl 0) v *
      (synchronizedSourceRoot Q split c (.inr 1) u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 1))
        ((AngularPresentation.table m).conjugate (.inr 1) (.inl 0) hj u v) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 1)).surjective u
  obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 0)).surjective v
  rw [AngularShortCompletion.table47,AngularShortCompletion.tail47_word]
  rw [synchronizedSourceRoot_field Q split c (.inr 1) (a,b),
    synchronizedSourceRoot_field Q split c (.inl 0) y,
    synchronizedSourceRoot_field Q split c (.inr 2) (0,a*y)]
  exact synchronized_short_terminal_conjugate Q split c a b y

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
