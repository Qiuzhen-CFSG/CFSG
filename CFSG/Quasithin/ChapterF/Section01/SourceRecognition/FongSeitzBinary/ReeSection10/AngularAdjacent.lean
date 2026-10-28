module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularAdjacent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCommuteFamily
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations

/-!
# The seven adjacent angular equations in the original source quotient

The already proved adjacent-root vanishing and the supplied reflections give
all seven neighboring positive-root commutations, preserving every field label.
Native coordinate uniqueness then identifies these with the literal angular
table, for arbitrary whole-root parameters and also at field two.

Source: Fong--Seitz II, Section 10, pp.221--224, the root-interval consequence
used in (10.2); Fong--Seitz I (3G), pp.14--16. The actual quotient, split
structure and full original (6H) input are unchanged.
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

private theorem adjacent_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem adjacent_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh


private theorem reflect_commute (s : Bool) (i j : Fin 4)
    (hi : (step false s (true,i)).1 = true)
    (hj : (step true s (true,j)).1 = true)
    (a b y : CoefficientField m) (h : Commute (L i a) (S j b y)) :
    Commute (L (next false s i) a) (S (next true s j) b y) := by
  change _ * _ = _ * _
  have hh := congrArg (MulAut.conj (W s)) h.eq
  simpa only [map_mul, adjacent_pair_reflection Q split c s i hi,
    adjacent_quartet_reflection Q split c s j hj] using hh

/-- All seven neighboring angular root groups commute, at the actual labels. -/
theorem synchronized_adjacent_commute_family (a b y : CoefficientField m) :
    Commute (L 1 a) (S 0 b y) ∧
    Commute (L 1 a) (S 3 b y) ∧
    Commute (L 3 a) (S 3 b y) ∧
    Commute (L 3 a) (S 1 b y) ∧
    Commute (L 2 a) (S 1 b y) ∧
    Commute (L 2 a) (S 2 b y) ∧
    Commute (L 0 a) (S 2 b y) := by
  have h67 := synchronized_A0_B2_commute Q split c a b y
  have h12 : Commute (L 1 a) (S 3 b y) := by
    simpa only [next, Matrix.cons_val, Fin.isValue, Matrix.head_cons] using
      reflect_commute Q split c true 0 2 (by decide) (by decide) a b y h67
  have h45 := synchronized_A2_B1_commute Q split c a b y
  have h34 : Commute (L 3 a) (S 1 b y) := by
    simpa only [next, Matrix.cons_val, Fin.isValue, Matrix.head_cons] using
      reflect_commute Q split c true 2 1 (by decide) (by decide) a b y h45
  have h23 : Commute (L 3 a) (S 3 b y) := by
    simpa only [next, Matrix.cons_val, Fin.isValue, Matrix.head_cons] using
      reflect_commute Q split c false 3 1 (by decide) (by decide) a b y h34
  have h56 : Commute (L 2 a) (S 2 b y) := by
    simpa only [next, Matrix.cons_val, Fin.isValue, Matrix.head_cons] using
      reflect_commute Q split c true 3 3 (by decide) (by decide) a b y h23
  have h01 : Commute (L 1 a) (S 0 b y) := by
    simpa only [next, Matrix.cons_val, Fin.isValue, Matrix.head_cons] using
      reflect_commute Q split c false 2 2 (by decide) (by decide) a b y h56
  exact ⟨h01,h12,h23,h34,h45,h56,h67⟩

open ReeF4.CentralCovers.TwoPrimary
/-- Adjacent positions in the exact angular order. -/
def AdjacentAngularPair (i j : PositiveTables.Root) : Prop :=
  (rootIndex i).val + 1 = (rootIndex j).val
instance (i j : PositiveTables.Root) : Decidable (AdjacentAngularPair i j) :=
  inferInstanceAs (Decidable ((rootIndex i).val + 1 = (rootIndex j).val))

private theorem adjacent_cases : ∀ (i j : PositiveTables.Root), AdjacentAngularPair i j →
    (i = .inr 0 ∧ j = .inl 1) ∨
    (i = .inl 1 ∧ j = .inr 3) ∨
    (i = .inr 3 ∧ j = .inl 3) ∨
    (i = .inl 3 ∧ j = .inr 1) ∨
    (i = .inr 1 ∧ j = .inl 2) ∨
    (i = .inl 2 ∧ j = .inr 2) ∨
    (i = .inr 2 ∧ j = .inl 0) := by
  simp only [AdjacentAngularPair, rootIndex,
    ReeF4.NormalizedRootCentralizers.CenterExponent.positive_pair_indices,
    ReeF4.NormalizedRootCentralizers.CenterExponent.positive_quartet_indices]
  decide

/-- All seven adjacent pairs in arbitrary whole-root parameters. -/
theorem synchronized_adjacent_commute (i j : PositiveTables.Root)
    (h : AdjacentAngularPair i j)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    Commute (synchronizedSourceRoot Q split c i u)
      (synchronizedSourceRoot Q split c j v) := by
  obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective u
  obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m j).surjective v
  rw [synchronizedSourceRoot_field Q split c i a,
    synchronizedSourceRoot_field Q split c j b]
  rcases adjacent_cases i j h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (synchronized_adjacent_commute_family Q split c b a.1 a.2).1.symm
  · exact (synchronized_adjacent_commute_family Q split c a b.1 b.2).2.1
  · exact (synchronized_adjacent_commute_family Q split c b a.1 a.2).2.2.1.symm
  · exact (synchronized_adjacent_commute_family Q split c a b.1 b.2).2.2.2.1
  · exact (synchronized_adjacent_commute_family Q split c b a.1 a.2).2.2.2.2.1.symm
  · exact (synchronized_adjacent_commute_family Q split c a b.1 b.2).2.2.2.2.2.1
  · exact (synchronized_adjacent_commute_family Q split c b a.1 a.2).2.2.2.2.2.2.symm

/-- The seven adjacent pairs satisfy the literal native angular table. -/
theorem synchronized_adjacentAngular_equation (i j : PositiveTables.Root)
    (h : AdjacentAngularPair i j)
    (hj : j ∈ Theory.GroupTheory.OrderedRootPresentation.tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      Theory.GroupTheory.OrderedRootPresentation.word (AngularPresentation.Parameter m)
        (fun k => synchronizedSourceRoot Q split c k)
        (Theory.GroupTheory.OrderedRootPresentation.tail sourceOrder i)
        ((AngularPresentation.table m).conjugate i j hj u v) := by
  exact AngularAdjacent.equation_of_commute m (synchronizedSourceRoot Q split c)
    i j hj u v
    (AngularAdjacent.native_adjacent_commute m (rootIndex i) (rootIndex j) h u v)
    (synchronized_adjacent_commute Q split c i j h u v)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
