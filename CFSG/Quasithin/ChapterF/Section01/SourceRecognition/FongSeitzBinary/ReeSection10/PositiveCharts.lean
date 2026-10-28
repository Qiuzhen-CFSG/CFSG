module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.PositiveRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.NativeSuzukiChart
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearCoordinates

/-!
# Eight whole-root charts and unique source unipotent coordinates

The common-field equality transports the additive linear chart to the Ree
coefficient field. The complete Suzuki chart uses the explicit triangular
correction (a,b) ↦ (a,b+a·titsEnd(a)), so its law is exactly the native
high-root law with cocycle titsEnd(a)·c. Literal reflection words transport
these two charts to the eight positive roots. Their zero and multiplication
laws prove every diagonal entry of the native finite exchange table.

Carter's ordered-product equivalence then gives unique twelve-parameter
coordinates on the entire original split U, without mixed-equation inputs.
The linear field automorphism is left variable for the later synchronization
by (10.7)--(10.9). All parameters, including m = 0, are retained.

`positiveChartsOfExchange` is the actual SourcePositive.Charts consumer.
Its distinct-root exchanges remain explicit obligations; this module does
not prove those exchanges, natural-module identification, angular equations,
torus pinning, or recognition of the source with the full Ree model.

Source: Fong--Seitz II (1974), Section 10, pp.221--224 and the root law
preceding (10.32), p.230; native convention: PositiveTables.quartet_mul.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The common-field equality identifies the actual linear source field. -/
def commonField : CoefficientField m ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField n :=
  RingEquiv.cast (R := BenderSuzuki.PFAppendixIII.BinaryGaloisField) c.common_field.symm

/-- Linear labels may later be relabelled by the field automorphism obtained
from the mixed-commutator comparison (10.7). -/
def linearChart (σ : CoefficientField m ≃+* CoefficientField m) :
    Multiplicative (CoefficientField m) ≃* simpleRoot Q split 0 :=
  (AddEquiv.toMultiplicative (σ.trans (commonField Q split c)).toAddEquiv).trans
    (linearRootEquiv Q split 0 c.linear c.linearSylow c.linearBorel).symm

/-- The native high-root convention requires the explicit triangular
correction; the uncorrected matrix chart has the opposite cocycle. -/
def suzukiChart : (CoefficientField m × CoefficientField m) ≃ simpleRoot Q split 1 :=
  (NativeSuzukiChart.coordinateCorrection (m := m)).trans
    (Equiv.ofBijective _ (suzukiParameter_bijective Q split 1 m c.suzuki c.suzukiBorel))

@[simp] theorem suzukiChart_apply (a b : CoefficientField m) :
    suzukiChart Q split c (a,b) =
      suzukiParameter Q split 1 m c.suzuki c.suzukiBorel a (b+a*titsEnd m a) := rfl

theorem suzukiChart_mul (a b u v : CoefficientField m) :
    suzukiChart Q split c (a,b) * suzukiChart Q split c (u,v) =
      suzukiChart Q split c (a+u,b+v+titsEnd m a*u) := by
  rw [suzukiChart_apply, suzukiChart_apply, suzukiParameter_mul, suzukiChart_apply,
    NativeSuzukiChart.suzukiTits_eq_titsEnd]
  congr 1
  simp only [map_add]
  linear_combination (norm := ring_nf)
    -(CharTwo.add_self_eq_zero (titsEnd m a*u))

@[simp] theorem suzukiChart_zero : suzukiChart Q split c (0,0) = 1 := by
  simpa only [suzukiChart_apply, zero_mul, add_zero] using
    suzukiParameter_zero Q split 1 m c.suzuki c.suzukiBorel

def positiveChart (σ : CoefficientField m ≃+* CoefficientField m) :
    (i : PositiveTables.Root) → PositiveTables.Parameter m i ≃ positiveRoot Q split i
  | .inl j => (Multiplicative.ofAdd.trans (linearChart Q split c σ).toEquiv).trans
      (positiveRootEquiv Q split c (.inl j)).toEquiv
  | .inr j => (suzukiChart Q split c).trans
      (positiveRootEquiv Q split c (.inr j)).toEquiv

variable (σ : CoefficientField m ≃+* CoefficientField m)

/-- Literal positive root points in the same quotient. -/
def positivePoint (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) : X ⧸ Q.D :=
  positiveChart Q split c σ i a

theorem positivePoint_injective (i : PositiveTables.Root) :
    Function.Injective (positivePoint Q split c σ i) :=
  Subtype.val_injective.comp (positiveChart Q split c σ i).injective

theorem positivePoint_range (i : PositiveTables.Root) :
    Set.range (positivePoint Q split c σ i) = (positiveRoot Q split i : Set (X ⧸ Q.D)) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩; exact (positiveChart Q split c σ i a).property
  · intro hx
    obtain ⟨a,ha⟩ := (positiveChart Q split c σ i).surjective ⟨x,hx⟩
    exact ⟨a,congrArg Subtype.val ha⟩

theorem positivePoint_mem_unipotent (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    positivePoint Q split c σ i a ∈ split.U :=
  positiveRoot_le_unipotent Q split c.rotation_eight i (positiveChart Q split c σ i a).property

theorem positivePoint_pair_mul (i : Fin 4) (a b : CoefficientField m) :
    positivePoint Q split c σ (.inl i) a * positivePoint Q split c σ (.inl i) b =
      positivePoint Q split c σ (.inl i) (a+b) := by
  exact congrArg Subtype.val ((positiveRootEquiv Q split c (.inl i)).map_mul
    (linearChart Q split c σ (Multiplicative.ofAdd a))
    (linearChart Q split c σ (Multiplicative.ofAdd b))).symm |>.trans
      (congrArg (fun z => (positiveRootEquiv Q split c (.inl i) z : X ⧸ Q.D))
        ((linearChart Q split c σ).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)).symm)

theorem positivePoint_quartet_mul (i : Fin 4) (a b u v : CoefficientField m) :
    positivePoint Q split c σ (.inr i) (a,b) * positivePoint Q split c σ (.inr i) (u,v) =
      positivePoint Q split c σ (.inr i) (a+u,b+v+titsEnd m a*u) := by
  exact (congrArg Subtype.val ((positiveRootEquiv Q split c (.inr i)).map_mul
    (suzukiChart Q split c (a,b)) (suzukiChart Q split c (u,v)))).symm.trans
      (congrArg (fun z : simpleRoot Q split 1 =>
        (positiveRootEquiv Q split c (.inr i) z : X ⧸ Q.D))
          (suzukiChart_mul Q split c a b u v))

@[simp] theorem positivePoint_pair_zero (i : Fin 4) : positivePoint Q split c σ (.inl i) 0 = 1 := by
  exact (congrArg (fun z : simpleRoot Q split 0 =>
    (positiveRootEquiv Q split c (.inl i) z : X ⧸ Q.D)) (map_one (linearChart Q split c σ))).trans
      (congrArg Subtype.val (map_one (positiveRootEquiv Q split c (.inl i))))

@[simp] theorem positivePoint_quartet_zero (i : Fin 4) : positivePoint Q split c σ (.inr i) (0,0) = 1 := by
  exact (congrArg (fun z : simpleRoot Q split 1 =>
    (positiveRootEquiv Q split c (.inr i) z : X ⧸ Q.D)) (suzukiChart_zero Q split c)).trans
      (congrArg Subtype.val (map_one (positiveRootEquiv Q split c (.inr i))))

private theorem positivePoint_word_single (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    PositivePresentation.word (positivePoint Q split c σ) (PositiveTables.single i a) =
      positivePoint Q split c σ i a := by
  cases i with
  | inl j => fin_cases j <;> simp [PositivePresentation.word, PositiveTables.single,
      List.ofFn_succ, positivePoint_pair_zero, positivePoint_quartet_zero]
  | inr j => fin_cases j <;> simp [PositivePresentation.word, PositiveTables.single,
      List.ofFn_succ, positivePoint_pair_zero, positivePoint_quartet_zero]

/-- The diagonal entries of the native exchange table follow from the proved
whole-root laws, including the nontrivial Suzuki cocycle. -/
theorem positivePoint_diagonal_exchange (i : PositiveTables.Root)
    (a b : PositiveTables.Parameter m i) :
    positivePoint Q split c σ i a * positivePoint Q split c σ i b =
      PositivePresentation.word (positivePoint Q split c σ) (PositiveTables.exchange i i a b) := by
  cases i with
  | inl j =>
    have he : PositiveTables.exchange (.inl j) (.inl j) a b =
        PositiveTables.single (.inl j) (a+b) := by
      apply PositiveTables.exchange_unique
      rw [PositiveTables.product_single]
      exact PositiveTables.pair_mul j a b
    rw [he, positivePoint_word_single]
    exact positivePoint_pair_mul Q split c σ j a b
  | inr j =>
    have he : PositiveTables.exchange (.inr j) (.inr j) a b =
        PositiveTables.single (.inr j) (a.1+b.1,a.2+b.2+titsEnd m a.1*b.1) := by
      apply PositiveTables.exchange_unique
      rw [PositiveTables.product_single]
      exact PositiveTables.quartet_mul j a.1 a.2 b.1 b.2
    rw [he, positivePoint_word_single]
    exact positivePoint_quartet_mul Q split c σ j a.1 a.2 b.1 b.2

open Theory.GroupTheory.OrderedRootPresentation

def positiveChartTuple : (l : List PositiveTables.Root) →
    Tuple (PositiveTables.Parameter m) l ≃ RootTuple (l.map (positiveRoot Q split))
  | [] => {
      toFun := fun _ => PUnit.unit
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | i::l => Equiv.prodCongr (positiveChart Q split c σ i) (positiveChartTuple l)

private theorem chartTuple_word (l : List PositiveTables.Root)
    (a : Tuple (PositiveTables.Parameter m) l) :
    rootProduct (l.map (positiveRoot Q split)) (positiveChartTuple Q split c σ l a) =
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) l a := by
  induction l with
  | nil => rfl
  | cons i l ih => exact congrArg (positivePoint Q split c σ i a.1 * ·) (ih a.2)

private theorem rootProduct_cast (l k : List (Subgroup (X ⧸ Q.D))) (h : l = k)
    (a : RootTuple l) :
    rootProduct k (Equiv.cast (congrArg RootTuple h) a) = rootProduct l a := by
  subst k
  rfl

/-- The twelve field parameters in the actual Carter order. -/
abbrev PositiveParameters (m : ℕ) :=
  Tuple (PositiveTables.Parameter m) (List.ofFn positiveIndex)

/-- Whole-U coordinates use only the root charts and the already proved
Carter product theorem. Mixed commutator coefficients are not an input. -/
def positiveCoordinates : PositiveParameters m ≃ split.U :=
  ((positiveChartTuple Q split c σ (List.ofFn positiveIndex)).trans
    (Equiv.cast (congrArg RootTuple (show
      (List.ofFn positiveIndex).map (positiveRoot Q split) =
        orderedRoots Q split false (rotationOrder Q) from by
          rw [c.rotation_eight, positiveRoot_ordered Q split c.rotation_eight, List.map_ofFn]
          rfl)))).trans
      (unipotentOrderedCoordinates Q split false)

theorem positiveCoordinates_apply (a : PositiveParameters m) :
    (positiveCoordinates Q split c σ a : X ⧸ Q.D) =
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) (List.ofFn positiveIndex) a := by
  unfold positiveCoordinates
  rw [Equiv.trans_apply, Equiv.trans_apply, unipotentOrderedCoordinates_apply]
  exact (rootProduct_cast Q _ _ (by
    rw [c.rotation_eight, positiveRoot_ordered Q split c.rotation_eight, List.map_ofFn]
    rfl) _).trans (chartTuple_word Q split c σ _ a)

/-- Every element of the literal source U has a unique twelve-parameter word. -/
theorem positiveWord_unique (u : split.U) :
    ∃! a : PositiveParameters m,
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) (List.ofFn positiveIndex) a = u := by
  refine ⟨(positiveCoordinates Q split c σ).symm u, ?_, ?_⟩
  · exact (positiveCoordinates_apply Q split c σ _).symm.trans
      (congrArg Subtype.val ((positiveCoordinates Q split c σ).apply_symm_apply u))
  · intro a ha
    apply (positiveCoordinates Q split c σ).injective
    apply Subtype.ext
    exact (positiveCoordinates_apply Q split c σ a).trans
      (ha.trans (congrArg Subtype.val ((positiveCoordinates Q split c σ).apply_symm_apply u)).symm)

/-- All geometric and single-root obligations of SourcePositive.Charts are
constructed. Only the two-root exchange coefficients remain explicit here. -/
def positiveChartsOfExchange
    (hexchange : ∀ i j, i ≠ j → ∀ a b,
      positivePoint Q split c σ i a * positivePoint Q split c σ j b =
        PositivePresentation.word (positivePoint Q split c σ) (PositiveTables.exchange i j a b)) :
    SourcePositive.Charts Q split m where
  orientation := false
  rotation_eight := c.rotation_eight
  index := positiveIndex
  root := positiveRoot Q split
  order_eq := positiveRoot_ordered Q split c.rotation_eight
  chart := positiveChart Q split c σ
  equations := {
    pair_zero := positivePoint_pair_zero Q split c σ
    quartet_zero := positivePoint_quartet_zero Q split c σ
    exchange := fun i j a b => by
      by_cases hij : i = j
      · subst j
        exact positivePoint_diagonal_exchange Q split c σ i a b
      · exact hexchange i j hij a b }

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
