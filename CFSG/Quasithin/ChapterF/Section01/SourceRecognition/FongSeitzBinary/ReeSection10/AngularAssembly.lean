module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedCommutators
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceAngular

/-!
# Positive source charts assembled from one angular equation family

The synchronized one- and two-field charts are homomorphisms on every
whole native root: the linear law is additive and the Suzuki law retains
its Tits cocycle. These homomorphisms are constructed before any mixed
relations are assumed.

Once their literal angular equations are proved, the native angular
presentation constructs evaluation from native U to the same marked
quotient. Applying that homomorphism to the native two-root exchanges
supplies every equation required by SourcePositive.Charts. Thus the source
owner only has to prove the angular coefficients once; the separately
ordered PositiveTables exchanges need no second coefficient calculation.
The resulting charts use the supplied synchronized parameters and retain
their Carter root placements. The angular equation family remains an
explicit hypothesis here, including its central coefficients at q = 2.

Source: Fong--Seitz II (1974), Section 10, pp.225--232; the proved native
angular presentation uses GLS3 2.4.5--6.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

theorem synchronizedPositivePoint_pair_mul (i : Fin 4) (a b : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inl i) a *
      synchronizedPositivePoint Q split c (.inl i) b =
      synchronizedPositivePoint Q split c (.inl i) (a+b) := by
  exact (congrArg Subtype.val ((positiveRootEquiv Q split (pinnedInput Q split c) (.inl i)).map_mul
    (synchronizedLinearChart Q split c (.ofAdd a))
    (synchronizedLinearChart Q split c (.ofAdd b)))).symm.trans
      (congrArg (fun z => (positiveRootEquiv Q split (pinnedInput Q split c) (.inl i) z : X ⧸ Q.D))
        ((synchronizedLinearChart Q split c).map_mul (.ofAdd a) (.ofAdd b)).symm)

theorem synchronizedPositivePoint_quartet_mul (i : Fin 4) (a b u v : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr i) (a,b) *
      synchronizedPositivePoint Q split c (.inr i) (u,v) =
      synchronizedPositivePoint Q split c (.inr i) (a+u,b+v+titsEnd m a*u) :=
  positivePoint_quartet_mul Q split (pinnedInput Q split c) (RingEquiv.refl _) i a b u v

@[simp] theorem synchronizedPositivePoint_pair_zero (i : Fin 4) :
    synchronizedPositivePoint Q split c (.inl i) 0 = 1 := by
  exact (congrArg (fun z =>
    (positiveRootEquiv Q split (pinnedInput Q split c) (.inl i) z : X ⧸ Q.D))
      (map_one (synchronizedLinearChart Q split c))).trans
    (congrArg Subtype.val (map_one (positiveRootEquiv Q split (pinnedInput Q split c) (.inl i))))

@[simp] theorem synchronizedPositivePoint_quartet_zero (i : Fin 4) :
    synchronizedPositivePoint Q split c (.inr i) (0,0) = 1 :=
  positivePoint_quartet_zero Q split (pinnedInput Q split c) (RingEquiv.refl _) i

/-- The whole-root equivalence in the unchanged synchronized field labels. -/
def synchronizedParameterEquiv (i : PositiveTables.Root) :
    AngularPresentation.Parameter m i ≃ positiveRoot Q split i :=
  (PositiveTables.rootChartEquiv m i).symm.trans (synchronizedPositiveChart Q split c i)

@[simp] theorem synchronizedParameterEquiv_field (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) :
    synchronizedParameterEquiv Q split c i (PositiveTables.rootChartEquiv m i a) =
      synchronizedPositiveChart Q split c i a := by
  simp only [synchronizedParameterEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem synchronizedParameterEquiv_mul (i : PositiveTables.Root)
    (a b : AngularPresentation.Parameter m i) :
    synchronizedParameterEquiv Q split c i (a*b) =
      synchronizedParameterEquiv Q split c i a * synchronizedParameterEquiv Q split c i b := by
  obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective a
  obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective b
  cases i with
  | inl j =>
    have h : PositiveTables.rootChartEquiv m (.inl j) a *
        PositiveTables.rootChartEquiv m (.inl j) b =
        PositiveTables.rootChartEquiv m (.inl j) (a+b) := by
      apply Subtype.ext
      exact congrArg (fun z : Parabolics.unipotent m => (z : Model m))
        (PositiveTables.pair_mul j a b)
    rw [h, synchronizedParameterEquiv_field, synchronizedParameterEquiv_field,
      synchronizedParameterEquiv_field]
    exact Subtype.ext (synchronizedPositivePoint_pair_mul Q split c j a b).symm
  | inr j =>
    have h : PositiveTables.rootChartEquiv m (.inr j) a *
        PositiveTables.rootChartEquiv m (.inr j) b =
        PositiveTables.rootChartEquiv m (.inr j) (a.1+b.1,a.2+b.2+titsEnd m a.1*b.1) := by
      apply Subtype.ext
      exact congrArg (fun z : Parabolics.unipotent m => (z : Model m))
        (PositiveTables.quartet_mul j a.1 a.2 b.1 b.2)
    rw [h, synchronizedParameterEquiv_field, synchronizedParameterEquiv_field,
      synchronizedParameterEquiv_field]
    exact Subtype.ext (synchronizedPositivePoint_quartet_mul Q split c j a.1 a.2 b.1 b.2).symm

/-- Literal whole-root homomorphisms, using only the established root laws. -/
def synchronizedSourceRoot (i : PositiveTables.Root) :
    AngularPresentation.Parameter m i →* X ⧸ Q.D :=
  (positiveRoot Q split i).subtype.comp
    (MulEquiv.toMonoidHom
      { toEquiv := synchronizedParameterEquiv Q split c i
        map_mul' := synchronizedParameterEquiv_mul Q split c i })

@[simp] theorem synchronizedSourceRoot_field (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) :
    synchronizedSourceRoot Q split c i (PositiveTables.rootChartEquiv m i a) =
      synchronizedPositivePoint Q split c i a :=
  congrArg Subtype.val (synchronizedParameterEquiv_field Q split c i a)

open Theory.GroupTheory.OrderedRootPresentation

variable (E : OrderedRootPresentation.Equations (AngularPresentation.table m)
  (synchronizedSourceRoot Q split c))

/-- Angular equations construct this homomorphism; no global comparison is an input. -/
def synchronizedPositiveEval : Parabolics.unipotent m →* X ⧸ Q.D :=
  (OrderedRootPresentation.eval (AngularPresentation.table m) E).comp
    (AngularPresentation.nativeEquiv m).symm.toMonoidHom

@[simp] theorem synchronizedPositiveEval_field (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) :
    synchronizedPositiveEval Q split c E (PositiveTables.root m i a) =
      synchronizedPositivePoint Q split c i a := by
  have h : AngularPresentation.nativeEquiv m
      (OrderedRootPresentation.root (AngularPresentation.table m) i
        (PositiveTables.rootChartEquiv m i a)) = PositiveTables.root m i a := by
    apply Subtype.ext
    exact AngularPresentation.nativeEquiv_root m i (PositiveTables.rootChartEquiv m i a)
  rw [←h]
  change OrderedRootPresentation.eval (AngularPresentation.table m) E
    ((AngularPresentation.nativeEquiv m).symm ((AngularPresentation.nativeEquiv m) _)) = _
  rw [MulEquiv.symm_apply_apply,OrderedRootPresentation.eval_root,synchronizedSourceRoot_field]

include E in
/-- The angular equations imply every native pair-collection equation. -/
theorem synchronizedPositiveEquations :
    PositivePresentation.Equations (synchronizedPositivePoint Q split c) where
  pair_zero := synchronizedPositivePoint_pair_zero Q split c
  quartet_zero := synchronizedPositivePoint_quartet_zero Q split c
  exchange i j a b := by
    have h := congrArg (synchronizedPositiveEval Q split c E)
      (PositiveTables.exchange_equation i j a b)
    rw [map_mul,synchronizedPositiveEval_field,synchronizedPositiveEval_field] at h
    refine h.trans ?_
    change synchronizedPositiveEval Q split c E
      (PositivePresentation.word (PositiveTables.root m) _) = _
    rw [PositivePresentation.map_word]
    simp only [synchronizedPositiveEval_field]

/-- The actual SourcePositive consumer, with no separate exchange hypothesis. -/
def synchronizedPositiveCharts : SourcePositive.Charts Q split m where
  orientation := false
  rotation_eight := c.rotation_eight
  index := positiveIndex
  root := positiveRoot Q split
  order_eq := positiveRoot_ordered Q split c.rotation_eight
  chart := synchronizedPositiveChart Q split c
  equations := synchronizedPositiveEquations Q split c E

/-- The constructed chart bundle satisfies exactly the original angular interface. -/
theorem synchronizedPositiveCharts_angular :
    SourceAngular.Equations Q split (synchronizedPositiveCharts Q split c E) := by
  have h : SourceAngular.sourceRoot Q split (synchronizedPositiveCharts Q split c E) =
      synchronizedSourceRoot Q split c := by
    funext i
    apply MonoidHom.ext
    intro a
    obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective a
    rw [SourceAngular.sourceRoot_field,synchronizedSourceRoot_field]
    rfl
  change OrderedRootPresentation.Equations (AngularPresentation.table m)
    (SourceAngular.sourceRoot Q split (synchronizedPositiveCharts Q split c E))
  rw [h]
  exact E
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
