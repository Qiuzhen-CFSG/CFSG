module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularLinearCommute
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCommuteFamily
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations

/-!
# Five source linear angular commutations

The elementary Frattini subgroup contains both middle linear roots. The
perpendicular pair centralizes by (10.2)(iv), and Weyl transport supplies the
other three pairs. Native coordinate uniqueness turns these into five literal
whole-root angular equations, including the binary field.

Source: Fong--Seitz II, Section 10, (10.2)(iv), (10.3), pp.221--224.
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
open ReeF4.CentralCovers.TwoPrimary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

private theorem linear_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem reflect_linear_commute (s : Bool) (i j : Fin 4)
    (hi : (step false s (true,i)).1 = true)
    (hj : (step false s (true,j)).1 = true)
    (a b : CoefficientField m) (h : Commute (L i a) (L j b)) :
    Commute (L (next false s i) a) (L (next false s j) b) := by
  have hh := h.map (MulAut.conj (W s)).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom,linear_pair_reflection Q split c s i hi,
    linear_pair_reflection Q split c s j hj] using hh

private theorem source_linear3_linear2 (a b : CoefficientField m) :
    Commute (L 3 a) (L 2 b) := by
  let d := pinnedInput Q split c
  let : IsElementaryAbelian 2 (phiCenterSection Q split d).numerator :=
    phiRemainder_elementary Q split d
  let x : (phiCenterSection Q split d).numerator :=
    inclusion (perpendicularLinear_le_phi Q split d) (synchronizedPositiveChart Q split c (.inl 3) a)
  let y : (phiCenterSection Q split d).numerator :=
    inclusion (nextLinear_le_phi Q split d) (synchronizedPositiveChart Q split c (.inl 2) b)
  exact (show Commute x y from Commute.all x y).map
    (phiCenterSection Q split d).numerator.subtype

private theorem source_linear0_linear3 (a b : CoefficientField m) :
    Commute (L 0 a) (L 3 b) := by
  have h0 : L 0 a ∈ simpleRoot Q split 0 := by
    rw [synchronizedPositivePoint_pair_word]
    simpa only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one] using
      (synchronizedLinearChart Q split c (.ofAdd a)).property
  exact (mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularLinear Q split c
      ((show simpleRoot Q split 0 ≤ rankOne Q split 0 from le_sup_left) h0))
      _ (synchronizedPositiveChart Q split c (.inl 3) b).property).symm

/-- The five commuting linear pairs in the actual marked source quotient. -/
theorem synchronized_linear_commute_family (a b : CoefficientField m) :
    Commute (L 1 a) (L 3 b) ∧
    Commute (L 1 a) (L 2 b) ∧
    Commute (L 3 a) (L 2 b) ∧
    Commute (L 3 a) (L 0 b) ∧
    Commute (L 2 a) (L 0 b) := by
  have h13 (x y : CoefficientField m) : Commute (L 1 x) (L 3 y) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_linear_commute Q split c false 2 3 (by decide) (by decide) x y
        (source_linear3_linear2 Q split c y x).symm
  have h12 : Commute (L 1 a) (L 2 b) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_linear_commute Q split c true 0 3 (by decide) (by decide) a b
        (source_linear0_linear3 Q split c a b)
  have h20 : Commute (L 2 a) (L 0 b) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_linear_commute Q split c true 3 1 (by decide) (by decide) a b (h13 b a).symm
  exact ⟨h13 a b,h12,source_linear3_linear2 Q split c a b,
    (source_linear0_linear3 Q split c b a).symm,h20⟩

/-- The five linear pairs, expressed in the literal positive-root labels. -/
def LinearCommutingAngularPair (i j : PositiveTables.Root) : Prop :=
    (i = .inl 1 ∧ j = .inl 3) ∨ (i = .inl 1 ∧ j = .inl 2) ∨
    (i = .inl 3 ∧ j = .inl 2) ∨ (i = .inl 3 ∧ j = .inl 0) ∨
    (i = .inl 2 ∧ j = .inl 0)
instance (i j : PositiveTables.Root) : Decidable (LinearCommutingAngularPair i j) :=
  by unfold LinearCommutingAngularPair; infer_instance

/-- Discharge these five cases of the literal native angular table. -/
theorem synchronized_linearAngular_equation (i j : PositiveTables.Root)
    (h : LinearCommutingAngularPair i j)
    (hj : j ∈ Theory.GroupTheory.OrderedRootPresentation.tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      Theory.GroupTheory.OrderedRootPresentation.word (AngularPresentation.Parameter m)
        (fun k => synchronizedSourceRoot Q split c k)
        (Theory.GroupTheory.OrderedRootPresentation.tail sourceOrder i)
        ((AngularPresentation.table m).conjugate i j hj u v) := by
  apply AngularAdjacent.equation_of_commute m (synchronizedSourceRoot Q split c) i j hj u v
  · obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective u
    obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m j).surjective v
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (AngularLinearCommute.linear_commute_family m a b).1
    · exact (AngularLinearCommute.linear_commute_family m a b).2.1
    · exact (AngularLinearCommute.linear_commute_family m a b).2.2.1
    · exact (AngularLinearCommute.linear_commute_family m a b).2.2.2.1
    · exact (AngularLinearCommute.linear_commute_family m a b).2.2.2.2
  · obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective u
    obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m j).surjective v
    rw [synchronizedSourceRoot_field Q split c i a,synchronizedSourceRoot_field Q split c j b]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (synchronized_linear_commute_family Q split c a b).1
    · exact (synchronized_linear_commute_family Q split c a b).2.1
    · exact (synchronized_linear_commute_family Q split c a b).2.2.1
    · exact (synchronized_linear_commute_family Q split c a b).2.2.2.1
    · exact (synchronized_linear_commute_family Q split c a b).2.2.2.2
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
