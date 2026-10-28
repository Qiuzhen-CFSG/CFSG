module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAdjacent
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiCommute

/-!
# Perpendicular Suzuki equations in the marked source quotient

Relation (10.2)(iv) centralizes the first and fifth whole Suzuki roots.
The actual linear reflection gives the third and seventh pair. Native
coordinate uniqueness converts both to the literal angular table, including
all central parameters in the binary case.

Source: Fong--Seitz II (1974), (10.2)(iv), pp.221--224.
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

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh



/-- Both perpendicular Suzuki pairs commute with their synchronized labels. -/
theorem synchronized_suzuki_commute_family (a b u v : CoefficientField m) :
    Commute (S 0 a b) (S 1 u v) ∧ Commute (S 3 a b) (S 2 u v) := by
  have hc (a b u v : CoefficientField m) : Commute (S 0 a b) (S 1 u v) := by
    have h : ⁅positiveRoot Q split (.inr 0), positiveRoot Q split (.inr 1)⁆ = ⊥ := by
      change ⁅rootAt Q split 1 1,
        rootAt Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0)⁆ = ⊥
      rw [rootAt_one]
      simpa only [nConj,U,Uat,OneMemClass.coe_one,rightConjugate_one]
        using c.relations.ten_two_iv_right 1
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h
      (synchronizedPositiveChart Q split c (.inr 0) (a,b)).property) _
      (synchronizedPositiveChart Q split c (.inr 1) (u,v)).property).symm
  refine ⟨hc a b u v, ?_⟩
  have hh := congrArg (MulAut.conj (W false)) (hc u v a b).eq
  change _ * _ = _ * _
  simpa only [map_mul,batch_quartet_reflection Q split c false 0 (by decide),
    batch_quartet_reflection Q split c false 1 (by decide),next,Matrix.cons_val,
    Fin.isValue,Matrix.head_cons] using hh.symm

open Theory.GroupTheory.OrderedRootPresentation ReeF4.CentralCovers.TwoPrimary

/-- The two perpendicular whole Suzuki-root pairs in angular order. -/
def SuzukiCommuteAngularPair (i j : PositiveTables.Root) : Prop :=
  (i = .inr 0 ∧ j = .inr 1) ∨ (i = .inr 3 ∧ j = .inr 2)
instance (i j : PositiveTables.Root) : Decidable (SuzukiCommuteAngularPair i j) :=
  inferInstanceAs (Decidable ((i = .inr 0 ∧ j = .inr 1) ∨ (i = .inr 3 ∧ j = .inr 2)))

/-- Exact literal angular equations for both perpendicular Suzuki pairs. -/
theorem synchronized_suzukiCommuteAngular_equation (i j : PositiveTables.Root)
    (h : SuzukiCommuteAngularPair i j) (hj : j ∈ tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj u v) := by
  obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective u
  obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m j).surjective v
  apply AngularAdjacent.equation_of_commute
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (AngularSuzukiCommute.suzuki_commute_family m a.1 a.2 b.1 b.2).1
    · exact (AngularSuzukiCommute.suzuki_commute_family m a.1 a.2 b.1 b.2).2
  · rw [synchronizedSourceRoot_field Q split c i a,
      synchronizedSourceRoot_field Q split c j b]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (synchronized_suzuki_commute_family Q split c a.1 a.2 b.1 b.2).1
    · exact (synchronized_suzuki_commute_family Q split c a.1 a.2 b.1 b.2).2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
