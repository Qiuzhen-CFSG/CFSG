module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularNextTransforms

/-!
# The remaining two next-linear ordered source equations

The supplied root reflections preserve both synchronized Suzuki coordinates.
Transporting and reversing the checked next-linear equation therefore proves
angular positions (1,6) and (2,7), with no additional source hypotheses.
The independently verified native coefficient vectors identify the literal
ordered table entries, retaining both binary central corrections.

The consumer discharges these two cases in `RemainingAngularEquations`.
Together with the preceding five cases this leaves 21 pairs, seven of which
are adjacent and belong to the separate adjacent-equation owner.

Source: Fong--Seitz II (1974), Section 10, (10.13)(i), (10.15), pp.224--226.
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

private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,synchronizedPositivePoint_quartet_zero]

/-- Angular positions 1 and 6: reflection and reversal put all three correction
factors in angular order, including both binary central coefficients. -/
theorem synchronized_next_reflected_conjugate (a b y : CoefficientField m) :
    L 1 y * S 2 a b * (L 1 y)⁻¹ =
      S 3 0 (a*titsEnd m y) * L 3 (titsEnd m a*y) *
        S 1 0 ((b+titsEnd m a*a)*y) * S 2 a b := by
  have h := congrArg (MulAut.conj (W false)) (synchronized_next_conjugate Q split c a b y)
  have hh : S 2 a b * L 1 y * (S 2 a b)⁻¹ =
      (S 1 0 ((b+titsEnd m a*a)*y) * L 3 (titsEnd m a*y) *
        S 3 0 (a*titsEnd m y)) * L 1 y := by
    simpa only [map_mul,map_inv,batch_quartet_reflection Q split c false 0 (by decide),batch_quartet_reflection Q split c false 3 (by decide),
      batch_quartet_reflection Q split c false 1 (by decide),batch_pair_reflection Q split c false 2 (by decide),batch_pair_reflection Q split c false 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [mul_inv_rev,omega_inv,pair_inv,mul_assoc] using reverse_conjugate hh

/-- Angular positions 2 and 7: a second reflection and reversal retain the
same parameters and place the two Omega corrections on opposite sides. -/
theorem synchronized_next_shifted_conjugate (a b y : CoefficientField m) :
    S 3 a b * L 0 y * (S 3 a b)⁻¹ =
      S 1 0 ((b+titsEnd m a*a)*y) * L 2 (titsEnd m a*y) *
        S 2 0 (a*titsEnd m y) * L 0 y := by
  have h := congrArg (MulAut.conj (W true)) (synchronized_next_reflected_conjugate Q split c a b y)
  have hh : L 0 y * S 3 a b * (L 0 y)⁻¹ =
      (S 2 0 (a*titsEnd m y) * L 2 (titsEnd m a*y) *
        S 1 0 ((b+titsEnd m a*a)*y)) * S 3 a b := by
    simpa only [map_mul,map_inv,batch_quartet_reflection Q split c true 2 (by decide),batch_quartet_reflection Q split c true 3 (by decide),
      batch_quartet_reflection Q split c true 1 (by decide),batch_pair_reflection Q split c true 1 (by decide),batch_pair_reflection Q split c true 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [mul_inv_rev,omega_inv,pair_inv,mul_assoc] using reverse_conjugate hh

open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary

/-- The two remaining members of the next-linear reflection family. -/
def NextAngularPair (i j : PositiveTables.Root) : Prop :=
  (i = .inl 1 ∧ j = .inr 2) ∨ (i = .inr 3 ∧ j = .inl 0)

instance (i j : PositiveTables.Root) : Decidable (NextAngularPair i j) :=
  by unfold NextAngularPair; infer_instance

/-- The literal ordered equations on the two transformed next-linear pairs,
for arbitrary whole-root parameters and every field, including q = 2. -/
theorem synchronized_nextAngular_equation (i j : PositiveTables.Root)
    (h : NextAngularPair i j) (hj : j ∈ tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj u v) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 1)).surjective u
    obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 2)).surjective v
    rw [AngularNextTransforms.table16,AngularNextTransforms.tail16_word]
    rw [synchronizedSourceRoot_field Q split c (.inl 1) y,
      synchronizedSourceRoot_field Q split c (.inr 2) (a,b),
      synchronizedSourceRoot_field Q split c (.inr 3) (0,a*titsEnd m y),
      synchronizedSourceRoot_field Q split c (.inl 3) (titsEnd m a*y),
      synchronizedSourceRoot_field Q split c (.inr 1) (0,(b+titsEnd m a*a)*y)]
    exact synchronized_next_reflected_conjugate Q split c a b y
  · obtain ⟨⟨a,b⟩,rfl⟩ := (PositiveTables.rootChartEquiv m (.inr 3)).surjective u
    obtain ⟨y,rfl⟩ := (PositiveTables.rootChartEquiv m (.inl 0)).surjective v
    rw [AngularNextTransforms.table27,AngularNextTransforms.tail27_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 3) (a,b),
      synchronizedSourceRoot_field Q split c (.inl 0) y,
      synchronizedSourceRoot_field Q split c (.inr 1) (0,(b+titsEnd m a*a)*y),
      synchronizedSourceRoot_field Q split c (.inl 2) (titsEnd m a*y),
      synchronizedSourceRoot_field Q split c (.inr 2) (0,a*titsEnd m y)]
    exact synchronized_next_shifted_conjugate Q split c a b y

/-- Remaining cases after the original five and the two next-linear transforms.
Independent adjacent-root work can discharge seven of these 21 cases. -/
def RemainingAfterNextEquations : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Apply the new literal equations at the existing construction boundary. -/
theorem remainingAngularEquations_of_next
    (h : RemainingAfterNextEquations Q split c) : RemainingAngularEquations Q split c := by
  intro i j hij hj a b
  by_cases hn : NextAngularPair i j
  · exact synchronized_nextAngular_equation Q split c i j hn hj a b
  · exact h i j hij hn hj a b

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
