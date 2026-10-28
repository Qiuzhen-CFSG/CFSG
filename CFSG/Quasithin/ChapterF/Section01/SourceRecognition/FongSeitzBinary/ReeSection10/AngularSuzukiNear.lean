module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAdjacent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCoefficients
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiNear

/-!
# Three nearby whole-Suzuki angular equations

The literal synchronized (10.8) fixes the first pair for all four parameters.
The supplied reflections give the other two pairs, and native uniqueness
identifies the precise chosen angular tuples, also at q=2.

Source: Fong--Seitz II (1974), (10.8), and its Weyl transforms.
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

private theorem linear_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]

private theorem conjugate_of_right {G : Type*} [Group G] {x y z : G}
    (h : x⁻¹*y⁻¹*x*y = z) (hx : Commute x z) (hy : Commute y z) :
    x*y*x⁻¹ = z*y := by
  have hs : x*y = y*x*z := by
    rw [←h]; group
  calc
    _ = (y*x*z)*x⁻¹ := by rw [hs]
    _ = (y*z*x)*x⁻¹ := by rw [mul_assoc y x z,hx.eq,←mul_assoc]
    _ = y*z := by group
    _ = z*y := hy.eq

/-- Literal full-root conjugation from (10.8), including both central labels. -/
theorem synchronized_nearSuzuki_conjugate (a b y z : CoefficientField m) :
    S 0 a b * S 3 y z * (S 0 a b)⁻¹ = L 1 (a*y) * S 3 y z := by
  have h := synchronized_ten_eight Q split c a b y z
  rw [←batch_simple_suzuki] at h
  have hh : (S 0 a b)⁻¹*(S 3 y z)⁻¹*S 0 a b*S 3 y z = L 1 (a*y) := by
    have he := congrArg Inv.inv h
    simpa only [mul_inv_rev,inv_inv,linear_inv,mul_assoc] using he
  have h0 := (synchronized_adjacent_commute_family Q split c (a*y) a b).1.symm
  have h1 := (synchronized_adjacent_commute_family Q split c (a*y) y z).2.1.symm
  exact conjugate_of_right hh h0 h1

private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) (hz : z⁻¹ = z) : b*a*b⁻¹ = z*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = z⁻¹*a := by group
    _ = _ := by rw [hz]

/-- The terminal nearby Suzuki pair is the linear reflection of (0,2). -/
theorem synchronized_nearSuzuki_terminal_conjugate (a b y z : CoefficientField m) :
    S 1 a b * S 2 y z * (S 1 a b)⁻¹ = L 2 (a*y) * S 2 y z := by
  have h := congrArg (MulAut.conj (W false))
    (synchronized_nearSuzuki_conjugate Q split c y z a b)
  have hh : S 2 y z * S 1 a b * (S 2 y z)⁻¹ = L 2 (a*y) * S 1 a b := by
    simpa only [map_mul,map_inv,batch_quartet_reflection Q split c false 0 (by decide),
      batch_quartet_reflection Q split c false 3 (by decide),batch_pair_reflection Q split c false 1 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_comm y a] using h
  exact reverse_conjugate hh (linear_inv Q split c _ _)

/-- The middle nearby Suzuki pair retains the literal product coefficient. -/
theorem synchronized_nearSuzuki_middle_conjugate (a b y z : CoefficientField m) :
    S 3 a b * S 1 y z * (S 3 a b)⁻¹ = L 3 (a*y) * S 1 y z := by
  have h := congrArg (MulAut.conj (W true))
    (synchronized_nearSuzuki_terminal_conjugate Q split c y z a b)
  have hh : S 1 y z * S 3 a b * (S 1 y z)⁻¹ = L 3 (a*y) * S 3 a b := by
    simpa only [map_mul,map_inv,batch_quartet_reflection Q split c true 1 (by decide),
      batch_quartet_reflection Q split c true 2 (by decide),batch_pair_reflection Q split c true 2 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_comm y a] using h
  exact reverse_conjugate hh (linear_inv Q split c _ _)


open Theory.GroupTheory.OrderedRootPresentation ReeF4.CentralCovers.TwoPrimary

/-- The three nearby Suzuki pairs in angular order. -/
def NearSuzukiAngularPair (i j : PositiveTables.Root) : Prop :=
  (i = .inr 0 ∧ j = .inr 3) ∨ (i = .inr 3 ∧ j = .inr 1) ∨
    (i = .inr 1 ∧ j = .inr 2)
instance (i j : PositiveTables.Root) : Decidable (NearSuzukiAngularPair i j) :=
  inferInstanceAs (Decidable ((i = .inr 0 ∧ j = .inr 3) ∨ (i = .inr 3 ∧ j = .inr 1) ∨
    (i = .inr 1 ∧ j = .inr 2)))

/-- All three nearby Suzuki pairs satisfy the exact native angular table. -/
theorem synchronized_nearSuzukiAngular_equation (i j : PositiveTables.Root)
    (h : NearSuzukiAngularPair i j) (hj : j ∈ tail sourceOrder i)
    (u : AngularPresentation.Parameter m i) (v : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i u * synchronizedSourceRoot Q split c j v *
      (synchronizedSourceRoot Q split c i u)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj u v) := by
  obtain ⟨a,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective u
  obtain ⟨b,rfl⟩ := (PositiveTables.rootChartEquiv m j).surjective v
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [AngularSuzukiNear.table02,AngularSuzukiNear.tail02_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) a,
      synchronizedSourceRoot_field Q split c (.inr 3) b,
      synchronizedSourceRoot_field Q split c (.inl 1) (a.1*b.1)]
    exact synchronized_nearSuzuki_conjugate Q split c a.1 a.2 b.1 b.2
  · rw [AngularSuzukiNear.table24,AngularSuzukiNear.tail24_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 3) a,
      synchronizedSourceRoot_field Q split c (.inr 1) b,
      synchronizedSourceRoot_field Q split c (.inl 3) (a.1*b.1)]
    exact synchronized_nearSuzuki_middle_conjugate Q split c a.1 a.2 b.1 b.2
  · rw [AngularSuzukiNear.table46,AngularSuzukiNear.tail46_word]
    rw [synchronizedSourceRoot_field Q split c (.inr 1) a,
      synchronizedSourceRoot_field Q split c (.inr 2) b,
      synchronizedSourceRoot_field Q split c (.inl 2) (a.1*b.1)]
    exact synchronized_nearSuzuki_terminal_conjugate Q split c a.1 a.2 b.1 b.2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
