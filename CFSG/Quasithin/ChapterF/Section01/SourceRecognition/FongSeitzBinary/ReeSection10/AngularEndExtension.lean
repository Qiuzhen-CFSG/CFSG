module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuffixSource
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiLast

/-!
# Extending the two pure end commutators to whole angular equations

The seven-root realization transfers each native pure right-commutator into
the source quotient. Main curves generate the entire relative root groups.
Equality of suffix homomorphisms first extends each inverse-main actor over
the whole suffix; the subgroup of intertwining actors then extends to the
entire first root. Thus the two literal pure source equations close both
remaining angular rows, including all central Suzuki parameters and field two.

Source: Fong--Seitz II, Section 10, (10.23)--(10.41).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)

/-- The literal opposite main-curve source equation, including its inverse cocycle. -/
def SuzukiOppositePureEquation : Prop := ∀ a y : CoefficientField m,
  (S 2 y 0)⁻¹ * (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
    S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) *
      L 3 ((a*titsEnd m a)*(y*titsEnd m y)) * S 3 (titsEnd m a*y) 0

/-- The pure opposite source identity intertwines inverse-main actors on the main curve. -/
theorem angularSuffixEval_oppositeMain_action
    (hpure : SuzukiOppositePureEquation Q split c)
    (a y : CoefficientField m) :
    angularSuffixEval Q split c
      (AngularSuffix.firstAction m (PositiveTables.rootChartEquiv m (.inr 0) (a,0))⁻¹
        (AngularSuffix.root m (.inr 2) (by apply (AngularSuffix.suffix_member _).mpr; decide)
          (PositiveTables.rootChartEquiv m (.inr 2) (y,0)))) =
      (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 := by
  let f := angularSuffixEval Q split c
  let A := PositiveTables.rootChartEquiv m (.inr 0) (a,0)
  let Y := AngularSuffix.root m (.inr 2) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 2) (y,0))
  let V := AngularSuffix.root m (.inr 1) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 1)
      (a*titsEnd m y,titsEnd m (a*titsEnd m y)*(a*titsEnd m y)))
  let W := AngularSuffix.root m (.inl 3) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inl 3) ((a*titsEnd m a)*(y*titsEnd m y)))
  let T := AngularSuffix.root m (.inr 3) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 3) (titsEnd m a*y,0))
  have hn : Y⁻¹ * AngularSuffix.firstAction m A⁻¹ Y = V * W * T := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,AngularSuffix.firstAction_val]
    change (PositiveTables.quartet m 2 y 0 : Model m)⁻¹ *
      ((PositiveTables.quartet m 0 a 0 : Model m)⁻¹ *
        (PositiveTables.quartet m 2 y 0 : Model m) *
          ((PositiveTables.quartet m 0 a 0 : Model m)⁻¹)⁻¹) =
        (PositiveTables.quartet m 1 (a*titsEnd m y)
          (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) : Model m) *
          (PositiveTables.pair m 3 ((a*titsEnd m a)*(y*titsEnd m y)) : Model m) *
          (PositiveTables.quartet m 3 (titsEnd m a*y) 0 : Model m)
    simpa only [inv_inv,mul_assoc] using AngularSuzukiOpposite.main_right_coordinates m a y
  have ht := congrArg f hn
  simp only [map_mul f, map_inv f] at ht
  have hY : f Y = S 2 y 0 := by
    dsimp [f,Y]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hV : f V = S 1 (a*titsEnd m y)
      (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) := by
    dsimp [f,V]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hW : f W = L 3 ((a*titsEnd m a)*(y*titsEnd m y)) := by
    dsimp [f,W]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hT : f T = S 3 (titsEnd m a*y) 0 := by
    dsimp [f,T]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  rw [hY,hV,hW,hT,← hpure a y] at ht
  have he := congrArg (fun z => S 2 y 0*z) ht
  simp only [← mul_assoc,mul_inv_cancel,one_mul] at he
  change f (AngularSuffix.firstAction m A⁻¹ Y) = _
  exact he
/-- The literal last main-curve source equation, in reverse angular order. -/
def SuzukiLastPureEquation : Prop := ∀ a y : CoefficientField m,
  (L 0 y)⁻¹ * (S 0 a 0)⁻¹ * L 0 y * S 0 a 0 =
    S 2 (a*y) (titsEnd m (a*y)*(a*y)) *
      L 2 ((a^2*titsEnd m a)*(y*titsEnd m y)) *
      S 1 0 ((a^3*(titsEnd m a)^2)*(y^2*titsEnd m y)) *
      L 3 ((a^2*(titsEnd m a)^2)*(y*titsEnd m y)) *
      S 3 ((a*titsEnd m a)*y) 0 * L 1 ((a^2*titsEnd m a)*y)

private theorem last_main_action
    (hpure : SuzukiLastPureEquation Q split c) (a y : CoefficientField m) :
    angularSuffixEval Q split c
      (AngularSuffix.firstAction m (PositiveTables.rootChartEquiv m (.inr 0) (a,0))⁻¹
        (AngularSuffix.root m (.inl 0) (by apply (AngularSuffix.suffix_member _).mpr; decide)
          (PositiveTables.rootChartEquiv m (.inl 0) y))) =
      (S 0 a 0)⁻¹ * L 0 y * S 0 a 0 := by
  let f := angularSuffixEval Q split c
  let A := PositiveTables.rootChartEquiv m (.inr 0) (a,0)
  let Y := AngularSuffix.root m (.inl 0) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inl 0) y)
  let V := AngularSuffix.root m (.inr 2) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 2) (a*y,titsEnd m (a*y)*(a*y)))
  let W := AngularSuffix.root m (.inl 2) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inl 2) ((a^2*titsEnd m a)*(y*titsEnd m y)))
  let Z := AngularSuffix.root m (.inr 1) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 1) (0,(a^3*(titsEnd m a)^2)*(y^2*titsEnd m y)))
  let U := AngularSuffix.root m (.inl 3) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inl 3) ((a^2*(titsEnd m a)^2)*(y*titsEnd m y)))
  let T := AngularSuffix.root m (.inr 3) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inr 3) ((a*titsEnd m a)*y,0))
  let B := AngularSuffix.root m (.inl 1) (by apply (AngularSuffix.suffix_member _).mpr; decide)
    (PositiveTables.rootChartEquiv m (.inl 1) ((a^2*titsEnd m a)*y))
  have hn : Y⁻¹ * AngularSuffix.firstAction m A⁻¹ Y = V * W * Z * U * T * B := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,AngularSuffix.firstAction_val]
    change (PositiveTables.pair m 0 y : Model m)⁻¹ *
      ((PositiveTables.quartet m 0 a 0 : Model m)⁻¹ *
        (PositiveTables.pair m 0 y : Model m) *
          ((PositiveTables.quartet m 0 a 0 : Model m)⁻¹)⁻¹) =
      (PositiveTables.quartet m 2 (a*y) (titsEnd m (a*y)*(a*y)) : Model m) *
        (PositiveTables.pair m 2 ((a^2*titsEnd m a)*(y*titsEnd m y)) : Model m) *
        (PositiveTables.quartet m 1 0 ((a^3*(titsEnd m a)^2)*(y^2*titsEnd m y)) : Model m) *
        (PositiveTables.pair m 3 ((a^2*(titsEnd m a)^2)*(y*titsEnd m y)) : Model m) *
        (PositiveTables.quartet m 3 ((a*titsEnd m a)*y) 0 : Model m) *
        (PositiveTables.pair m 1 ((a^2*titsEnd m a)*y) : Model m)
    simpa only [inv_inv,mul_assoc] using AngularSuzukiLast.main_right_coordinates m a y
  have ht := congrArg f hn
  simp only [map_mul f, map_inv f] at ht
  have hY : f Y = L 0 y := by
    dsimp [f,Y]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hV : f V = S 2 (a*y) (titsEnd m (a*y)*(a*y)) := by
    dsimp [f,V]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hW : f W = L 2 ((a^2*titsEnd m a)*(y*titsEnd m y)) := by
    dsimp [f,W]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hZ : f Z = S 1 0 ((a^3*(titsEnd m a)^2)*(y^2*titsEnd m y)) := by
    dsimp [f,Z]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hU : f U = L 3 ((a^2*(titsEnd m a)^2)*(y*titsEnd m y)) := by
    dsimp [f,U]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hT : f T = S 3 ((a*titsEnd m a)*y) 0 := by
    dsimp [f,T]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  have hB : f B = L 1 ((a^2*titsEnd m a)*y) := by
    dsimp [f,B]
    rw [angularSuffixEval_root,synchronizedSourceRoot_field]
  rw [hY,hV,hW,hZ,hU,hT,hB,← hpure a y] at ht
  have he := congrArg (fun z => L 0 y*z) ht
  simp only [← mul_assoc,mul_inv_cancel,one_mul] at he
  exact he

/-- The two pure source end identities determine the whole first-root action. -/
theorem angularSuffixEval_firstAction
    (hopp : SuzukiOppositePureEquation Q split c)
    (hlast : SuzukiLastPureEquation Q split c)
    (a : AngularPresentation.Parameter m (.inr 0)) (v : AngularSuffix.Carrier m) :
    angularSuffixEval Q split c (AngularSuffix.firstAction m a v) =
      synchronizedSourceRoot Q split c (.inr 0) a * angularSuffixEval Q split c v *
        (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ := by
  apply AngularSuffix.firstAction_intertwining m
    (synchronizedSourceRoot Q split c (.inr 0)) (angularSuffixEval Q split c) _ a v
  intro t i hi y
  by_cases he : i = .inr 2
  · subst i
    simp only [AngularSuffix.mainParameter,angularSuffixEval_root,
      map_inv (synchronizedSourceRoot Q split c (.inr 0)),inv_inv]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) (t,0),
      synchronizedSourceRoot_field Q split c (.inr 2) (y,0)]
    exact angularSuffixEval_oppositeMain_action Q split c hopp t y
  by_cases hl : i = .inl 0
  · subst i
    simp only [AngularSuffix.mainParameter,angularSuffixEval_root,
      map_inv (synchronizedSourceRoot Q split c (.inr 0)),inv_inv]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) (t,0),
      synchronizedSourceRoot_field Q split c (.inl 0) y]
    exact last_main_action Q split c hlast t y
  simpa only [angularSuffixEval_root] using
    angularSuffixEval_firstAction_root Q split c (AngularSuffix.mainParameter m (.inr 0) t)⁻¹
      i hi he hl (AngularSuffix.mainParameter m i y)

/-- The complete first angular row, for arbitrary whole-root parameters. -/
theorem synchronized_firstAngular_equation
    (hopp : SuzukiOppositePureEquation Q split c)
    (hlast : SuzukiLastPureEquation Q split c)
    (j : PositiveTables.Root) (hj : j ∈ tail sourceOrder (.inr 0))
    (a : AngularPresentation.Parameter m (.inr 0)) (b : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c (.inr 0) a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 0)) ((AngularPresentation.table m).conjugate (.inr 0) j hj a b) := by
  have hi : j ∈ AngularSuffix.suffixOrder := hj
  have hfa : AngularSuffix.firstAction m a (AngularSuffix.root m j hi b) =
      ⟨word (AngularPresentation.Parameter m) (fun k => AngularPresentation.nativeRoot m k)
          AngularSuffix.suffixOrder ((AngularPresentation.table m).conjugate (.inr 0) j hj a b),
        word_mem_join _ _ _ _⟩ := by
    apply Subtype.ext
    change (a : Model m) * (b : Model m) * (a : Model m)⁻¹ = _
    exact AngularPresentation.native_equations m (.inr 0) j hj a b
  have he := angularSuffixEval_firstAction Q split c hopp hlast a (AngularSuffix.root m j hi b)
  rw [hfa,angularSuffixEval_word,angularSuffixEval_root] at he
  exact he.symm

/-- The genuine pure-to-whole consumer closes both residual end rows together. -/
theorem synchronizedSuzukiEndEquations_of_pure
    (hopp : SuzukiOppositePureEquation Q split c)
    (hlast : SuzukiLastPureEquation Q split c) : RemainingSuzukiEndEquations Q split c := by
  intro i j he hj a b
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact synchronized_firstAngular_equation Q split c hopp hlast _ hj a b
  · exact synchronized_firstAngular_equation Q split c hopp hlast _ hj a b

/-- The exact pure source identities imply the entire native angular table. -/
theorem synchronizedAngularEquations_of_pureEnd
    (hopp : SuzukiOppositePureEquation Q split c)
    (hlast : SuzukiLastPureEquation Q split c) :
    Equations (AngularPresentation.table m) (synchronizedSourceRoot Q split c) := by
  intro i j hj a b
  by_cases he : SuzukiEndAngularPair i j
  · exact synchronizedSuzukiEndEquations_of_pure Q split c hopp hlast i j he hj a b
  · exact synchronizedAngularEquation_of_not_suzukiEnd Q split c i j he hj a b

/-- Final Section 10 construction consumes only the two pure end equations. -/
def Section10Construction.ofPureEndCommutators
    (hopp : SuzukiOppositePureEquation Q split c)
    (hlast : SuzukiLastPureEquation Q split c) : Section10Construction Q split n m :=
  Section10Construction.ofSuzukiEndAngular Q split c
    (synchronizedSuzukiEndEquations_of_pure Q split c hopp hlast)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
