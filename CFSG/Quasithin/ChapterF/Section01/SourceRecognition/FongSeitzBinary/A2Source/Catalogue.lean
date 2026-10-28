module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalA2MarkedRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The marked source A₂ comparison in the concrete catalogue

The accepted source recognition supplies a full flag-amalgam isomorphism,
with a point index recording its orientation. The two possible indices give
the ordinary or reversed LinearThree model. The finite characteristic-two
field itself supplies the positive exponent; in particular q=2 and q=4
are retained. No perfect-factor premise or root-data input is added.

The last theorem applies this construction to the literal Chapter 12
preparation. Its two original endpoint maps and whole-overlap map are those
of MarkedRecognition, which proves both inclusion squares. The independent
natural actions, Borel normalization, centerfreeness and rotation order
remain explicit source inputs; this selected A₂ branch does not assert
exhaustive row selection.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224;
Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Configuration
open Matrix.PSL3.RootPresentationRecognition
open Theory.AlgebraicGroup.TitsSystem.SourceBinary

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

/-- Both orientations of the full PSL₃ flag comparison give the actual
linear catalogue row, with the field parameter derived internally. -/
theorem ConcreteAmalgamComparison.of_a2_flag
    {A B C : Type*} [Group A] [Group B] [Group C]
    {α : RankTwoAmalgam A B C} {F : Type} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (e : RankTwoAmalgam.Iso α (flagAmalgam F i)) :
    ConcreteAmalgamComparison α := by
  let := Fintype.ofFinite F
  obtain ⟨m, _, hm⟩ := FiniteField.card F 2
  apply ConcreteAmalgamComparison.linear F m m.property
    (by simpa only [Nat.card_eq_fintype_card] using hm)
  fin_cases i
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedRecognition
open Chapter6.Source.RankOneGeneric
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)
variable {k₀ W₀ W₁ : Type*} {k₁ : Type}
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

include mark h in
/-- Source natural actions and the independently marked triangular quotient
produce the ordinary concrete linear row in either actual orientation. -/
theorem concreteComparison
    (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
      (base (fullFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
      (base (fullFamily L S) false) k₁ W₁)
    (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set _))
    (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set _))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hm : RootCoordinates.rotationOrder d = 3) (hc : centerIn c₁.actor = ⊥)
    (split : SplitData d.tits) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam L S) :=
  Global.ConcreteAmalgamComparison.of_a2_flag _
    (comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc split)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedRecognition

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable {k₀ W₀ W₁ : Type*} {k₁ : Type}
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

include D in
/-- The selected Chapter 12 pair obtains its actual linear catalogue
comparison from the accepted full marked source recognition. -/
theorem rankOne_a2_marked_concrete_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (prep : Global.Preparation T L H A B R)
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic ![L,R] (Global.sourceS L H) 0)
        (parabolic ![L,R] (Global.sourceS L H) 0 ⊓ parabolic ![L,R] (Global.sourceS L H) 1)
        (parabolic ![L,R] (Global.sourceS L H) 1) inf_le_left inf_le_right) d.standardAmalgam)
    (split : SplitData d.tits)
    (c₀ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true) k₀ W₀)
    (c₁ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false) k₁ W₁)
    (hn₀ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₀.actor : Set _))
    (hn₁ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₁.actor : Set _))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hm : RootCoordinates.rotationOrder d = 3) (hc : centerIn c₁.actor = ⊥) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨i, _, cmp, _⟩ := D.rankOne_a2_marked_source_recognition
    h hmany hn hpsl hH prep d mark split c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc
  exact Global.ConcreteAmalgamComparison.of_a2_flag i cmp

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
