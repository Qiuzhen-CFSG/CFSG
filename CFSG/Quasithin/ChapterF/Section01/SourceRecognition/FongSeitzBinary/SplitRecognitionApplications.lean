module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original split quadrangle and hexagon comparisons in Chapter 12

The completed quadrangle catalogue applies to the literal original quotient
and to the selected Chapter 12 linear factor. For rotation six, the finite
polygon square theorem supplies the exhaustive hexagon consumer. Both routes
retain the supplied original amalgam marking and the full KnownSimple/proper-K
preparation. The rotation-four-or-six premise is not an exhaustive Weyl-order
selection theorem.

Source: Aschbacher--Smith 12.2.2 and F.1.12; DGS Theorem D, p.224;
Fong--Seitz I (6A), II (8C); Feit--Higman (1964), Theorems 1--2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleRecognition
open Chapter6.Source.RankOneGeneric

/-- Apply the catalogue on the literal original quotient, with its canonical
marking rather than a newly chosen endpoint isomorphism. -/
theorem quotient_quadrangle_catalogue_of_linear_left
    {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hqt : IsQuasithin G) (hm : rotationOrder Q = 4)
    (μ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,K)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam L S) :=
  marked_quadrangle_catalogue_of_linear_left Q (originalMarkedIso Q) h split hqt hm μ

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleRecognition

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 preparation supplies the quadrangle comparison
without an opposite-factor, perfectness, profile or equation premise. -/
theorem rankOne_quadrangle_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hf := d.hypothesisF11 hi hTH
  obtain ⟨K,hK,hfin,hcard,⟨μ⟩⟩ := hpsl
  let := Fintype.ofFinite K
  let : NeZero n := ⟨by omega⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact QuadrangleRecognition.marked_quadrangle_catalogue_of_linear_left
    Q mark hf split hi.qtke.quasithin hm μ

/-- The original selected pair is recognized on either rotation-four or
rotation-six geometry. The geometric disjunction remains an explicit input. -/
theorem rankOne_quadrangle_or_hexagon_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4 ∨ rotationOrder Q = 6) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  rcases hm with hfour | hsix
  · exact D.rankOne_quadrangle_comparison h hmany hn hpsl d hTH Q mark split hfour
  · exact HexagonRecognition.marked_hexagon_catalogue_of_rotation_six Q mark
      (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH) split hsix

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
