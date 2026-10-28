module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.SquareExports

/-!+# Source polygon parameters and hexagon recognition

The Feit--Higman constraints are applied to the literal finite marked
quotient. They remove the square premise from the exhaustive hexagon
recognition theorem, retaining its whole original Borel and both endpoint
inclusion squares. The two polygon constraints also hold for the actual
original parabolic/common-Borel indices.

Source: Fong--Seitz I (1J), Feit--Higman (1964), Theorems 1--2;
DGS, Groups and Graphs, Part II Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual polygon metric discharges the source square premise for
either original factor of a marked hexagon. -/
theorem marked_hexagon_linear_factor_of_rotation_six
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) (i j : Fin 2) (hij : i≠j) :
    ∃ n : ℕ, 0<n ∧ ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) :=
  marked_hexagon_linear_factor Q mark h split hm i j hij
    (hexagon_root_product_isSquare_of_ne Q split hm i j hij)

/-- Exhaustive marked G₂/triality recognition with the square premise
proved from the actual finite coset graph. -/
theorem marked_hexagon_catalogue_of_rotation_six
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_hexagon_catalogue Q mark h split hm
    (hexagon_root_product_isSquare Q split hm)

/-- The original source quotient needs only its split structure and
rotation-six geometry for the full marked hexagon comparison. -/
theorem quotient_hexagon_catalogue_of_rotation_six
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_hexagon_catalogue_of_rotation_six Q (originalMarkedIso Q) h split hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Fong--Seitz I (1J) for the two original endpoint indices in a hexagon. -/
theorem original_hexagon_commonBorel_product_isSquare
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) (i j : Fin 2) (hij : i≠j) :
    IsSquare ((((commonBorel L S).subgroupOf (parabolic L S i)).index-1)*
      (((commonBorel L S).subgroupOf (parabolic L S j)).index-1)) := by
  rw [original_commonBorel_root_index h Q split i,
    original_commonBorel_root_index h Q split j]
  simpa only [Nat.add_sub_cancel_left] using
    hexagon_root_product_isSquare_of_ne Q split hm i j hij

/-- Fong--Seitz I (1J) for the same original endpoint indices in an octagon. -/
theorem original_octagon_twice_commonBorel_product_isSquare
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i≠j) :
    IsSquare (2*(((commonBorel L S).subgroupOf (parabolic L S i)).index-1)*
      (((commonBorel L S).subgroupOf (parabolic L S j)).index-1)) := by
  rw [original_commonBorel_root_index h Q split i,
    original_commonBorel_root_index h Q split j]
  simpa only [Nat.add_sub_cancel_left] using
    octagon_twice_root_product_isSquare_of_ne Q split hm i j hij

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
