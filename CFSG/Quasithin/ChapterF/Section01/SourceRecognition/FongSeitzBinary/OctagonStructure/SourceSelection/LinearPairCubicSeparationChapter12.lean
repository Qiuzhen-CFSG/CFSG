module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicChapter12
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicSeparation

/-!
# Chapter 12 cubic Cartan separation for the selected two-linear row

The selected two-linear source branch already constructs the cubic Cartan
element, its fixed-root kernel separation and the exact radical orders.  This
leaf adds the next (6G) interface on the same quotient: the fixed radical is
the join of the three fixed roots in the odd family.  Both orientations,
whole-Borel markings and the original endpoint maps remain those supplied by
the panel-data consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)

include D h hmany hn hpsl d hTH e split hm in
/-- The cubic Cartan fixed radical is the literal three-root join in the
selected two-linear Chapter 12 branch.  The `rootAt` intersection clauses
are the actual opposite-root kernel separation, not a row-selection tag. -/
theorem rankOne_octagon_selected_linear_cubic_separation
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      Odd n ∧ Even b ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        (∀ w : Weyl Q,
          (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split 0 w : Set (X ⧸ Q.D)) ∧
          rootAt Q split 1 w ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
        rootAt Q split 0 (Q.simple 1) ⊔
            rootAt Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1) ⊔
            rootAt Q split 0 (Q.simple 1 * Q.simple 0) =
          simpleRemainder Q split 0 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ∧
        Nat.card (simpleRemainder Q split 0 ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^n)^3) ∨
    (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      Odd b ∧ Even n ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        (∀ w : Weyl Q,
          (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split 1 w : Set (X ⧸ Q.D)) ∧
          rootAt Q split 0 w ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
        rootAt Q split 1 (Q.simple 0) ⊔
            rootAt Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0) ⊔
            rootAt Q split 1 (Q.simple 0 * Q.simple 1) =
          simpleRemainder Q split 1 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ∧
        Nat.card (simpleRemainder Q split 1 ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^b)^3) := by
  obtain ⟨b, hb, hR, hratio, hdata⟩ :=
    rankOne_octagon_selected_linear_cubic_centralizers D h hmany hn hpsl d hTH Q e split hm
      hbranch
  rcases hdata with ⟨hnodd, hbeven, c, hc, hroots, hcard, _, _⟩ |
      ⟨hieven, hbodd, c, hc, hroots, hcard, _, _⟩
  · exact Or.inl ⟨b, hb, hR, hnodd, hbeven,
      c, hc, hroots,
      separated_radical_centralizer_sup Q split hm 0 1 (by decide) c hroots,
      hcard⟩
  · exact Or.inr ⟨b, hb, hR, hbodd, hieven,
      c, hc, hroots,
      separated_radical_centralizer_sup Q split hm 1 0 (by decide) c hroots,
      hcard⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
