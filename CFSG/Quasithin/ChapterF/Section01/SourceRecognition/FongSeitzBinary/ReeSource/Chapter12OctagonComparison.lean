module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCompleteConsumer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter 12 octagon comparison from the selected factor alternatives

The octagonal source branch already constructs the complete Section 10
comparison from a marked linear factor and a Suzuki or dihedral opposite
factor.  This leaf packages that comparison at the literal Chapter 12
boundary, preserving the same marked quotient, split data, full Borel and
both endpoint squares.  It does not select the octagon branch or discharge
the remaining linear/unitary alternatives.

Source: Fong--Seitz I (6H), pp.51--56; Fong--Seitz II, Section 10;
Aschbacher--Smith 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source
open ChapterF.Source.FongSeitzBinary
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
/-- The selected octagon linear/Suzuki or linear/dihedral branch gives the
literal Ree row of the generic Chapter 12 catalogue. -/
theorem rankOne_octagon_ree_comparison_of_suzuki_or_dihedral
    (hother :
      (∃ a, Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* DihedralGroup 5)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  have hlinear : ClassicalGroup.IsPSL
      ((![L,R] 0) ⧸ pCore 2 (![L,R] 0)) 2 (2^n) := by
    change ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)
    exact hpsl
  have hother' :
      (∃ a, Nonempty (((![L,R] 1) ⧸ pCore 2 (![L,R] 1)) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty (((![L,R] 1) ⧸ pCore 2 (![L,R] 1)) ≃* DihedralGroup 5) := by
    cases hother with
    | inl hs =>
      obtain ⟨a,ha⟩ := hs
      obtain ⟨μ⟩ := ha
      left
      exact ⟨a, ⟨by
        change (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup a
        exact μ⟩⟩
    | inr hd =>
      obtain ⟨μ⟩ := hd
      right
      exact ⟨by
        change (R ⧸ pCore 2 R) ≃* DihedralGroup 5
        exact μ⟩
  rcases original_suzuki_or_dihedral_concrete_comparison Q e hf split hm n
      (Nat.zero_lt_of_lt hn) hlinear hother' with ⟨m, he⟩
  exact Global.ConcreteAmalgamComparison.ree m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
