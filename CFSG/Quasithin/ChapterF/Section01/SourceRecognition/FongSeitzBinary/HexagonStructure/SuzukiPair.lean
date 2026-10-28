module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiSections

/-!
# Original/geometric regular Suzuki/Suzuki parameter bounds

The source local identifications produce the two canonical root maps in the
same finite quotient.  We transport their exact root cardinalities into the
two-sided (6C) parameter theorem.  Perfectness is required only for the two
regular Suzuki local recognition maps; no unknown-group simplicity or
unrelated whole-panel model is introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The two regular original Suzuki endpoints satisfy both oriented (6C)
parameter inequalities, using the actual canonical simple roots. -/
theorem original_suzuki_suzuki_parameter_bounds
    (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    {m n : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    2*(2*m+1) ≤ 3*(2*n+1) ∧ 2*(2*n+1) ≤ 3*(2*m+1) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hmi := MarkedLocal.suzuki_parameter_pos i hpi μi
  have hmj := MarkedLocal.suzuki_parameter_pos j hpj μj
  let ai := MarkedLocal.suzukiRankOneEquiv Q e h split i hpi Ti hTi μi
  let aj := MarkedLocal.suzukiRankOneEquiv Q e h split j hpj Tj hTj μj
  let νi := originalSuzukiRootEquiv Q e h split i hpi Ti hTi μi
  let νj := originalSuzukiRootEquiv Q e h split j hpj Tj hTj μj
  have hi : Nat.card (simpleRoot Q split i) = 2^(2*(2*m+1)) := by
    have hh := MarkedLocal.suzuki_simpleRoot_card Q e h split i Ti hTi μi
    rw [← pow_mul] at hh
    have he : (2*m+1)*2 = 2*(2*m+1) := by omega
    rw [he] at hh
    exact hh
  have hj : Nat.card (simpleRoot Q split j) = 2^(2*(2*n+1)) := by
    have hh := MarkedLocal.suzuki_simpleRoot_card Q e h split j Tj hTj μj
    rw [← pow_mul] at hh
    have he : (2*n+1)*2 = 2*(2*n+1) := by omega
    rw [he] at hh
    exact hh
  obtain ⟨hijm, hnmi⟩ :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure.suzuki_suzuki_parameter_bounds
      Q split hhex i j hij hKi hKj hmi hmj ai νi aj νj hi hj
  exact ⟨by omega, by omega⟩

set_option linter.unusedSectionVars false in
include h in
/-- The same two-sided inequalities on the literal original quotient. -/
theorem quotient_suzuki_suzuki_parameter_bounds
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    {m n : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    2*(2*m+1) ≤ 3*(2*n+1) ∧ 2*(2*n+1) ≤ 3*(2*m+1) :=
  original_suzuki_suzuki_parameter_bounds Q (originalMarkedIso Q) h split hhex i j hij
    hpi hpj μi μj hKi hKj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
