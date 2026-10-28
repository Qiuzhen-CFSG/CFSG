module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiNaturalPlacement

/-!
# Excluding regular Suzuki pairs on the original marked quotient

The all-parameter original local identifications supply the literal root
actors, root maps, local-kernel containments, and the core-free Borel.
The source natural-factor contradiction then excludes any pair of original
Suzuki quotients with at least one positive parameter. The remaining pair
must have both parameters zero. The earlier SmallSuzuki module already
excludes a positive Suzuki endpoint opposite the original D₁₀ constructor.

The arbitrary marked amalgam isomorphism includes the geometric application.
The final theorems specialize to the original SourceQuotient and its Q.q map.
No perfectness of either original factor is assumed. The split structure and
rotation-six premise retain their earlier source producers and final discharge
in source assembly. The both-small, unitary and exhaustive (6E) obligations
remain. Source: Fong--Seitz I (6C), printed pp.39--41.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split in
/-- A positive Suzuki endpoint is excluded opposite every original Suzuki
parameter, under the actual original or geometric marking. -/
theorem original_suzuki_pair_excluded_of_pos (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_pair_excluded_of_pos Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hn
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

include e h split in
/-- The two original Suzuki parameters must both be zero. This retains
the solvable pair as a genuine remaining source case. -/
theorem original_suzuki_pair_parameters_zero (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : m = 0 ∧ n = 0 := by
  constructor
  · by_contra hm
    exact original_suzuki_pair_excluded_of_pos Q e h split hhex j i hij.symm
      (Nat.pos_of_ne_zero hm) μj μi
  · by_contra hn
    exact original_suzuki_pair_excluded_of_pos Q e h split hhex i j hij
      (Nat.pos_of_ne_zero hn) μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The exclusion on the literal original source quotient, with its
original marked endpoint maps. -/
theorem quotient_suzuki_pair_excluded_of_pos (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : False :=
  original_suzuki_pair_excluded_of_pos Q (originalMarkedIso Q) h split hhex i j hij hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The both-small conclusion for the actual original quotient. -/
theorem quotient_suzuki_pair_parameters_zero (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : m = 0 ∧ n = 0 :=
  original_suzuki_pair_parameters_zero Q (originalMarkedIso Q) h split hhex i j hij μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
