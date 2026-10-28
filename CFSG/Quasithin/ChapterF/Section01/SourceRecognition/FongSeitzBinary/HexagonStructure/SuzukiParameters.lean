module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiCartanSection

/-!
# Suzuki parameter equality on the original marked hexagon

The all-parameter local identifications give the literal R_i and U_i Suzuki
markings, and discharge both local-kernel containments. The Cartan weight
argument then synchronizes the two positive parameters. This applies to any
supplied original/geometric amalgam isomorphism and to the actual quotient Q.q.
No perfectness of either original factor is assumed.

This discharges the parameter-equality step of Fong--Seitz I (6C), printed
p.40. The equal-parameter Cartan/kernel and commutator contradiction is still
required; equality alone is not the Suzuki exclusion or the (6E) dichotomy.
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
/-- Both original Suzuki fields have the same parameter in a source hexagon. -/
theorem original_suzuki_suzuki_parameters_eq (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : m = n := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_suzuki_parameters_eq Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm hn
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The same equality for the original source quotient with its literal Q.q marking. -/
theorem quotient_suzuki_suzuki_parameters_eq
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : m = n :=
  original_suzuki_suzuki_parameters_eq Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
