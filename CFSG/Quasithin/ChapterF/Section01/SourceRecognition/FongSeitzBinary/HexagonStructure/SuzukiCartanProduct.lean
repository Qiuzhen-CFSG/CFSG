module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiKernelIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiParameters

/-!
# Full Suzuki Cartan and root kernels on the original quotient

The original overlap faithfulness supplies the trivial Borel core, and
all-parameter local identification supplies the actual source actors.
After parameter synchronization, the two rank-one Cartans generate H and
every canonical conjugate root has Cartan kernel of order q-1. Both the
geometric amalgam marking and the literal quotient Q.q are retained.

Source: Fong--Seitz I (6C), printed p.41. Native Suzuki parameters are
positive, but original-factor perfectness is not an input. These results
supply the Cartan data for the still-required derived-radical argument.
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
/-- The literal source Cartan conclusion on the original/geometric marking. -/
theorem original_suzuki_rankOne_cartans_generate
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) ⊔
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j) = Q.tits.B ⊓ Q.tits.N) ∧
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = (2^(2*m+1)-1)^2 := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_rankOne_cartans_generate Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The same conclusion for the literal source quotient Q.q. -/
theorem quotient_suzuki_rankOne_cartans_generate
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) ⊔
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j) = Q.tits.B ⊓ Q.tits.N) ∧
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup ((generated L S) ⧸ Q.D)) = (2^(2*m+1)-1)^2 :=
  original_suzuki_rankOne_cartans_generate Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

include e h split in
/-- The literal source Cartan conclusion on the original/geometric marking. -/
theorem original_suzuki_rootAction_kernel_card
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) (k : Fin 2) (w : Weyl Q) :
    Nat.card (ReeSource.rootAction Q split k w).ker = 2^(2*m+1)-1 := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_rootAction_kernel_card Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) k w

set_option linter.unusedSectionVars false in
include h in
/-- The same conclusion for the literal source quotient Q.q. -/
theorem quotient_suzuki_rootAction_kernel_card
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) (k : Fin 2) (w : Weyl Q) :
    Nat.card (ReeSource.rootAction Q split k w).ker = 2^(2*m+1)-1 :=
  original_suzuki_rootAction_kernel_card Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj k w

include e h split in
/-- The literal source Cartan conclusion on the original/geometric marking. -/
theorem original_suzuki_rootAction_kernel_ne_bot
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) (k : Fin 2) (w : Weyl Q) :
    (ReeSource.rootAction Q split k w).ker ≠ ⊥ := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_rootAction_kernel_ne_bot Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) k w

set_option linter.unusedSectionVars false in
include h in
/-- The same conclusion for the literal source quotient Q.q. -/
theorem quotient_suzuki_rootAction_kernel_ne_bot
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) (k : Fin 2) (w : Weyl Q) :
    (ReeSource.rootAction Q split k w).ker ≠ ⊥ :=
  original_suzuki_rootAction_kernel_ne_bot Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj k w

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
