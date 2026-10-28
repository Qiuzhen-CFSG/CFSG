module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiKernelIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# Actual original Suzuki Cartan images and kernel intersections

The original Sylow and all-parameter local identifications supply the actual
root-generated Suzuki group and its canonical root. They discharge each
local-kernel containment, while original overlap faithfulness gives the
trivial Borel core. The full Cartan image has order q−1 and every Cartan
element factors through the actual H ∩ R_i and panel kernel. In a hexagon,
the two same-type Cartan kernels separated by the opposite reflection meet
trivially, in either orientation and with literal right-conjugation words.

These applications work with any original/geometric amalgam isomorphism,
and specialize to the source quotient with its unchanged Q.q marking.
No perfectness of the original local factors is required. The Suzuki
parameters are positive; the small Suzuki and dihedral rows remain separate.

Source: Fong--Seitz I (6C), printed p.40. The remaining opposite-type kernel
intersection and p.41 commutator contradiction are still needed for exclusion.
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
/-- The original marking supplies the full Cartan image and literal factorization. -/
theorem original_suzuki_cartan_image_and_factorization
    (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    Nat.card (ReeSource.cartanPanelMap Q i).range = 2^(2*m+1)-1 ∧
      ∀ a : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        ∃ c : (rankOne Q split i).subgroupOf (Q.tits.B ⊓ Q.tits.N),
          ∃ k : (ReeSource.cartanPanelMap Q i).ker, a = c.val * k.val := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  let μ := suzukiAllRankOneEquiv Q e h split i Ti hTi μi
  let ν := originalSuzukiAllRootEquiv Q e h split i Ti hTi μi
  have hKi := suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi
  exact ⟨suzuki_cartan_panel_image_card Q split i hKi hm μ ν,
    suzuki_cartan_factorization Q split i hKi hm μ ν⟩

include e h split in
/-- The source same-type kernel intersection, with both local-model inputs
and Borel faithfulness discharged by the original amalgam. -/
theorem original_suzuki_same_type_cartan_kernels_disjoint
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let K := (Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i
    K ⊓ rightConjugate K (representative (Q.simple j) : X ⧸ Q.D) = ⊥ := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_same_type_cartan_kernels_disjoint Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm hn
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The Cartan factorization on the literal source quotient Q.q. -/
theorem quotient_suzuki_cartan_image_and_factorization
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    Nat.card (ReeSource.cartanPanelMap Q i).range = 2^(2*m+1)-1 ∧
      ∀ a : (Q.tits.B ⊓ Q.tits.N : Subgroup ((generated L S) ⧸ Q.D)),
        ∃ c : (rankOne Q split i).subgroupOf (Q.tits.B ⊓ Q.tits.N),
          ∃ k : (ReeSource.cartanPanelMap Q i).ker, a = c.val * k.val :=
  original_suzuki_cartan_image_and_factorization Q (originalMarkedIso Q) h split i hm μi

set_option linter.unusedSectionVars false in
include h in
/-- Both orientations apply on the original source quotient with its unchanged
quotient map and endpoint equivalences. -/
theorem quotient_suzuki_same_type_cartan_kernels_disjoint
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let K := (Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i
    K ⊓ rightConjugate K (representative (Q.simple j) : (generated L S) ⧸ Q.D) = ⊥ :=
  original_suzuki_same_type_cartan_kernels_disjoint Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
