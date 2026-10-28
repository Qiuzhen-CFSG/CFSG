module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSeparatedKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiKernelIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiParameters

/-!
# The separated opposite-type Suzuki kernel on the original quotient

The proved five-weight argument first synchronizes the original positive
Suzuki parameters. The actual all-parameter local markings then instantiate
the separated opposite-type Cartan-kernel contradiction. Original overlap
faithfulness discharges the Borel core premise, with no original-factor
perfectness assumption. The conclusion concerns ambient subgroups and the
literal source word s_i s_j, and retains the given geometric amalgam marking
or the original quotient Q.q.

Source: Fong--Seitz I (6C), end of printed p.40 and start of p.41.
The rank-one Cartan intersection and radical commutator contradiction on
p.41, the small/solvable and unitary exclusions, and exhaustive (6E) assembly
remain required for the original theorem family.
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
/-- Parameter equality and the source separated-kernel argument on any
original/geometric marked amalgam, without original-factor perfectness. -/
theorem original_suzuki_separated_local_kernels_disjoint
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i) ⊓
      rightConjugate ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q j)
        (representative (Q.simple i*Q.simple j) : X ⧸ Q.D) = ⊥ := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_separated_local_kernels_disjoint Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The same literal s_i s_j kernel intersection for the source quotient Q.q. -/
theorem quotient_suzuki_separated_local_kernels_disjoint
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i) ⊓
      rightConjugate ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q j)
        (representative (Q.simple i*Q.simple j) : (generated L S) ⧸ Q.D) = ⊥ :=
  original_suzuki_separated_local_kernels_disjoint Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
