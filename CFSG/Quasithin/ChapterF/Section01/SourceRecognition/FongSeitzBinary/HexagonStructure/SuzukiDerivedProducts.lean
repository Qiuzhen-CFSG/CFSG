module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedProducts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiDerivedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiCartanProduct

/-!
# Both exact Suzuki derived-radical products on the original source

The five actual Cartan kernels separate the root quotient constituents.
This identifies the larger q⁶ derived radical as the ordered product of
four root Frattini subgroups and the whole middle root. Together with the
q⁵ branch, both source product alternatives are now explicit.

The original rank-one and root markings and the core-free Borel are
constructed from the F.1.1 marking. No original-factor perfectness is used.
The arbitrary marking includes geometric carriers; the last theorem uses
the literal Q.q image of S and the actual chosen reflection in R_j.

Source: Fong--Seitz I (6C), printed p.41. Placement of the unique natural
composition factor and the triple-commutator contradiction remain necessary,
as do the small Suzuki, unitary and exhaustive structural branches.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
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

include e h in
/-- Both source product alternatives, with their exact orders, on the same
original or geometric marking. -/
theorem original_suzuki_derived_product_alternatives (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    ((D : Set (X ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∧
      Nat.card D = 2^(5*(2*m+1))) ∨
    ((D : Set (X ⧸ Q.D)) = radicalMiddleFrattiniProduct Q split i j ∧
      Nat.card D = 2^(6*(2*m+1))) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_derived_product_alternatives Q split hhex
    (LinearThreePresentation.borel_core_eq_bot Q e h) i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

/-- The products apply to the radical of the actual marked Sylow image,
with its literal source right-conjugation reflection. -/
theorem marked_suzuki_derived_product_alternatives (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let U := (MarkedLocal.sylowMap Q e h).range
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    let D := ⁅V,V⁆
    ((D : Set (X ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∧
      Nat.card D = 2^(5*(2*m+1))) ∨
    ((D : Set (X ⧸ Q.D)) = radicalMiddleFrattiniProduct Q split i j ∧
      Nat.card D = 2^(6*(2*m+1))) := by
  dsimp only
  rw [←marked_radical_eq h Q e split j
    (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact original_suzuki_derived_product_alternatives Q e h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- Both derived products for the literal original quotient image Q.q(S). -/
theorem quotient_suzuki_derived_product_alternatives (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let U := (S.subgroupOf (generated L S)).map Q.q
    let V := U ⊓ rightConjugate U
      ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    let D := ⁅V,V⁆
    ((D : Set ((generated L S) ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∧
      Nat.card D = 2^(5*(2*m+1))) ∨
    ((D : Set ((generated L S) ⧸ Q.D)) = radicalMiddleFrattiniProduct Q split i j ∧
      Nat.card D = 2^(6*(2*m+1))) := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := marked_suzuki_derived_product_alternatives Q (originalMarkedIso Q) h split
    hhex i j hij hm hn μi μj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
