module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiPairSection

/-!
# Cartan-invariant sections on the original Suzuki/Suzuki hexagon

The actual local cover and Sylow markings instantiate the HR_j-invariant
natural-section theorem on an arbitrary supplied original/geometric marked
amalgam, and on the literal source quotient Q.q. Both relative subspaces
remain invariant under HR_j; the Suzuki intertwiner uses the same original
cover map. All local-kernel containments are discharged by the proved
all-parameter Suzuki regularity theorem. No original-factor perfectness
is assumed. The representation argument requires positive parameters.

Source: Fong--Seitz I (6C), printed pp.40--41. The remaining Cartan-weight
argument must prove parameter equality, followed by the equal-parameter
kernel and commutator contradiction; this section alone is not an exclusion.
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
/-- The actual original/geometric HR_j action has an HR_j-invariant natural
Suzuki section, with the original cover map and both relative subspaces. -/
theorem original_suzuki_suzuki_cartan_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let hKj := suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj
    let K := radicalCartanRankOne Q split j
    let μ := (radicalCartanRankOneEquiv Q split j).trans
      (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    ∃ U : Subrepresentation (radicalCartanRepresentation Q split j hKj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Representation.IsIrreducible (N.quotientRepresentation.comp K.subtype) ∧
        Nonempty (Representation.Equiv
          (N.quotientRepresentation.comp (K.subtype.comp μ.symm.toMonoidHom))
          (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_suzuki_cartan_natural_section Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm hn hmn
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The HR_j-invariant section on the literal source quotient Q.q. -/
theorem quotient_suzuki_suzuki_cartan_natural_section
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    let hKj := suzuki_remainder_le_kernel_all Q (originalMarkedIso Q) h split j Tj hTj μj
    let K := radicalCartanRankOne Q split j
    let μ := (radicalCartanRankOneEquiv Q split j).trans
      (suzukiAllRankOneEquiv Q (originalMarkedIso Q) h split j Tj hTj μj)
    ∃ U : Subrepresentation (radicalCartanRepresentation Q split j hKj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Representation.IsIrreducible (N.quotientRepresentation.comp K.subtype) ∧
        Nonempty (Representation.Equiv
          (N.quotientRepresentation.comp (K.subtype.comp μ.symm.toMonoidHom))
          (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) :=
  original_suzuki_suzuki_cartan_natural_section Q (originalMarkedIso Q) h split hhex i j hij
    Tj hTj hm hn hmn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
