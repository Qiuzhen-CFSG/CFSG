module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiDerivedRadical

/-!
# Exact derived-radical root intersections on the original Suzuki quotient

The original all-parameter identifications construct the actual rank-one
actors and canonical root markings. Parameter synchronization and the
source square/reflection argument then exclude every nonmiddle whole root
from the derived radical and identify its intersection as the root Frattini
subgroup. The literal root Frattini maps are injective on these four roots.
The smaller derived-order branch is the exact ordered product of the five
root Frattini subgroups.

The arbitrary amalgam marking covers the original and geometric applications;
the final exports use Q.q through originalMarkedIso. No original-factor
perfectness is assumed. Positive native Suzuki parameters remain necessary.
Source: Fong--Seitz I (6C), printed p.41. These are local structural steps;
the larger-order root-product decomposition and final Suzuki contradiction remain open.
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
/-- All five root Frattini subgroups lie in the derived radical; each of the
four nonmiddle roots intersects it in precisely that Frattini subgroup. -/
theorem original_suzuki_derived_root_intersections (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∀ t : Fin 5,
      let A := rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)
      let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
      (frattini A).map A.subtype ≤ D ∧
        (t ≠ 2 → (¬ A ≤ D) ∧ A ⊓ D = (frattini A).map A.subtype) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  let ki := suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi
  let kj := suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj
  let ri := suzukiAllRankOneEquiv Q e h split i Ti hTi μi
  let rj := suzukiAllRankOneEquiv Q e h split j Tj hTj μj
  let ui := originalSuzukiAllRootEquiv Q e h split i Ti hTi μi
  let uj := originalSuzukiAllRootEquiv Q e h split j Tj hTj μj
  intro t
  refine ⟨suzuki_radical_root_frattini_le_derived Q split hhex i j hij hm hm ui uj t,?_⟩
  intro ht
  exact ⟨suzuki_nonmiddle_root_not_le_derived Q split hhex i j hij ki kj hm ri rj ui uj t ht,
    suzuki_nonmiddle_root_inf_derived Q split hhex i j hij ki kj hm ri rj ui uj t ht⟩

include e h in
/-- The actual second Frattini layer has trivial rank-one action. The
Sylow marking determines the literal original panel-kernel inclusion. -/
theorem original_suzuki_second_frattini_radical_action_eq_one (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (frattiniSection Q split j (frattiniSection Q split j (radicalSection Q split j
      (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj)))).action = 1 := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_second_frattini_radical_action_eq_one Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

include e h in
/-- The four actual Cartan-equivariant root quotient maps embed in the
original radical quotient, with the chosen original Sylow retained. -/
theorem original_suzuki_nonmiddle_root_intertwiner_injective (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n)
    (t : Fin 5) (ht : t ≠ 2) :
    Function.Injective (radicalRootIntertwiner Q split hhex i j hij
      (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) t) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_nonmiddle_root_intertwiner_injective Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) t ht

set_option linter.unusedSectionVars false in
include h in
/-- The exact five-root profile on the literal quotient Q.q. -/
theorem quotient_suzuki_derived_root_intersections (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∀ t : Fin 5,
      let A := rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)
      let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
      (frattini A).map A.subtype ≤ D ∧
        (t ≠ 2 → (¬ A ≤ D) ∧ A ⊓ D = (frattini A).map A.subtype) :=
  original_suzuki_derived_root_intersections Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- Second Frattini centralization on Q.q, with the literal actor action. -/
theorem quotient_suzuki_second_frattini_radical_action_eq_one (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (frattiniSection Q split j (frattiniSection Q split j (radicalSection Q split j
      (suzuki_remainder_le_kernel_all Q (originalMarkedIso Q) h split j Tj hTj μj)))).action = 1 :=
  original_suzuki_second_frattini_radical_action_eq_one Q (originalMarkedIso Q) h split
    hhex i j hij Tj hTj hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The same four literal root quotient embeddings on Q.q. -/
theorem quotient_suzuki_nonmiddle_root_intertwiner_injective (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n)
    (t : Fin 5) (ht : t ≠ 2) :
    Function.Injective (radicalRootIntertwiner Q split hhex i j hij
      (suzuki_remainder_le_kernel_all Q (originalMarkedIso Q) h split j Tj hTj μj) t) :=
  original_suzuki_nonmiddle_root_intertwiner_injective Q (originalMarkedIso Q) h split
    hhex i j hij Tj hTj hm hn μi μj t ht


include e h in
/-- The smaller derived-order branch has its exact ordered root product.
Only the larger q⁶ branch retains a root-product placement obligation. -/
theorem original_suzuki_derived_product_or_large_order (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) :
        Set (X ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1)) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_derived_product_or_large_order Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The exact smaller-branch product on the original source quotient Q.q. -/
theorem quotient_suzuki_derived_product_or_large_order (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup ((generated L S) ⧸ Q.D)) :
        Set ((generated L S) ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup ((generated L S) ⧸ Q.D)) = 2^(6*(2*m+1)) :=
  original_suzuki_derived_product_or_large_order Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
