module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiPairSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedSuzuki

/-!
# Natural sections on the original Suzuki/Suzuki hexagon

The all-parameter local cover identifies the actual root-generated actor
and its Sylow. For two positive Suzuki parameters the five-root Frattini
bound gives the literal radical degree window. When the parameters are
ordered, its actual binary action has an invariant subquotient equivalent
to the natural Suzuki module. The representation uses the canonical local
cover map, and the output retains the subspaces and linear intertwiner.

These applications work with the supplied original or geometric marked
amalgam isomorphism and specialize to the literal original quotient Q.q.
They discharge the local-kernel premises using SuzukiAllRegularity; no
original-factor perfectness is assumed. Positivity excludes Sz(2) from
this particular degree argument. Parameter equality, the regular-pair
contradiction, and the remaining small/solvable rows remain to be proved.

Source: Fong--Seitz I (6C), printed pp.40--41.
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

/-- The representation determined by the actual original Suzuki quotient
and its marked Sylow, using the proved local-kernel containment. -/
abbrev originalSuzukiRadicalRepresentation (j : Fin 2) [Finite (L j)]
    (T : Sylow 2 (L j)) (hT : (T : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {n : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :=
  suzukiRadicalRepresentation Q split j
    (suzuki_remainder_le_kernel_all Q e h split j T hT μ)
    (suzukiAllRankOneEquiv Q e h split j T hT μ)

include e h in
/-- The upper and lower bounds on the literal original radical quotient.
The kernel and model inputs are supplied by the actual local cover. -/
theorem original_suzuki_suzuki_radical_bounds (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    2^(4*(2*n+1)) ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ≤
      2^(3*(2*m+1)+2*(2*n+1)) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hKj := suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj
  exact ⟨suzuki_radical_card_bound Q split j hn
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj) hhex i hij
    (UnitarySource.actorReflection Q split j) hKj,
    suzuki_suzuki_radical_frattini_upper Q split hhex i j hij hm hn
      (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
      (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)⟩

include e h in
/-- The source interval on the original marked quotient when a<b. -/
theorem original_suzuki_suzuki_radical_window (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    2^(4*(2*n+1)) ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) < 2^(5*(2*n+1)) := by
  obtain ⟨hlo,hhi⟩ := original_suzuki_suzuki_radical_bounds Q e h split hhex i j hij hm hn μi μj
  exact ⟨hlo,hhi.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))⟩

include e h in
/-- A natural section of the actual original Suzuki radical representation,
with the source subspaces and the exact canonical actor map retained. -/
theorem original_suzuki_suzuki_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∃ U : Subrepresentation (originalSuzukiRadicalRepresentation Q e h split j Tj hTj μj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_suzuki_radical_natural_section Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm hn hmn
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The same bounds on the literal source quotient Q.q. -/
theorem quotient_suzuki_suzuki_radical_bounds
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    2^(4*(2*n+1)) ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ≤
      2^(3*(2*m+1)+2*(2*n+1)) :=
  original_suzuki_suzuki_radical_bounds Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The unequal-parameter degree window on Q.q. -/
theorem quotient_suzuki_suzuki_radical_window
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    2^(4*(2*n+1)) ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) < 2^(5*(2*n+1)) :=
  original_suzuki_suzuki_radical_window Q (originalMarkedIso Q) h split hhex i j hij hm hn hmn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- Natural subquotients of the original quotient action, with no
original-factor perfectness assumption. -/
theorem quotient_suzuki_suzuki_natural_section
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∃ U : Subrepresentation
        (originalSuzukiRadicalRepresentation Q (originalMarkedIso Q) h split j Tj hTj μj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) :=
  original_suzuki_suzuki_natural_section Q (originalMarkedIso Q) h split hhex i j hij
    Tj hTj hm hn hmn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
