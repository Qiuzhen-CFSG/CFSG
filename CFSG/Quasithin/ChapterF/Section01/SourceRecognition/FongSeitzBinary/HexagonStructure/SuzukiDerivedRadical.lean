module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiKernelIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiParameters

/-!
# Derived-radical alternatives on the original Suzuki quotient

All-parameter local identification supplies the actual Suzuki actors and
root markings, without original-factor perfectness. The source radical's
Frattini subgroup is its derived subgroup. Parameter synchronization then
gives the derived orders q⁵ or q⁶ and a genuine natural subquotient of its
Frattini quotient, using the same original Sylow and quotient maps.

Both general original/geometric markings and the literal source quotient
Q.q are included. Source: Fong--Seitz I (6C), printed p.41. The exact
root-product location, triple-commutator contradiction and the remaining
small, unitary and exhaustive structural branches are still required.
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

/-- The actual original action on the derived radical's effective section.
The numerator identification is proved below at the positive parameters. -/
abbrev originalSuzukiDerivedRepresentation (j : Fin 2) [Finite (L j)]
    (T : Sylow 2 (L j)) (hT : (T : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {n : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :=
  let f := frattiniSection Q split j (radicalSection Q split j
    (suzuki_remainder_le_kernel_all Q e h split j T hT μ))
  f.effectiveRepresentation.comp (suzukiAllRankOneEquiv Q e h split j T hT μ).symm.toMonoidHom

include e h in
/-- The original radical's Frattini subgroup equals its actual derived group. -/
theorem original_suzuki_radical_frattini_eq_commutator (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hn
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

include e h in
/-- The source derived-order alternatives, on ambient subgroups of the
same original/geometric quotient. -/
theorem original_suzuki_derived_radical_card (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^(5*(2*m+1)) ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1)) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact suzuki_derived_radical_card Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

include e h in
/-- The representation's numerator is the literal ambient derived radical,
with the chosen original Sylow retained in its kernel producer. -/
theorem original_suzuki_derived_numerator (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (frattiniSection Q split j (radicalSection Q split j
      (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj))).numerator =
        ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_frattiniSection_numerator_eq_derived Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm hn
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

include e h in
/-- A genuine natural section of the original derived-radical action,
including its literal actor map, subspaces and linear intertwiner. -/
theorem original_suzuki_derived_radical_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∃ U : Subrepresentation (originalSuzukiDerivedRepresentation Q e h split j Tj hTj μj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) := by
  have he := original_suzuki_suzuki_parameters_eq Q e h split hhex i j hij hm hn μi μj
  subst n
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  exact suzuki_derived_radical_natural_section Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj)

set_option linter.unusedSectionVars false in
include h in
/-- The same derived-radical conclusion on the literal quotient Q.q. -/
theorem quotient_suzuki_radical_frattini_eq_commutator (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j) :=
  original_suzuki_radical_frattini_eq_commutator Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The same derived-radical conclusion on the literal quotient Q.q. -/
theorem quotient_suzuki_derived_radical_card (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup ((generated L S) ⧸ Q.D)) = 2^(5*(2*m+1)) ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup ((generated L S) ⧸ Q.D)) = 2^(6*(2*m+1)) :=
  original_suzuki_derived_radical_card Q (originalMarkedIso Q) h split hhex i j hij hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The same derived-radical conclusion on the literal quotient Q.q. -/
theorem quotient_suzuki_derived_numerator (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    (frattiniSection Q split j (radicalSection Q split j
      (suzuki_remainder_le_kernel_all Q (originalMarkedIso Q) h split j Tj hTj μj))).numerator =
        ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :=
  original_suzuki_derived_numerator Q (originalMarkedIso Q) h split hhex i j hij Tj hTj hm hn μi μj

set_option linter.unusedSectionVars false in
include h in
/-- The same derived-radical conclusion on the literal quotient Q.q. -/
theorem quotient_suzuki_derived_radical_natural_section (Q : SourceQuotient L S) (split : SplitData Q.tits) (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) [Finite (L j)]
    (Tj : Sylow 2 (L j)) (hTj : (Tj : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) :
    ∃ U : Subrepresentation (originalSuzukiDerivedRepresentation Q (originalMarkedIso Q) h split j Tj hTj μj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) :=
  original_suzuki_derived_radical_natural_section Q (originalMarkedIso Q) h split hhex i j hij Tj hTj hm hn μi μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
