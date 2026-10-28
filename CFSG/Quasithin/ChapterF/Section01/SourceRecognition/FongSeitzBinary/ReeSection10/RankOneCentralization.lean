module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.PositiveRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.SuzukiLayers

/-!
# Rank-one centralization of the perpendicular linear root

The linear simple root centralizes its perpendicular fourth relative root by
(10.2)(iv). Conjugating that relation by the supplied linear reflection and
using perpendicular-root stability gives the same statement for the reflected
simple root. Since the simple root and its conjugate generate the linear
rank-one group, the entire rank-one group centralizes the fourth root.

This is the linear counterpart of
`rankOne_centralizes_perpendicularSuzuki`; it uses the literal normalizer
representative and retains the binary case.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
/-- The full linear rank-one group centralizes its perpendicular root. -/
theorem rankOne_centralizes_perpendicularLinear :
    rankOne Q split 0 ≤ centralizer (positiveRoot Q split (.inl 3) : Set (X ⧸ Q.D)) := by
  have h0 : ⁅simpleRoot Q split 0, positiveRoot Q split (.inl 3)⁆ = ⊥ := by
    simpa [nConj, U, Uat, OneMemClass.coe_one, rightConjugate_one,
      positiveRoot, positiveKind, positiveWord, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply] using c.relations.ten_two_iv_left 1
  let s := (c.reflections 0).val
  have h1 : ⁅rightConjugate (simpleRoot Q split 0) (s : X ⧸ Q.D),
      positiveRoot Q split (.inl 3)⁆ = ⊥ := by
    have h := c.relations.ten_two_iv_left s
    change ⁅rightConjugate (simpleRoot Q split 0) (s : X ⧸ Q.D),
      rightConjugate (rootAt Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1))
        (s : X ⧸ Q.D)⁆ = ⊥ at h
    rw [perpendicular_root_stable Q split c.rotation_eight 0 1 (by decide)
      s (c.reflections 0).class_eq] at h
    exact h
  rw [rankOne_eq Q split 0 s (c.reflections 0).class_eq]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h0)
    (commutator_eq_bot_iff_le_centralizer.mp h1)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
