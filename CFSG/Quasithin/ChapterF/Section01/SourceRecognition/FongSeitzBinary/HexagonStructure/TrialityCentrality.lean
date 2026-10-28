module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.StructuralApplication

/-!
# Discharge the centrality premises of the actual triality consumer

The small-section and Cartan arguments prove the long-central and
orthogonal fields of TrialitySource.StructuralRow. The preceding derived
identity and nonzero long-root commutator remain explicit, so this is a
reduction from four structural premises to two, not a proof of (6E)(b).
The latter two identities and the irreducible module remain with this
HexagonStructure family. The subsequent field pinnings and module equations
remain with the triality source-relation owner.

Apply the constructed row to the published positiveCommutations theorem
on the same RankOnePair, WeylPlacement and canonical simple-root ranges.
It yields all ten actual positive commuting pairs. The binary application
uses the original marked Sylow count and kernel theorem and requires no
perfectness of either original factor, including the universal/geometric
carrier. No mixed polynomial equation or group recognition is assumed.

Source: Fong–Seitz I (6E)(b), printed pp.43–45; II (9.22), pp.217–220.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- Two actual 6E centrality obligations are discharged. The derived identity
and the nonzero long commutator remain preceding mathematical obligations. -/
theorem triality_structuralRow_of_middle_root
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i)) :
    TrialitySource.StructuralRow Q split j i := by
  have hsmall : Nat.card (simpleRoot Q split i) < 2^(2*b) := by
    rw [GTwoSource.simpleRoot_card Q split i hKi μi,hE]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hz := derived_middle_root_zero_relations Q split j hKj μj
    (UnitarySource.actorReflection Q split j) hm i hij hKi μi hderived (by omega) hF hsmall
  exact ⟨hderived,hlong,hz.1,hz.2.2.2⟩

/-- Apply the new centrality proofs to the exact published signed-root
consumer, with the cubic endpoint w.indices 0 and the fixed endpoint w.indices 1. -/
theorem triality_positiveCommutations_of_middle_root
    {σ : F ≃+* F}
    (p : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair σ (X ⧸ Q.D))
    (w : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.WeylPlacement Q p)
    (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
    (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
    (hm : rotationOrder Q = 6)
    (hKi : simpleRemainder Q split (w.indices 1) ≤ localKernel Q (w.indices 1))
    (hKj : simpleRemainder Q split (w.indices 0) ≤ localKernel Q (w.indices 0))
    (μi : localGroup Q split (w.indices 1) ≃* PSL(2,E))
    (μj : localGroup Q split (w.indices 0) ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (hderived : ⁅simpleRemainder Q split (w.indices 0),simpleRemainder Q split (w.indices 0)⁆ =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1)))
    (hlong : ⁅simpleRoot Q split (w.indices 1),rootAt Q split (w.indices 1) (Q.simple (w.indices 0))⁆ =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1))) :
    p.PositiveCommutations :=
  TrialitySource.StructuralApplication.positiveCommutations Q split p w shortBase longBase hm
    (triality_structuralRow_of_middle_root Q split hm (w.indices 1) (w.indices 0)
      (w.indices.injective.ne (by decide)) hKi hKj μi μj ha hab hE hF hderived hlong)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

include e h in
/-- The original binary opposite endpoint supplies centrality without any
perfectness or identification of original and source local groups. -/
theorem binary_triality_structuralRow_of_original_factors
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F)) (hE : Nat.card E = 2)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i)) :
    TrialitySource.StructuralRow Q split j i := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hKj := MarkedLocal.linear_remainder_le_kernel Q e h split j Tj hTj μj
  have hc : Nat.card (simpleRoot Q split i) = 2 :=
    (MarkedLocal.simpleRoot_card_linear Q e h split i Ti hTi μi).trans hE
  have hz := binary_derived_middle_root_zero_relations Q split j hm i hij hKj hderived hc
  exact ⟨hderived,hlong,hz.1,hz.2.2.2⟩

include e h in
/-- The same ten positive commuting pairs on the original/geometric marking;
the binary case retains both full original factors, including nonperfect ones. -/
theorem binary_triality_positiveCommutations_of_original_factors
    {σ : F ≃+* F}
    (p : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair σ (X ⧸ Q.D))
    (w : Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.WeylPlacement Q p)
    (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
    (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
    (hm : rotationOrder Q = 6)
    (μi : ((L (w.indices 1)) ⧸ pCore 2 (L (w.indices 1))) ≃* PSL(2,E))
    (μj : ((L (w.indices 0)) ⧸ pCore 2 (L (w.indices 0))) ≃* PSL(2,F))
    (hE : Nat.card E = 2)
    (hderived : ⁅simpleRemainder Q split (w.indices 0),simpleRemainder Q split (w.indices 0)⁆ =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1)))
    (hlong : ⁅simpleRoot Q split (w.indices 1),rootAt Q split (w.indices 1) (Q.simple (w.indices 0))⁆ =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1))) :
    p.PositiveCommutations :=
  TrialitySource.StructuralApplication.positiveCommutations Q split p w shortBase longBase hm
    (binary_triality_structuralRow_of_original_factors Q split e h hm (w.indices 1) (w.indices 0)
      (w.indices.injective.ne (by decide)) μi μj hE hderived hlong)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
