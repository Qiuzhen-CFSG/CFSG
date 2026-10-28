module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzukiLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSuzuki

/-!
# The two solvable order-four endpoints on the original marked quotient

The original Sz(2) and dihedral D₁₀ alternatives both supply the actual
Sz(2) root actor and cyclic order-four canonical root. Their proved kernel
inclusions give the two actual Frattini sections, without original-factor
perfectness. For a pair of these endpoints, each radical has second
Frattini subgroup of order at most four, derived subgroup of order at most
sixteen, and nonzero third lower-central term. The last conclusion uses
the actual order-four root action and its nonzero cubic displacement.

The same results are stated on the literal marked Sylow image, and on
(S ∩ generated L S).map Q.q. These are the surviving small-pair constraints
in Fong--Seitz I (5H), printed p.30. The argument that the radicals have
class at most two, and hence the final small-pair exclusion, remains to be
proved. Regular Suzuki pairs, the remaining unitary rows and exhaustive
(6E) assembly also remain with this family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped Pointwise MatrixGroups
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
private theorem small_actor_inputs (j : Fin 2)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
    Nonempty (rankOne Q split j ≃* SuzukiMatrixGroup 0) ∧
    Nonempty (simpleRoot Q split j ≃* SuzukiRootSubgroup 0) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hj with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact ⟨suzuki_remainder_le_kernel_all Q e h split j T hT μ,
      ⟨suzukiAllRankOneEquiv Q e h split j T hT μ⟩,
      ⟨originalSuzukiAllRootEquiv Q e h split j T hT μ⟩⟩
  · exact ⟨dihedral_remainder_le_kernel Q e h split j T hT μ,
      ⟨dihedralSuzukiRankOneEquiv Q e h split j T hT μ⟩,
      ⟨originalDihedralRootEquiv Q e h split j T hT μ⟩⟩

include e h in
/-- Both actual source Frattini sections, for either original small constructor. -/
theorem original_smallSuzuki_two_layers (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    16 ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    16 ≤ Nat.card (frattini (simpleRemainder Q split j) ⧸
      frattini (frattini (simpleRemainder Q split j))) := by
  obtain ⟨hK,⟨μ⟩,⟨ν⟩⟩ := small_actor_inputs Q e h split j hj
  exact smallSuzuki_radical_two_layers Q split hm i j hij hK μ ν

include e h in
/-- On each orientation, two small original endpoints force the exact
Frattini and commutator bounds and the nonzero third lower-central term. -/
theorem original_smallSuzuki_pair_radical (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    Nat.card (frattini (frattini (simpleRemainder Q split j))) ≤ 4 ∧
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ≤ 16 ∧
    ⁅simpleRemainder Q split j,⁅simpleRemainder Q split j,simpleRemainder Q split j⁆⁆ ≠ ⊥ := by
  obtain ⟨hKi,⟨μi⟩,⟨νi⟩⟩ := small_actor_inputs Q e h split i hi
  obtain ⟨hKj,⟨μj⟩,⟨νj⟩⟩ := small_actor_inputs Q e h split j hj
  have hc : Nat.card (simpleRoot Q split i) = 4 := by
    rw [Nat.card_congr νi.toEquiv,ReeSource.matrixRoot_card]; norm_num
  exact ⟨smallSuzuki_second_frattini_card_le_four Q split hm i j hij hKj μj νj hc,
    smallSuzuki_pair_derived_card_le_sixteen Q split hm i j hij hKi hKj μj νi νj,
    smallSuzuki_opposite_radical_not_classTwo Q split hm j i hij.symm hKj hKi μi νi⟩

include e h in
/-- The Frattini intersection with the literal own-root conjugate has
exponent two, in both original small constructors. -/
theorem original_smallSuzuki_pair_frattini_root (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (a : rootAt Q split j (Q.simple i))
    (ha : (a : X ⧸ Q.D) ∈ (frattini (simpleRemainder Q split j)).map
      (simpleRemainder Q split j).subtype) : a^2 = 1 := by
  obtain ⟨_,_,⟨νi⟩⟩ := small_actor_inputs Q e h split i hi
  obtain ⟨hKj,⟨μj⟩,⟨νj⟩⟩ := small_actor_inputs Q e h split j hj
  have hc : Nat.card (simpleRoot Q split i) = 4 := by
    rw [Nat.card_congr νi.toEquiv,ReeSource.matrixRoot_card]; norm_num
  exact smallSuzuki_frattini_root_square_eq_one Q split hm i j hij hKj μj νj hc a ha

include e h split in
/-- The same constraints on the literal original/geometric Sylow-image
radical, for any representative of the specified reflection. -/
theorem marked_smallSuzuki_pair_radical (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (s : Q.tits.N)
    (hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s = Q.simple j) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range (s : X ⧸ Q.D)
    Nat.card (frattini (frattini V)) ≤ 4 ∧
      Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) ≤ 16 ∧ ⁅V,⁅V,V⁆⁆ ≠ ⊥ := by
  dsimp only
  rw [←marked_radical_eq h Q e split j s hs]
  exact original_smallSuzuki_pair_radical Q e h split hm i j hij hi hj

/-- Both layers on the original source quotient, with no perfectness assumption. -/
theorem quotient_smallSuzuki_two_layers
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    16 ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    16 ≤ Nat.card (frattini (simpleRemainder Q split j) ⧸
      frattini (frattini (simpleRemainder Q split j))) :=
  original_smallSuzuki_two_layers Q (originalMarkedIso Q) h split hm i j hij hj

/-- The original Q.q image and right conjugation are retained explicitly. -/
theorem quotient_smallSuzuki_pair_radical
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (s : Q.tits.N)
    (hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s = Q.simple j) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q) (s : (generated L S) ⧸ Q.D)
    Nat.card (frattini (frattini V)) ≤ 4 ∧
      Nat.card (⁅V,V⁆ : Subgroup ((generated L S) ⧸ Q.D)) ≤ 16 ∧ ⁅V,⁅V,V⁆⁆ ≠ ⊥ := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ←sylow_range Q (originalMarkedIso Q) h split]
  exact marked_smallSuzuki_pair_radical Q (originalMarkedIso Q) h split hm i j hij hi hj s hs

/-- The root/Frattini intersection on the same original quotient. -/
theorem quotient_smallSuzuki_pair_frattini_root
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (a : rootAt Q split j (Q.simple i))
    (ha : (a : (generated L S) ⧸ Q.D) ∈ (frattini (simpleRemainder Q split j)).map
      (simpleRemainder Q split j).subtype) : a^2 = 1 :=
  original_smallSuzuki_pair_frattini_root Q (originalMarkedIso Q) h split hm i j hij hi hj a ha

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
