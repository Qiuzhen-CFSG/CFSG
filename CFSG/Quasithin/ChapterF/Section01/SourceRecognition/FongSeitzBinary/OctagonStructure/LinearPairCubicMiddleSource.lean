module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicDegreeOneSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleCentralizer

/-!
# The degree-one middle-root centralizer at the original source pair

The five consecutive middle roots form a subgroup of order 128, normal in
U_(s_i), and centralize the middle odd root. Thus its centralizer in U_(s_i)
has index at most sixteen. All panel-kernel containments, root orders and
the cubic actor are constructed from the original PSL₂(2), PSL₂(4) factors.
The full marked amalgam, including both endpoint maps, is retained.

Source: Fong--Seitz I (6G), printed p.50, the five-root subgroup in the
first paragraph. Proving that this centralizer is the whole radical and
the subsequent normalizer contradiction remains separate work.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal LinearPanel ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

private theorem binary_marking {Y : Type*} [Group Y] {a : ℕ}
    (ha : 0 < a) (hlinear : ClassicalGroup.IsPSL Y 2 (2^a)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup a) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 a ha.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

include e h in
private theorem original_root_data (i : Fin 2) (a : ℕ) (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nat.card (simpleRoot Q split i) = 2^a := by
  obtain ⟨μ⟩ := binary_marking ha hi
  obtain ⟨σ,T,_,hB,_,_,_,_⟩ := original_panel Q e h split i μ
  let := h.finite_local i
  obtain ⟨T₀,hT₀⟩ := h.sylow i
  exact ⟨linear_remainder_le_kernel Q e h split i T₀ hT₀ μ,
    by simpa only [rootAt_one] using linear_rootAt_card Q split i a σ T hB ha 1⟩

include e h split in
/-- The actual order-128 normal subgroup and index-sixteen bound in the
source degree-one centralizer argument, in either endpoint orientation. -/
theorem original_linear_degree_one_middle_centralizer
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    Nat.card (middleFive Q split i j) = 128 ∧
    middleFive Q split i j ≤ simpleRemainder Q split i ⊓
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) ∧
    simpleRemainder Q split i ≤ normalizer (middleFive Q split i j : Set (X ⧸ Q.D)) ∧
    (simpleRemainder Q split i ⊓
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))).relIndex
        (simpleRemainder Q split i) ≤ 16 := by
  obtain ⟨hKi,hci⟩ := original_root_data Q e h split i 1 (by decide) hi
  obtain ⟨hKj,hcj⟩ := original_root_data Q e h split j 2 (by decide) hj
  norm_num at hci hcj
  obtain ⟨c,_,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input Q e h split hm
    i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  refine ⟨?_,le_inf (middleFive_le_remainder Q split hm i j hij)
    (separated_middleFive_centralizes Q split hm i j hij hKi hKj hci c hc),
    middleFive_normalized_by_remainder Q split hm i j hij hKj,
    separated_binary_middle_centralizer_index_le Q split hm i j hij hKi hKj hci hcj c hc⟩
  rw [middleFive_card Q split hm i j hij,hci,hcj]
  norm_num

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
