module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicSectionSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicCentralizerDichotomy

/-!
# The exact middle-root centralizer alternatives at the original pair

The original PSL₂(2), PSL₂(4) factors give the local linear root action.
The end-root reflection argument excludes index four without perfectness
of the binary factor. Cubic congruence then leaves index one or sixteen;
these identify the centralizer with the whole radical or exactly its five
middle roots. Both orientations, the full Borel and both endpoint maps
are retained in the original marking.

Source: Fong--Seitz I (1973), (6G), printed p.50, first paragraph. This
establishes that paragraph's centralizer dichotomy, not its subsequent
exclusion of the second alternative or the terminal (6G) theorem.
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


include e h in
private theorem original_linear_marking (i : Fin 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nat.card (simpleRoot Q split i) = Nat.card F ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hK := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μ]
    exact ((Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  exact ⟨hK,simpleRoot_card_linear Q e h split i T hT μ,
    ⟨(regularFactorLocalEquiv Q e h split i T hT hK hc hz).trans μ⟩⟩

include e h split in
/-- The original degree-one centralizer has exactly the two alternatives
stated at the beginning of printed p.50. No index-four case remains. -/
theorem original_linear_degree_one_centralizer_dichotomy
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    middleRootCentralizer Q split i j = simpleRemainder Q split i ∨
      middleRootCentralizer Q split i j = middleFive Q split i j := by
  have hJC := (original_linear_degree_one_middle_centralizer Q e h split hm i j hij hi hj).2.1
  obtain ⟨hPC,hn,_,hindex⟩ := original_linear_degree_one_centralizer_quotient Q e h split hm i j hij hi hj
  change (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 1 ∨
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 4 ∨
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 16 at hindex
  obtain ⟨F,hF,hfin,hFcard,⟨μi⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hFcard)
  obtain ⟨E,hE,hfinE,hEcard,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hEcard])
  obtain ⟨hKi,hci,_⟩ := original_linear_marking Q e h split i μi
  obtain ⟨hKj,hcj,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  have hi2 := hci.trans hFcard
  have hj4 := hcj.trans hEcard
  rcases hindex with h1 | h4 | h16
  · exact Or.inl (le_antisymm inf_le_left (relIndex_eq_one.mp h1))
  · exact (binary_middle_overgroup_index_ne_four Q split hm i j hij hKi hKj νj
      (UnitarySource.actorReflection Q split i) hi2 hj4 _ hJC inf_le_left hPC h4).elim
  · apply Or.inr
    have hq := binary_middleFive_quotient_card Q split hm i j hij hi2 hj4
    change (middleFive Q split i j).relIndex (simpleRemainder Q split i) = 16 at hq
    have hh := relIndex_mul_relIndex (middleFive Q split i j)
      (middleRootCentralizer Q split i j) (simpleRemainder Q split i) hJC inf_le_left
    rw [h16,hq] at hh
    have he : (middleFive Q split i j).relIndex (middleRootCentralizer Q split i j) = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp he) hJC

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
