module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicMiddleSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleSection

/-!
# Middle-root quotients from the original degree-one factors

The original PSL₂(2), PSL₂(4) markings supply elementary roots and the
separating cubic. The five-root quotient is elementary abelian of order
sixteen. The actual middle-root centralizer is normalized by the entire
marked parabolic; its radical quotient is elementary abelian of order
one, four or sixteen. Every normality assertion is relative to its literal
radical, and both endpoint maps and the full Borel remain in the marking.

Source: Fong--Seitz I (1973), (6G), printed p.50, first paragraph. These
results supply the quotient and invariance inputs. Eliminating orders
four and sixteen, and the subsequent normalizer contradiction, remain.
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
private theorem original_root_data (i : Fin 2) (a : ℕ)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nat.card (simpleRoot Q split i) = 2^a ∧
      IsElementaryAbelian 2 (simpleRoot Q split i) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
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
  let ν := (regularFactorLocalEquiv Q e h split i T hT hK hc hz).trans μ
  exact ⟨hK,(simpleRoot_card_linear Q e h split i T hT μ).trans hcard,
    simpleRoot_elementary_of_linear Q split i ν⟩

include e h split in
/-- The literal five-root quotient at the original degree-one pair is an
elementary abelian group of order sixteen, with its relative normality proved. -/
theorem original_linear_degree_one_middle_quotient
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    ∃ hn : ((middleFive Q split i j).subgroupOf (simpleRemainder Q split i)).Normal,
      letI := hn
      IsElementaryAbelian 2 ((simpleRemainder Q split i) ⧸
        (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)) ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)) = 16 := by
  obtain ⟨_,hci,_⟩ := original_root_data Q e h split i 1 hi
  obtain ⟨hKj,hcj,hEj⟩ := original_root_data Q e h split j 2 hj
  norm_num at hci hcj
  let hn : ((middleFive Q split i j).subgroupOf (simpleRemainder Q split i)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (middleFive_normalized_by_remainder Q split hm i j hij hKj)
  refine ⟨hn,?_⟩
  let := hn
  exact ⟨middleFive_overgroup_quotient_elementary Q split hm i j hij hKj hEj _ le_rfl,
    binary_middleFive_quotient_card Q split hm i j hij hci hcj⟩

include e h split in
/-- The actual middle-root centralizer is parabolic-invariant. Its radical
quotient is elementary abelian and has order 1, 4 or 16. All cubic and
perpendicular-root inputs are derived from the original two factor markings. -/
theorem original_linear_degree_one_centralizer_quotient
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (middleRootCentralizer Q split i j : Set (X ⧸ Q.D)) ∧
    ∃ hn : ((middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)).Normal,
      letI := hn
      IsElementaryAbelian 2 ((simpleRemainder Q split i) ⧸
        (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) ∧
      (Nat.card ((simpleRemainder Q split i) ⧸
        (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) = 1 ∨
       Nat.card ((simpleRemainder Q split i) ⧸
        (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) = 4 ∨
       Nat.card ((simpleRemainder Q split i) ⧸
        (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) = 16) := by
  obtain ⟨hKi,hci,_⟩ := original_root_data Q e h split i 1 hi
  obtain ⟨hKj,hcj,hEj⟩ := original_root_data Q e h split j 2 hj
  norm_num at hci hcj
  let := hEj
  have hA : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  obtain ⟨c,horder,hc,_,_,hperp,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  have hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j :=
    le_inf (middleFive_le_remainder Q split hm i j hij)
      (separated_middleFive_centralizes Q split hm i j hij hKi hKj hci c hc)
  have hPC := middleRootCentralizer_parabolic_normalizes Q split hm i j hij
    hKi hKj hA (UnitarySource.actorReflection Q split i) hJC hperp
  let hn : ((middleRootCentralizer Q split i j).subgroupOf
      (simpleRemainder Q split i)).Normal := normal_subgroupOf_of_le_normalizer
    ((show simpleRemainder Q split i ≤ Q.tits.standardParabolic {Q.simple i} from
      inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans hPC)
  refine ⟨hPC,hn,?_⟩
  let := hn
  exact ⟨middleFive_overgroup_quotient_elementary Q split hm i j hij hKj hEj _ hJC,
    separated_binary_middleRootCentralizer_index Q split hm i j hij hci hcj c horder hc hJC
      (hPC (Q.tits.B_le_standardParabolic _ c.property.1))⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
