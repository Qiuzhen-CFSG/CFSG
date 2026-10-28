module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicExclusionSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.NonbinaryLongCommutator

/-!
# Higher-degree root separation for the original two-linear octagon

The degree-one exclusion puts the smaller linear factor in degree greater
than one. The original cubic actor and perpendicular rank-one product then
supply the full-Cartan kernel separation and exact two-root long commutator.
No root identity or field marking is added as a hypothesis. Both original
endpoint maps and the full Borel remain those of the supplied amalgam map.

Source: Fong--Seitz I (6G), printed p.50, “Now [U_1,U_1^{s_2}]”. The later
mixed-root containment and (4B) contradiction remain separate obligations.
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
/-- The actual odd/even linear pair supplies the first higher-degree (6G)
identity and the distinct Cartan kernels which force its two root factors. -/
theorem original_oriented_linear_long_commutator
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    (rootAction Q split i (Q.simple j*Q.simple i)).ker ≠
        (rootAction Q split i (Q.simple j*Q.simple i*Q.simple j)).ker ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
          rootAt Q split i (Q.simple j*Q.simple i) := by
  have ha1 := (original_linear_pair_degrees_gt_one Q e h split hm i j hij
    ha.pos hb hi hj).1
  obtain ⟨c,_,hc,_,_,hperp,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij ha hb heb hi hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨hK,_,⟨ν⟩⟩ := original_linear_marking Q e h split i μ
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^a from Nat.pow_lt_pow_right (by decide) ha1)
  exact ⟨separated_nonbinary_middle_kernels Q split hm i j hij hK ν hq hperp,
    separated_nonbinary_long_commutator Q split hm i j hij hK ν hq c hc hperp⟩

include e h split in
/-- The original quadratic-degree selection carries the precise long-root
identity in both orientations; no selected-row callback is assumed. -/
theorem original_linear_long_commutator_alternatives
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    (Odd a ∧ b = 2*a ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
          rootAt Q split i (Q.simple j*Q.simple i)) ∨
    (Odd b ∧ a = 2*b ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊔
          rootAt Q split j (Q.simple i*Q.simple j)) := by
  rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij ha hb hi hj with
    ⟨hoa,hbval⟩ | ⟨hob,haval⟩
  · exact Or.inl ⟨hoa,hbval,(original_oriented_linear_long_commutator Q e h split hm
      i j hij hoa hb (hbval ▸ even_two_mul a) hi hj).2⟩
  · exact Or.inr ⟨hob,haval,(original_oriented_linear_long_commutator Q e h split hm
      j i hij.symm hob ha (haval ▸ even_two_mul b) hj hi).2⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
