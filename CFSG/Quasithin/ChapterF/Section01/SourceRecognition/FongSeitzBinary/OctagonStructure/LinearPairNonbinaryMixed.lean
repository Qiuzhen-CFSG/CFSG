module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairNonbinaryCommutator
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.NonbinaryMixedCommutator

/-!
# The original higher-degree mixed-root vanishing

The original linear factor markings supply both canonical local actions.
The larger factor's minimum binary degree makes its derived radical
strictly smaller than the five middle roots. The checked long commutator
then forces the mixed commutator to vanish: otherwise Cartan irreducibility
and reflections put every middle root in that derived radical.

Source: Fong--Seitz I (6G), printed p.50, the paragraph beginning
“We claim that”. Both orientations use the same quotient, full Borel and
original endpoint maps. The central pair is constructed and shown not to be invariant under the
larger rank-one group. The final commutator contradiction remains open.
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
/-- The exact (4B) obstruction and mixed-root vanishing on the original
odd/even linear pair. All local markings are constructed from the factors. -/
theorem original_oriented_linear_mixed_commutator
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleFive Q split j i ∧
      ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ ∧
      (rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) ≤
        centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) ∧
      ¬ rankOne Q split j ≤ normalizer
        ((rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set _) := by
  have hlong := (original_oriented_linear_long_commutator Q e h split hm i j hij ha hb heb hi hj).2
  have hb1 := (original_linear_pair_degrees_gt_one Q e h split hm i j hij ha.pos hb hi hj).2
  have hab : a < b := by
    rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij ha.pos hb hi hj with
      ⟨_,hval⟩ | ⟨hodd,_⟩
    · omega
    · obtain ⟨k,hk⟩ := hodd
      obtain ⟨l,hl⟩ := heb
      omega
  obtain ⟨E,hE,hEfin,hEc,⟨μi⟩⟩ := hi
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEc)
  obtain ⟨F,hF,hFfin,hFc,⟨μj⟩⟩ := hj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hFc)
  obtain ⟨hKi,hUi,⟨νi⟩⟩ := original_linear_marking Q e h split i μi
  obtain ⟨hKj,_,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  have hA := simpleRoot_commutator_eq_bot_of_linear Q split i νi
  have hsmall : Nat.card (simpleRoot Q split i) < Nat.card F := by
    rw [hUi,hEc,hFc]
    exact Nat.pow_lt_pow_right (by decide) hab
  have hbound := linear_radical_commutator_lt_middleFive Q split j hKj νj
    (UnitarySource.actorReflection Q split j) hm i hij hKi hA hb1 hFc hsmall
  have hmix := linear_mixed_commutator_eq_bot Q split j hKj νj
    (UnitarySource.actorReflection Q split j) hm i hij hKi hA hb1 hFc hsmall hlong
  obtain ⟨c,_,hc,_,_,hperp,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij ha hb heb
    ⟨E,hE,hEfin,hEc,⟨μi⟩⟩ ⟨F,hF,hFfin,hFc,⟨μj⟩⟩
  have hperproot : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ :=
    bot_unique ((commutator_mono le_sup_left (comap_mono
      (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left))).trans hperp.le)
  exact ⟨hbound,hmix,
    separated_middle_pair_centralizes Q split hm i j hij hKi hKj hA c hc hperproot hmix,
    linear_rankOne_not_normalizes_middlePair Q split hm i j hij hKj νj
      (UnitarySource.actorReflection Q split j) hb1 hFc hsmall
      (separated_middle_commutators Q split hm i j hij hKi c hc).2⟩


include e h split in
/-- Both source orientations have the strict derived bound and the actual
mixed-root vanishing, with no selected-row or commutator callback. -/
theorem original_linear_mixed_commutator_alternatives
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    (Odd a ∧ b = 2*a ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleFive Q split j i ∧
      ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ ∧
      (rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) ≤
        centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) ∧
      ¬ rankOne Q split j ≤ normalizer
        ((rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set _)) ∨
    (Odd b ∧ a = 2*b ∧
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ < middleFive Q split i j ∧
      ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ ∧
      (rootAt Q split j (Q.simple i*Q.simple j) ⊔
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)) ≤
        centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) ∧
      ¬ rankOne Q split i ≤ normalizer
        ((rootAt Q split j (Q.simple i*Q.simple j) ⊔
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Subgroup (X ⧸ Q.D)) : Set _)) := by
  rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij ha hb hi hj with
    ⟨hoa,hbval⟩ | ⟨hob,haval⟩
  · exact Or.inl ⟨hoa,hbval,original_oriented_linear_mixed_commutator Q e h split hm
      i j hij hoa hb (hbval ▸ even_two_mul a) hi hj⟩
  · exact Or.inr ⟨hob,haval,original_oriented_linear_mixed_commutator Q e h split hm
      j i hij.symm hob ha (haval ▸ even_two_mul b) hj hi⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
