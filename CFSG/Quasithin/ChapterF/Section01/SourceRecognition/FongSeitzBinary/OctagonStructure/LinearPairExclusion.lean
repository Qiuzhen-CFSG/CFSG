module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairNonbinaryMixed
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.NonbinaryTerminal

/-!
# Exclusion of two original linear endpoints in an octagon

The quadratic-degree selection chooses the odd/even orientation. The
complete degree-one exclusion and higher-degree root argument provide
the strict derived bound, vanishing mixed commutator and central middle
pair. The pair is not invariant under the larger rank-one group. Its
escaping commutator and the original cubic actor force every middle root
into the derived radical, contradicting that strict bound.

Source: Fong--Seitz I (6G), printed pp.49--51, ending at the top of p.51.
The result applies to both orientations and every positive linear degree,
retaining the actual marked quotient, full Borel and both endpoint maps.
No recognition result or final-exclusion callback is assumed.
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
/-- The original odd/even orientation is impossible, with all root,
representation and Cartan premises discharged at the same quotient. -/
theorem original_oriented_linear_pair_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) : False := by
  obtain ⟨hbound,hzero,hcentral,hN⟩ := original_oriented_linear_mixed_commutator
    Q e h split hm i j hij ha hb heb hi hj
  have hlong := (original_oriented_linear_long_commutator Q e h split hm i j hij ha hb heb hi hj).2
  obtain ⟨c,_,hc,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij ha hb heb hi hj
  obtain ⟨E,hE,hEfin,hEc,⟨μi⟩⟩ := hi
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEc)
  obtain ⟨F,hF,hFfin,hFc,⟨μj⟩⟩ := hj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hFc)
  obtain ⟨hKi,_⟩ := original_linear_marking Q e h split i μi
  obtain ⟨hKj,_,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  exact nonbinary_linear_terminal_false Q split hm i j hij hKi hKj νj c hc
    hlong hzero hcentral (middle_pair_commutator_not_le Q split i j hzero hN) hbound

include e h split in
/-- Fong--Seitz (6G) for the actual original pair: an octagon cannot have
two linear factors. Both orientations and binary endpoints are included. -/
theorem original_linear_pair_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) : False := by
  rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij ha hb hi hj with
    ⟨hoa,hbval⟩ | ⟨hob,haval⟩
  · exact original_oriented_linear_pair_false Q e h split hm i j hij hoa hb
      (hbval ▸ even_two_mul a) hi hj
  · exact original_oriented_linear_pair_false Q e h split hm j i hij.symm hob ha
      (haval ▸ even_two_mul b) hj hi

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
