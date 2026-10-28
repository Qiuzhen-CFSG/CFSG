module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicSectionSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleClosure

/-!
# The middle involution's normal closure at the original degree-one pair

The original PSL₂(2), PSL₂(4) factor markings construct an elementary
normal subgroup of the actual seven-root radical, invariant under the full
marked parabolic. It is the radical-normal closure of the middle root,
not an assumed representation. Its centralizer is exactly the previously
constructed middle-root centralizer. The corresponding elementary quotient
acts faithfully by the literal conjugation map, and the conjugacy orbit
gives strict lower bounds on the normal subgroup's order.

Source: Fong--Seitz I (1973), (6G), printed p.50. This supplies an actual
normal subgroup for the degree-one contradiction; that contradiction and
the full recognition theorem remain separate obligations. Both endpoint
orientations and the full Borel remain in the same original marking.
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
      Nat.card (simpleRoot Q split i) = 2^a := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact ⟨linear_remainder_le_kernel Q e h split i T hT μ,
    (simpleRoot_card_linear Q e h split i T hT μ).trans hcard⟩

include e h split in
/-- The actual middle-root normal closure is elementary, parabolic-invariant,
and central in the five middle roots. Its centralizer is exactly C_V(A). -/
theorem original_linear_degree_one_normal_closure
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    IsElementaryAbelian 2 (middleRootClosure Q split i j) ∧
    middleRootClosure Q split i j ≤ middleFive Q split i j ⊓
      centralizer (middleFive Q split i j : Set (X ⧸ Q.D)) ∧
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (middleRootClosure Q split i j : Set (X ⧸ Q.D)) ∧
    simpleRemainder Q split i ⊓
      centralizer (middleRootClosure Q split i j : Set (X ⧸ Q.D)) =
        middleRootCentralizer Q split i j := by
  obtain ⟨hKi,hci⟩ := original_root_data Q e h split i 1 hi
  obtain ⟨hKj,_⟩ := original_root_data Q e h split j 2 hj
  norm_num at hci
  have hJC := (original_linear_degree_one_middle_centralizer Q e h split hm i j hij hi hj).2.1
  obtain ⟨_,_,_,_,_,hperp,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  obtain ⟨_,hn,_⟩ := original_linear_degree_one_centralizer_quotient Q e h split hm i j hij hi hj
  exact ⟨binary_middleRootClosure_elementary Q split hm i j hij hKj hci hJC,
    middleRootClosure_le_middle_center Q split hm i j hij hKj hJC,
    middleRootClosure_parabolic_normalizes Q split i j hKi (UnitarySource.actorReflection Q split i) hperp,
    middleRootClosure_centralizer Q split hm i j hij
      ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn)⟩

include e h split in
/-- The source centralizer quotient embeds in the automorphism group of the
constructed elementary subgroup, with the original conjugation equation. -/
theorem original_linear_degree_one_normal_closure_action
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    ∃ hn : ((middleRootCentralizer Q split i j).subgroupOf
        (simpleRemainder Q split i)).Normal,
      letI := hn
      ∃ φ : ((simpleRemainder Q split i) ⧸
          (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) →*
            MulAut (middleRootClosure Q split i j),
        Function.Injective φ ∧
        ∀ (v : simpleRemainder Q split i) (z : middleRootClosure Q split i j),
          (φ (QuotientGroup.mk v) z : X ⧸ Q.D) =
            (v : X ⧸ Q.D)*(z : X ⧸ Q.D)*(v : X ⧸ Q.D)⁻¹ := by
  obtain ⟨_,hn,_⟩ := original_linear_degree_one_centralizer_quotient Q e h split hm i j hij hi hj
  exact ⟨hn,middleRootClosure_faithful_action Q split hm i j hij hn⟩

include e h split in
/-- The actual nonidentity conjugacy orbit bounds the elementary subgroup's
order, including the two still-open noncentral cases. -/
theorem original_linear_degree_one_normal_closure_card
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) <
      Nat.card (middleRootClosure Q split i j) ∧
    Nat.card (middleRootClosure Q split i j) ∣ 128 ∧
    ((middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 4 →
      8 ≤ Nat.card (middleRootClosure Q split i j)) ∧
    ((middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 16 →
      32 ≤ Nat.card (middleRootClosure Q split i j)) := by
  obtain ⟨_,hci⟩ := original_root_data Q e h split i 1 hi
  obtain ⟨hKj,hcj⟩ := original_root_data Q e h split j 2 hj
  norm_num at hci hcj
  have hJC := (original_linear_degree_one_middle_centralizer Q e h split hm i j hij hi hj).2.1
  exact ⟨binary_middleRootClosure_card_gt_index Q split hm i j hij hci,
    binary_middleRootClosure_card_bounds Q split hm i j hij hKj hci hcj hJC⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
