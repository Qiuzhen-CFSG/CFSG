module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicDichotomySource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleIrreducible

/-!
# The original degree-one five-root quotient action

At the original PSL₂(2), PSL₂(4) pair, every subgroup between the five
middle roots and the radical invariant under the rank-one actor and full
Cartan is an endpoint of that interval. If the middle-root centralizer is
proper, the exact centralizer dichotomy identifies it with the five roots.
This supplies their parabolic invariance and hence an actual irreducible
conjugation action on the elementary quotient of order sixteen.

Source: Fong--Seitz I (1973), (6G), printed p.50, first paragraph. Both
orientations and the full Borel and endpoint marking are retained. This
discharges the irreducibility premise in the remaining five-root case;
it does not yet exclude that case or prove terminal recognition.
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
/-- The literal order-sixteen quotient action in the proper-centralizer
branch, constructed from the original factors rather than assumed. -/
theorem original_linear_degree_one_proper_centralizer_action
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4)
    (hproper : middleRootCentralizer Q split i j ≠ simpleRemainder Q split i) :
    ∃ hn : ((middleFive Q split i j).subgroupOf (simpleRemainder Q split i)).Normal,
      letI := hn
      IsElementaryAbelian 2 ((simpleRemainder Q split i) ⧸
        (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)) ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)) = 16 ∧
      ∃ φ : (rankOne Q split i ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)) →*
          MulAut ((simpleRemainder Q split i) ⧸
            (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)),
        (∀ (r : (rankOne Q split i ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)))
          (v : simpleRemainder Q split i),
          ∃ w : simpleRemainder Q split i,
            (w : X ⧸ Q.D) = (r : X ⧸ Q.D)*(v : X ⧸ Q.D)*(r : X ⧸ Q.D)⁻¹ ∧
            φ r (QuotientGroup.mk v) = QuotientGroup.mk w) ∧
        ∀ D : Subgroup ((simpleRemainder Q split i) ⧸
            (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)),
          (∀ r, ∀ x ∈ D, φ r x ∈ D) → D = ⊥ ∨ D = ⊤ := by
  have hCJ := (original_linear_degree_one_centralizer_dichotomy
    Q e h split hm i j hij hi hj).resolve_left hproper
  have hPJ := (original_linear_degree_one_centralizer_quotient
    Q e h split hm i j hij hi hj).1
  rw [hCJ] at hPJ
  obtain ⟨c,horder,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  obtain ⟨hn,hE,hcard⟩ := original_linear_degree_one_middle_quotient
    Q e h split hm i j hij hi hj
  obtain ⟨F,hF,hfin,hFcard,⟨μi⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hFcard)
  obtain ⟨E,hEfield,hfinE,hEcard,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hEcard])
  obtain ⟨hKi,hci,_⟩ := original_linear_marking Q e h split i μi
  obtain ⟨hKj,hcj,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  obtain ⟨hn',hact⟩ := separated_binary_middleFive_quotient_action Q split hm i j hij
    hKi hKj νj (UnitarySource.actorReflection Q split i) (hci.trans hFcard)
      (hcj.trans hEcard) c horder hc hPJ
  exact ⟨hn',hE,hcard,hact⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
