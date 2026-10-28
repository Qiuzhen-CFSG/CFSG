module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicNormalizerSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleExclusion

/-!
# Whole-radical centrality at the original binary linear pair

The proper middle-root centralizer would make the five middle roots
abelian. The perpendicular-root contradiction excludes this alternative,
so the middle odd root is central in the entire original panel radical.
Both orientations use the same original factor quotients, full Borel,
and both endpoint inclusion squares.

Source: Fong--Seitz I (6G), printed p.50. This proves the whole-radical
centrality conclusion in its first paragraph; the subsequent normalizer
contradiction and higher-degree exclusion remain separate obligations.
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
/-- The index-sixteen alternative is impossible: the middle odd root's
centralizer is the entire radical, for either original endpoint orientation. -/
theorem original_linear_degree_one_middle_centralizer_eq
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    middleRootCentralizer Q split i j = simpleRemainder Q split i := by
  by_contra hproper
  have hab := original_linear_degree_one_proper_middle_abelian Q e h split hm i j hij hi hj hproper
  obtain ⟨c,hc3,hc,_,_,hfull,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  have hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
    apply bot_unique
    apply le_trans (commutator_mono
      (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)
      (comap_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)))
    exact hfull.le
  have hne := original_linear_degree_one_root_perpendicular_nontrivial Q e h split hm i j hij hi hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
  obtain ⟨hKi,hci,_⟩ := original_linear_marking Q e h split i μ
  obtain ⟨E,hE,hfinE,hcardE,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hcardE])
  obtain ⟨hKj,_,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  exact separated_binary_middleFive_not_abelian Q split hm i j hij hKi hKj νj
    (UnitarySource.actorReflection Q split i) (hci.trans hcard) c hc3 hc hperp hne hab

include e h split in
/-- The literal middle odd root lies in the center of the seven-root radical. -/
theorem original_linear_degree_one_middle_central
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      simpleRemainder Q split i ⊓ centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
  have hC := original_linear_degree_one_middle_centralizer_eq Q e h split hm i j hij hi hj
  have hcent : simpleRemainder Q split i ≤
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
    rw [←hC]
    exact inf_le_right
  exact le_inf ((show rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
    middleFive Q split i j from le_sup_of_le_left (le_sup_of_le_left le_sup_right)).trans
      (middleFive_le_remainder Q split hm i j hij)) (le_centralizer_iff.mp hcent)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
