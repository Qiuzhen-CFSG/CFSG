module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairQuadraticDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicCentralitySource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicNormalizerExclusion

/-!
# The degree-one exclusion for the original two-linear octagon

The middle odd root is central in the whole radical. Its three fixed
root conjugates therefore centralize the five middle roots. The center
and fixed-normalizer argument forces those five roots to be abelian,
contradicting the nonzero perpendicular even-root commutator.

This proves the complete a = 1 branch of Fong--Seitz I (6G), printed p.50,
from the original factor quotient markings. It also excludes a binary
endpoint against any positive-degree linear endpoint and forces both
linear degrees to exceed one. Both orientations, the full Borel and
both endpoint maps are retained. The a > 1 branch of (6G) remains open.
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
/-- The original PSL₂(2), PSL₂(4) octagon is impossible. All root and
normalizer inputs are constructed from the original marked pair. -/
theorem original_linear_degree_one_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) : False := by
  have hmid := original_linear_degree_one_middle_central Q e h split hm i j hij hi hj
  have hne := original_linear_degree_one_root_perpendicular_nontrivial Q e h split hm i j hij hi hj
  obtain ⟨c,hc3,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
  obtain ⟨hKi,hci,⟨νi⟩⟩ := original_linear_marking Q e h split i μ
  obtain ⟨E,hE,hfinE,hcardE,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hcardE])
  obtain ⟨hKj,_,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  exact separated_binary_normalizer_exclusion Q split hm i j hij hKi hKj νi νj
    (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hcard (hci.trans hcard) c hc3 hc hne (hmid.trans inf_le_right)

include e h split in
/-- A binary endpoint cannot occur against any positive-degree linear
endpoint: the actual source degree relation forces the excluded pair. -/
theorem original_linear_binary_endpoint_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {b : ℕ} (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) : False := by
  have hi' : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^1) := by
    simpa only [pow_one] using hi
  rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij
    (a := 1) (by decide) hb hi' hj with ⟨_,hdeg⟩ | ⟨_,hdeg⟩
  · have hb2 : b = 2 := by omega
    subst b
    exact original_linear_degree_one_false Q e h split hm i j hij hi hj
  · omega

include e h split in
/-- After the degree-one exclusion, both original linear degrees exceed one. -/
theorem original_linear_pair_degrees_gt_one
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    1 < a ∧ 1 < b := by
  constructor
  · by_contra hle
    have ha1 : a = 1 := by omega
    subst a
    exact original_linear_binary_endpoint_false Q e h split hm i j hij hb
      (by simpa only [pow_one] using hi) hj
  · by_contra hle
    have hb1 : b = 1 := by omega
    subst b
    exact original_linear_binary_endpoint_false Q e h split hm j i hij.symm ha
      (by simpa only [pow_one] using hj) hi

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
