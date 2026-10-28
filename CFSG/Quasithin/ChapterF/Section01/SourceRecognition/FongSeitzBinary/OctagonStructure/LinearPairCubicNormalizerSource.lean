module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicDichotomySource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleAbelian

/-!
# Normalizer control at the original cubic pair

The original linear quotient markings construct the separating cubic and
its abelian three-root fixed subgroup. Coprime decomposition identifies
that subgroup's normalizer and centralizer in the full panel radical.
This holds in every odd-degree orientation. In degree one, if the
middle-root centralizer is proper, the orbit and cardinality argument
identifies the fixed-subgroup normalizer and centralizer with exactly the
five roots. The large central normal closure and Cartan irreducibility
then force this five-root subgroup to be abelian.

Source: Fong--Seitz I (6G), printed p.50, normalizer argument. This removes
a normalizer-control obligation without asserting the outstanding
proper-centralizer exclusion. The same marked quotient, full Borel and
both endpoint inclusion squares are retained.
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
/-- The source three-root fixed subgroup has identical relative normalizer
and centralizer, for every odd-degree linear orientation. -/
theorem original_oriented_linear_fixed_normalizer
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      simpleRemainder Q split i ⊓ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) := by
  obtain ⟨c,hc3,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij ha hb heb hi hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨hKi,hci,⟨ν⟩⟩ := original_linear_marking Q e h split i μ
  exact separated_fixedOddRoots_normalizer Q split hm i j hij hKi ν
    (UnitarySource.actorReflection Q split i) ha.pos hcard (hci.trans hcard) c hc3 hc

include e h split in
/-- In the unresolved index-sixteen branch, the fixed subgroup's normalizer
and centralizer are exactly the five-root subgroup. -/
theorem original_linear_degree_one_proper_fixed_normalizer
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4)
    (hproper : middleRootCentralizer Q split i j ≠ simpleRemainder Q split i) :
    (simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      middleFive Q split i j) ∧
    (simpleRemainder Q split i ⊓ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      middleFive Q split i j) := by
  have hCJ := (original_linear_degree_one_centralizer_dichotomy
    Q e h split hm i j hij hi hj).resolve_left hproper
  obtain ⟨c,hc3,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
  obtain ⟨hKi,hci,⟨ν⟩⟩ := original_linear_marking Q e h split i μ
  obtain ⟨E,hE,hfinE,hcardE,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hcardE])
  obtain ⟨hKj,hcj,_⟩ := original_linear_marking Q e h split j μj
  have hN := separated_binary_fixedOddRoots_normalizer Q split hm i j hij hKi hKj ν
    (UnitarySource.actorReflection Q split i) hcard (hci.trans hcard) (hcj.trans hcardE) c hc3 hc hCJ
  have hNC := separated_fixedOddRoots_normalizer Q split hm i j hij hKi ν
    (UnitarySource.actorReflection Q split i) (a := 1) (by decide) hcard (hci.trans hcard) c hc3 hc
  exact ⟨hN,hNC.symm.trans hN⟩

include e h split in
/-- The remaining proper-centralizer branch has an abelian five-root
subgroup, derived from the literal normal closure and Cartan actions. -/
theorem original_linear_degree_one_proper_middle_abelian
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4)
    (hproper : middleRootCentralizer Q split i j ≠ simpleRemainder Q split i) :
    IsMulCommutative (middleFive Q split i j) := by
  have hCJ := (original_linear_degree_one_centralizer_dichotomy
    Q e h split hm i j hij hi hj).resolve_left hproper
  have hC := (original_linear_degree_one_proper_fixed_normalizer
    Q e h split hm i j hij hi hj hproper).2
  have hJM : middleFive Q split i j ≤ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) := by
    rw [←hC]
    exact inf_le_right
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
  obtain ⟨_,hci,_⟩ := original_linear_marking Q e h split i μ
  obtain ⟨E,hE,hfinE,hcardE,⟨μj⟩⟩ := hj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (f := 2) (by norm_num only [←Nat.card_eq_fintype_card,hcardE])
  obtain ⟨hKj,hcj,⟨νj⟩⟩ := original_linear_marking Q e h split j μj
  exact binary_middleFive_abelian_of_fixed_centralizer Q split hm i j hij hKj νj
    (hci.trans hcard) (hcj.trans hcardE) hCJ hJM

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
