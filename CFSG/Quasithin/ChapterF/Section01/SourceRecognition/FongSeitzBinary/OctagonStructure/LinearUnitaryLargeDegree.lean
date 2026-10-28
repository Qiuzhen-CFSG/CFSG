module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitarySeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryLayers

/-!
# Excluding larger original linear degrees opposite a unitary octagon

The original linear quotient supplies the actual faithful root action.
The original special or projective unitary quotient supplies its regular
SU3 cover, root order and nontrivial root square. The separating-prime
fixed radical then has order 2^(9b), whereas its two moved Frattini layers
require order at least 2^(12b). Consequently a nonbinary unitary endpoint
has linear degree exactly twice its odd unitary degree.

Both orientations use the same marked quotient and full original amalgam
isomorphism, with no perfectness assumption on the original factors.
Source: Fong--Seitz I (6F), printed p.46. The degree-one unitary cases and
the remaining quadratic-degree contradiction are separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The strict larger-degree (6F) cases are impossible for the original
linear and nonbinary unitary factors, with either scalar convention. -/
theorem original_linear_unitary_large_degree_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (_ha : 0 < a) (hb : 2 ≤ b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (hlarge : 2*b < a) : False := by
  obtain ⟨E,hEfield,hEfin,hEcard,⟨μ⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hKi := linear_remainder_le_kernel Q e h split i Ti hTi μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow Ti) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi μ]
    exact ((Nat.card_congr (linearSylowEquiv i Ti μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i Ti μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  let μi := (regularFactorLocalEquiv Q e h split i Ti hTi hKi hc hz).trans μ
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F = (2^b)^2) (hconj : ∀ x, J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
    have hinputs : simpleRemainder Q split j ≤ localKernel Q j ∧
        Nat.card (simpleRoot Q split j) = (2^b)^3 := by
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · exact ⟨projectiveUnitary_remainder_le_kernel Q e h split j Tj hTj J hb hcard hconj ν,
          projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J (by omega) hcard hconj ν⟩
      · exact ⟨specialUnitary_remainder_le_kernel Q e h split j Tj hTj J hb hcard hconj ν,
          specialUnitary_simpleRoot_card Q e h split j Tj hTj J (by omega) hcard hconj ν⟩
    obtain ⟨μj,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J (by omega)
      hcard hconj j hinputs.1 hmodel.symm
    exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.octagon_mixed_unitary_no_larger_linear_field
      Q split J hb hcard hconj hm i j hij hKi hinputs.1 μi μj σ hσ hinputs.2
      (HexagonStructure.original_unitary_root_square_witness Q e h split J hb hcard hconj j hmodel)
      hEcard hlarge
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,ν⟩ | ⟨F,hF,hfin,J,hcard,hconj,ν⟩
  · exact applyModel J hcard hconj (Or.inl ν)
  · exact applyModel J hcard hconj (Or.inr ν)

/-- Only the quadratic field ratio survives at a nonbinary unitary
endpoint. The parity, divisibilities and strict-degree exclusions are proved. -/
theorem original_linear_unitary_quadratic_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 2 ≤ b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : Odd b ∧ a=2*b := by
  obtain ⟨_,hob,hcases⟩ := original_linear_unitary_degrees Q e h split hm i j hij ha (by omega) hi hj
  refine ⟨hob,?_⟩
  rcases hcases with he | he | he
  · exact he
  · exact (original_linear_unitary_large_degree_false Q e h split hm i j hij ha hb hi hj (by omega)).elim
  · exact (original_linear_unitary_large_degree_false Q e h split hm i j hij ha hb hi hj (by omega)).elim

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
