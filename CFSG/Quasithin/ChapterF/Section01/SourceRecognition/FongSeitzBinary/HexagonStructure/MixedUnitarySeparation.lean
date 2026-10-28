module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MixedUnitarySeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction

/-!
# Exact mixed linear–unitary parameters on the original marked hexagon

The original regular factor markings supply the faithful PSL₂ and PSU₃
local actions and the actual SU₃ cover of the unitary rank-one group.
The separating-prime centralizer argument excludes a > 2n. Together with
the two-layer lower bound this forces a = 2n; the original square profile
then forces n even. Both original unitary scalar conventions are retained,
without an original-factor perfectness assumption.

Source: Fong–Seitz I (6D), printed p.43. The remaining equality-case
contradiction is a separate source obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

include e h split hn hcard hconj in
private theorem regular_unitary_separation_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nonempty (localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∧
      ∃ σ : J.specialSubgroup →* rankOne Q split j, Function.Surjective σ := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    exact ⟨hK,⟨projectiveUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩,
      a.symm.toMonoidHom.comp J.specialToProjective,
      a.symm.surjective.comp J.specialToProjective_surjective⟩
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    exact ⟨hK,⟨specialUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩,a.symm.toMonoidHom,a.symm.surjective⟩

include e h split hn hcard hconj in
/-- The strict mixed branch is impossible for either original unitary scalar convention. -/
theorem original_mixed_unitary_no_larger_linear_field
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (ha : 2*n < a) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hKi := linear_remainder_le_kernel Q e h split i T hT μi
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μi]
    exact ((Nat.card_congr (linearSylowEquiv i T μi).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μi)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μi hz
    change μi z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μi.injective (hh.trans μi.map_one.symm)
  let μlocal := (regularFactorLocalEquiv Q e h split i T hT hKi hc hz).trans μi
  obtain ⟨hKj,⟨ν⟩,σ,hσ⟩ := regular_unitary_separation_inputs Q e h split J hn hcard hconj j hmodel
  exact mixed_unitary_no_larger_linear_field Q split J hn hcard hconj hhex i j hij
    hKi hKj μlocal ν σ hσ hE ha

include e h split hn hcard hconj in
/-- Under the original square profile only the even equality parameter remains. -/
theorem original_mixed_linear_unitary_parameter_eq
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    a = 2*n ∧ n%2 = 0 := by
  have hb := original_mixed_linear_unitary_parameter_bounds Q e h split J hn hcard hconj
    hhex i j hij μi hE hmodel hsquare
  have hle : a ≤ 2*n := by
    by_contra! hlt
    exact original_mixed_unitary_no_larger_linear_field Q e h split J hn hcard hconj
      hhex i j hij μi hE hmodel hlt
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
