module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.EffectiveSections

/-!
# The two unitary layers on the original marked quotient

The regular original-factor cover identifies the canonical root actor with
the supplied SU₃ or PSU₃ quotient. The actual quotient-Sylow order makes
the canonical root a full Sylow, supplying its nontrivial square. In the
projective case the acting cover uses the literal scalar projection; in the
special case it keeps the full special group. No original-factor
perfectness premise is used, and the regular (2B) input is discharged.

The reflection therefore moves the Frattini subgroup of the original
Sylow radical. Both literal Frattini layers give |U_sj| ≥ 2^(12n), and
the opposite-root exponent is at least 2n. In particular, regular unitary
endpoints cannot face PSL₂(2), PSL₂(4), PSL₂(8), SU₃(2), PSU₃(2), Sz(2)
or the original dihedral constructor. Together with the retained mixed
centralizer proof this excludes every Suzuki parameter opposite a regular
unitary endpoint. Both initial mixed linear--unitary inequalities and the
source square-profile parity are also established. Original/geometric
markings and the literal Q.q map are retained. Two degree-one endpoints,
the remaining unitary parameters and the exhaustive dichotomy remain open.

Source: Fong--Seitz I (5D), (6D), printed pp.26--27,41--43.
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

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

include e h split hn hcard hconj in
private theorem regular_unitary_layer_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = (2^n)^3 ∧
      (∃ a : simpleRoot Q split j, a^2 ≠ 1) ∧
      ∃ σ : J.specialSubgroup →* rankOne Q split j, Function.Surjective σ := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    let T' := (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective
    let b : quotientSylow T ≃* T' :=
      (quotientSylow T : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
    refine ⟨hK,projectiveUnitary_simpleRoot_card Q e h split j T hT J
      (by omega) hcard hconj μ,?_,a.symm.toMonoidHom.comp J.specialToProjective,
        a.symm.surjective.comp J.specialToProjective_surjective⟩
    exact root_square_of_model_sylow Q split j a T' (hc.trans (Nat.card_congr b.toEquiv))
      (projective_unitary_sylow_square_witness J hn hcard hconj T')
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    let T' := (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective
    let b : quotientSylow T ≃* T' :=
      (quotientSylow T : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
    refine ⟨hK,specialUnitary_simpleRoot_card Q e h split j T hT J
      (by omega) hcard hconj μ,?_,a.symm.toMonoidHom,a.symm.surjective⟩
    exact root_square_of_model_sylow Q split j a T' (hc.trans (Nat.card_congr b.toEquiv))
      (special_unitary_sylow_square_witness J hn hcard hconj T')

include e h split hn hcard hconj in
/-- The original regular unitary model supplies a square in the SAME canonical root. -/
theorem original_unitary_root_square_witness (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ a : simpleRoot Q split j, a^2 ≠ 1 :=
  (regular_unitary_layer_inputs Q e h split J hn hcard hconj j hmodel).2.2.1

include e h split hn hcard hconj in
/-- Both unitary Frattini bounds on the literal original/geometric Sylow radical. -/
theorem original_unitary_radical_two_layers
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    2^(6*n) ≤ Nat.card (V ⧸ frattini V) ∧
      2^(6*n) ≤ Nat.card (frattini V ⧸ frattini (frattini V)) ∧
      2^(12*n) ≤ Nat.card V := by
  obtain ⟨hK,hroot,hsquare,σ,hσ⟩ := regular_unitary_layer_inputs Q e h split J hn hcard hconj j hmodel
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact ⟨unitary_radical_first_layer_card_bound J hn hcard hconj Q split j σ hσ
    hhex i hij (UnitarySource.actorReflection Q split j) hK,
    unitary_frattini_radical_card_bound J hn hcard hconj Q split j σ hσ
    hhex i hij (UnitarySource.actorReflection Q split j) hK hsquare,
    unitary_radical_two_layer_bound J hn hcard hconj Q split j σ hσ
    hhex i hij (UnitarySource.actorReflection Q split j) hK hsquare⟩

include e h split hn hcard hconj in
/-- The parameter bound comes from these same two source sections. -/
theorem original_unitary_hexagon_parameter_bound
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    {a : ℕ} (hopp : Nat.card (simpleRoot Q split i) = 2^a) : 2*n ≤ a := by
  obtain ⟨hK,hroot,hsquare,σ,hσ⟩ := regular_unitary_layer_inputs Q e h split J hn hcard hconj j hmodel
  exact unitary_hexagon_parameter_bound J hn hcard hconj Q split j σ hσ
    hhex i hij (UnitarySource.actorReflection Q split j) hK hsquare hroot hopp

include e h split hn hcard hconj in
/-- Regular unitary endpoints cannot face a linear field of order at most eight.
No perfectness assumption is imposed on the small linear endpoint. -/
theorem original_unitary_small_linear_exclusion
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E)) (hsmall : Nat.card E ≤ 8)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  obtain ⟨a,ha⟩ := (split.isTwo.to_le (simpleRoot_le Q split i)).exists_card_eq
  have hb := original_unitary_hexagon_parameter_bound Q e h split J hn hcard hconj hhex i j hij hmodel ha
  have hc := simpleRoot_card_linear Q e h split i T hT μi
  have hpow : 2^a ≤ 2^3 := by simpa only [←ha,hc,Nat.reducePow] using hsmall
  have hle := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  omega


include e h split hn hcard hconj in
/-- Initial mixed (6D) bounds and source (1J) parity, with the actual regular
covers and both section-action inputs discharged. -/
theorem original_mixed_linear_unitary_parameter_bounds
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    2*n ≤ a ∧ 2*a ≤ 9*n ∧ a%2 = n%2 := by
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
  obtain ⟨hKj,hroot,hsq,σ,hσ⟩ := regular_unitary_layer_inputs Q e h split J hn hcard hconj j hmodel
  have hb := mixed_linear_unitary_parameter_bounds Q split J hn hcard hconj hhex i j hij
    hKi hKj μlocal σ hσ (UnitarySource.actorReflection Q split i)
    (UnitarySource.actorReflection Q split j) hE hsq hroot
  refine ⟨hb.1,hb.2,mixed_unitary_square_profile_parity ?_⟩
  rwa [simpleRoot_card_linear Q e h split i T hT μi,hE,hroot] at hsquare

include e h split hn hcard hconj in
/-- The opposite unitary field is kept independent, including degree one. -/
theorem original_unitary_pair_parameter_bound
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {b : ℕ} (hb : 0 < b) (hE : Nat.card E = (2^b)^2)
    (hconjE : ∀ x, I.conj x = x^(2^b))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : 2*n ≤ 3*b := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hc : Nat.card (simpleRoot Q split i) = 2^(3*b) := by
    have hc' : Nat.card (simpleRoot Q split i) = (2^b)^3 := by
      rcases hi with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split i T hT I hb hE hconjE μ
      · exact specialUnitary_simpleRoot_card Q e h split i T hT I hb hE hconjE μ
    rw [hc',←pow_mul,Nat.mul_comm]
  exact original_unitary_hexagon_parameter_bound Q e h split J hn hcard hconj hhex i j hij hj hc

include e h split hn hcard hconj in
/-- A regular unitary endpoint excludes BOTH SU₃(2) and PSU₃(2) at the other
endpoint, without identifying their scalar covers with one another. -/
theorem original_unitary_degree_one_opposite_exclusion
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    (hE : Nat.card E = 4) (hconjE : ∀ x, I.conj x = x^2)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  have hb := original_unitary_pair_parameter_bound Q e h split J hn hcard hconj I
    (n := n) (b := 1) (by decide) (by simpa using hE) (by simpa using hconjE)
    hhex i j hij hi hj
  omega

include e h split hn hcard hconj in
/-- The small Suzuki original factor is excluded opposite any regular unitary
endpoint by the same literal two-layer bound. -/
theorem original_unitary_suzuki_zero_exclusion
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hc : Nat.card (simpleRoot Q split i) = 2^2 := by
    simpa using suzuki_simpleRoot_card Q e h split i T hT μi
  have hb := original_unitary_hexagon_parameter_bound Q e h split J hn hcard hconj hhex i j hij hj hc
  omega

include e h split hn hcard hconj in
/-- The original dihedral constructor has canonical root order four, rather
than the order-two Sylow of the original factor quotient. -/
theorem original_unitary_dihedral_exclusion
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hc : Nat.card (simpleRoot Q split i) = 2^2 :=
    dihedral_simpleRoot_card Q e h split i T hT μi
  have hb := original_unitary_hexagon_parameter_bound Q e h split J hn hcard hconj hhex i j hij hj hc
  omega

include e h split hn hcard hconj in
/-- The mixed unitary--Suzuki exclusion now includes every Suzuki parameter.
The positive branch uses the proved literal three-Cartan centralizer. -/
theorem original_regular_unitary_suzuki_exclusion
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact original_unitary_suzuki_zero_exclusion Q e h split J hn hcard hconj hhex i j hij μi hj
  · exact original_mixed_unitary_suzuki_exclusion Q e h split J (by omega) hcard hconj
      hhex j i hij.symm hj hm μi (by simpa only [mul_comm] using hsquare)


include e h split hcard hconj in
/-- The entire original unitary--Suzuki mixed branch, including Sz(2) and
both degree-one unitary covers. The source square profile supplies n ≥ 2. -/
theorem original_unitary_suzuki_all_parameters_exclusion (hnpos : 0 < n)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hroot : Nat.card (simpleRoot Q split j) = (2^n)^3 := by
    rcases hj with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hnpos hcard hconj μ
    · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hnpos hcard hconj μ
  have heven := unitary_even_of_suzuki_square_profile Q split j i hroot
    (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi) (by simpa only [mul_comm] using hsquare)
  have hn2 : 2 ≤ n := by have := Nat.even_iff.mp heven; omega
  exact original_regular_unitary_suzuki_exclusion Q e h split J hn2 hcard hconj
    hhex i j hij μi hj hsquare

include e h split hcard hconj in
/-- The full original dihedral--unitary branch, including degree one.
The root order is four, so (1J) forces the unitary degree to be even. -/
theorem original_unitary_dihedral_all_parameters_exclusion (hnpos : 0 < n)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hi : Nat.card (simpleRoot Q split i) = 2^2 := dihedral_simpleRoot_card Q e h split i Ti hTi μi
  have hroot : Nat.card (simpleRoot Q split j) = (2^n)^3 := by
    rcases hj with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hnpos hcard hconj μ
    · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hnpos hcard hconj μ
  rw [hi,hroot] at hsquare
  have hpar := mixed_unitary_square_profile_parity hsquare
  have hn2 : 2 ≤ n := by omega
  exact original_unitary_dihedral_exclusion Q e h split J hn2 hcard hconj hhex i j hij μi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Literal Q.q application of both Frattini-layer bounds, with both scalar models. -/
theorem quotient_unitary_radical_two_layers
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    2^(6*n) ≤ Nat.card (V ⧸ frattini V) ∧
      2^(6*n) ≤ Nat.card (frattini V ⧸ frattini (frattini V)) ∧
      2^(12*n) ≤ Nat.card V := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_radical_two_layers Q (originalMarkedIso Q) h split J hn hcard hconj
    hhex i j hij hmodel
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

/-- The original quotient-map exclusion of the three small linear fields. -/
theorem quotient_unitary_small_linear_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E)) (hsmall : Nat.card E ≤ 8)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_unitary_small_linear_exclusion Q (originalMarkedIso Q) h split J hn hcard hconj
    hhex i j hij μi hsmall hmodel


/-- The same mixed-field restrictions in the literal original quotient. -/
theorem quotient_mixed_linear_unitary_parameter_bounds
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    2*n ≤ a ∧ 2*a ≤ 9*n ∧ a%2 = n%2 :=
  original_mixed_linear_unitary_parameter_bounds Q (originalMarkedIso Q) h split J hn hcard hconj
    hhex i j hij μi hE hj hsquare

/-- Both degree-one unitary scalar alternatives are excluded opposite the
regular unitary endpoint of the original quotient. -/
theorem quotient_unitary_degree_one_opposite_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    (hE : Nat.card E = 4) (hconjE : ∀ x, I.conj x = x^2)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_unitary_degree_one_opposite_exclusion Q (originalMarkedIso Q) h split J hn hcard hconj
    I hE hconjE hhex i j hij hi hj

/-- The dihedral constructor is excluded using its actual degree-five panel. -/
theorem quotient_unitary_dihedral_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_unitary_dihedral_exclusion Q (originalMarkedIso Q) h split J hn hcard hconj
    hhex i j hij μi hj

/-- Every Suzuki parameter, including zero, is excluded opposite a regular
unitary endpoint in the same original quotient. -/
theorem quotient_regular_unitary_suzuki_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_regular_unitary_suzuki_exclusion Q (originalMarkedIso Q) h split J hn hcard hconj
    hhex i j hij μi hj hsquare


/-- The full unitary--Suzuki exclusion on the original finite quotient,
with all positive unitary degrees and all Suzuki parameters admitted. -/
theorem quotient_unitary_suzuki_all_parameters_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_unitary_suzuki_all_parameters_exclusion Q (originalMarkedIso Q) h split J hcard hconj hn
    hhex i j hij μi hj hsquare

/-- The degree-five original dihedral panel is retained in the full quotient
application; it is not replaced by the order-two original quotient Sylow. -/
theorem quotient_unitary_dihedral_all_parameters_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_unitary_dihedral_all_parameters_exclusion Q (originalMarkedIso Q) h split J hcard hconj hn
    hhex i j hij μi hj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
