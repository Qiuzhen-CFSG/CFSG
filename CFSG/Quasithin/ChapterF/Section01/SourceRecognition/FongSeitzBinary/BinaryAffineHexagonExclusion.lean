module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineFrattiniExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffinePerfectExclusion

/-!
# Hexagon regularity for every original rank-one factor

The two-layer Frattini argument excludes an affine endpoint opposite every
root of order at most eight. This includes the binary linear and unitary
models, Sz(2), and the truncated dihedral factor. For a larger linear
factor, the regular whole-root cover constructs the local PSL2 equivalence
without perfectness of the original factor. The established Cartan
arguments handle the larger linear, Suzuki and unitary models.

Exhausting the original F.1.1 catalogue now gives (2B) at both endpoints of
the same marked split hexagon, with no perfectness premise. The remainder
preimages are the literal original two-cores. The unitary consumer then
constructs its surjective SU3 cover and projective square at every positive
degree, including two nonperfect endpoints. The full Borel and both
endpoint squares are those of the original amalgam marking throughout.

Source: Fong--Seitz I (5I), pp.31--35, especially the two successive
Frattini actions on p.34; AS F.1.1--3; DGS Theorem D, p.224. The genuine
marked quotient, split data and rotation order six remain earlier source
inputs. Other Weyl orders, minimality and exhaustive seven-row marked
recognition remain with source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- A nonbinary original linear quotient excludes the opposite affine hexagon without original perfectness. -/
theorem binary_affine_hexagon_false_of_linear_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    have hTcard : Nat.card (quotientSylow T) = Nat.card F :=
      (Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
        ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
          (linearModelSylow i T μ)).symm.toEquiv).trans
            (Nat.card_congr Multiplicative.toAdd))
    exact (simpleRoot_card_linear Q e h split i T hT μ).trans hTcard.symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at he
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at he
    exact μ.injective (he.trans μ.map_one.symm)
  let a := (regularFactorLocalEquiv Q e h split i T hT hV hc hz).trans μ
  exact no_affine_hexagon_of_linear Q split hF hm i j hij hV a
    (UnitarySource.actorReflection Q split i) hx.1 hx.2.1 hx.2.2.1

include e h in
/-- The entire original endpoint catalogue excludes an opposite affine hexagon, including every nonperfect parameter. -/
theorem binary_affine_hexagon_false
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hsmall (hc : Nat.card (simpleRoot Q split i) ≤ 8) : False :=
    no_affine_hexagon_of_small_opposite Q split hm i j hij hc hx.1 hx.2.1 hx.2.2.1
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    by_cases hF2 : 2 < Nat.card F
    · exact binary_affine_hexagon_false_of_linear_quotient Q e h split hF2 hm i j hij μ hx
    · apply hsmall
      rw [simpleRoot_card_linear Q e h split i T hT μ]
      omega
  | suzuki m hmodel =>
    by_cases hm0 : 0 < m
    · exact binary_affine_hexagon_false_of_suzuki Q e h split hm i j hij hm0 hmodel.some hx
    · have he : m = 0 := by omega
      subst m
      apply hsmall
      rw [suzuki_simpleRoot_card Q e h split i T hT hmodel.some]
      decide
  | projective_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact binary_affine_hexagon_false_of_unitary Q e h split J hn2 hcard hconj hm i j hij
        (Or.inr ⟨μ⟩) hx
    · have he : n = 1 := by omega
      subst n
      apply hsmall
      rw [projectiveUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ]
      decide
  | special_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact binary_affine_hexagon_false_of_unitary Q e h split J hn2 hcard hconj hm i j hij
        (Or.inl ⟨μ⟩) hx
    · have he : n = 1 := by omega
      subst n
      apply hsmall
      rw [specialUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ]
      decide
  | dihedral hmodel =>
    apply hsmall
    rw [dihedral_simpleRoot_card Q e h split i T hT hmodel.some]
    decide

include e h in
/-- Both original remainder preimages are exactly their two-cores on every marked split hexagon. -/
theorem marked_hexagon_regularity (hm : rotationOrder Q = 6) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  intro j
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
  · exact hr
  · exact (binary_affine_hexagon_false Q e h split hm (1-j) j (by fin_cases j <;> decide) hx).elim

include e h in
/-- The actual unitary root cover and its projective square, with both original core identifications and no perfectness premise. -/
theorem marked_hexagon_unitary_cover
    (hm : rotationOrder Q = 6) (j : Fin 2)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (endpointMap Q e k) = pCore 2 (parabolic L S k)) ∧
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split j,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a := by
  have hr := marked_hexagon_regularity Q e h split hm
  exact ⟨hr,regular_unitary_cover_of_factor Q e h split J hn hc hconj j (hr j).1 hfactor⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
