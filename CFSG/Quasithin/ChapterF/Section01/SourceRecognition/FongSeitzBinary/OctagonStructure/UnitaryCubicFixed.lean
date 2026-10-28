module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SmallSpecialUnitary

/-!
# Original unitary octagon factors and the cubic fixed roots

The original quotient markings give the faithful linear panel and the full
special or projective unitary actor, including the scalar cover at degree
one. The preceding degree reduction makes the linear degree twice the odd
unitary degree. On the same marked quotient, the nontrivial three-core of
the full Cartan then fixes exactly the unitary root Frattini subgroups (equal to their centers) and no
nonidentity points of any linear root. Both endpoint orientations and the
full Borel and original endpoint inclusion squares are retained.

Source: Fong--Seitz I (6F), printed pp.46--47. This supplies the actual
rootwise cubic centralizers; the radical centralizer and lower-central
series contradiction still have to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
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

/-- The actual original quadratic alternatives have the source cubic
fixed roots. Both scalar conventions and b=1 are included. -/
theorem original_linear_unitary_cubic_fixed_roots
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    cartanThreeCore Q ≠ ⊥ ∧ ∀ w : Weyl Q,
      (rootAt Q split i w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥) ∧
      rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
        (frattini (rootAt Q split j w)).map (rootAt Q split j w).subtype ∧
      frattini (rootAt Q split j w) = center (rootAt Q split j w) := by
  obtain ⟨hob,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨μ⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    have he := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 2 ≤ 2*b by omega)
    exact (by decide : 2 < 2^2).trans_le he
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i μ
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
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
  let μi := (regularFactorLocalEquiv Q e h split i Ti hTi (hregular i).1 hc hz).trans μ
  have hae : Even a := hab ▸ even_two_mul b
  obtain ⟨t,ht,_,hto⟩ := exists_linear_cubic_in_threeCore Q split hae hEcard i (hregular i).1 μi
  refine ⟨?_,?_⟩
  · intro he
    rw [he,mem_bot] at ht
    rw [ht,orderOf_one] at hto
    omega
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x, J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      ∀ w : Weyl Q,
        (rootAt Q split i w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥) ∧
        rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
          (frattini (rootAt Q split j w)).map (rootAt Q split j w).subtype ∧
      frattini (rootAt Q split j w) = center (rootAt Q split j w) := by
    obtain ⟨μj,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j (hregular j).1 hmodel.symm
    intro w
    have hphi := unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j (hregular j).1 μj w
    refine ⟨even_linear_threeCore_fixed_free Q split hae hEcard i (hregular i).1 μi w,?_,hphi⟩
    rw [hphi]
    have hroot : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
    by_cases hb1 : b=1
    · have hfull : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
          Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
        rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
        · have hcj := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
            J hb hcard hconj ν
          exact Or.inr ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
        · have hcj := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
            J hb hcard hconj ν
          exact Or.inl ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
      subst b
      exact small_unitary_threeCore_fixed_eq_center Q split J
        (by simpa [hab] using hEcard) (by simpa using hcard) (by simpa using hconj)
        hm i j hij (hregular i).1 (hregular j).1 μi μj hfull (by simpa using hroot) w
    · have hb2 : 2 ≤ b := by omega
      exact unitary_threeCore_fixed_eq_center Q split J hb2 hob (hab ▸ hEcard) hcard hconj
        hm i j hij (hregular i).1 (hregular j).1 μi μj σ hσ hroot
        (HexagonStructure.original_unitary_root_square_witness Q e h split J hb2 hcard hconj j hmodel) w
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,ν⟩ | ⟨F,hF,hfin,J,hcard,hconj,ν⟩
  · exact applyModel J hcard hconj (Or.inl ν)
  · exact applyModel J hcard hconj (Or.inr ν)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
