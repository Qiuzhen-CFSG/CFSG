module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCubicRadical

/-!
# Original quadratic unitary factors and their derived radical

The actual original PSL2 and SU3/PSU3 markings supply regularity, both
root orders, the full special-unitary cover and the nonabelian unitary
root. The already proved quadratic field ratio then gives the five-root
containment and order bound 2^(13b) for the same derived radical. A
crossed-root commutator proves that the actual rank-one actor moves it;
its first Frattini quotient has order at least 2^(6b), including b = 1.

Each factor of the previously constructed cubic radical centralizer is
a root commutator. Consequently its intersection with the derived radical
is the whole fixed group, which remains abelian. Both orientations,
special/projective scalar kernels, the full Borel and both original
endpoint inclusion squares are retained without extra source premises.

Source: Fong--Seitz I (6F), printed p.47. The projective-section bound
2^(8b), exclusion of the intervening subgroup of order 2^(9b), and
persistence through the lower central series remain required.
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

/-- The derived radical in the original (6F) quadratic branch:
its five-root containment, order bound, moved unitary action and first
Frattini-layer bound, together with the unchanged abelian cubic fixed
group, including degree one and both scalar conventions. -/
theorem original_linear_unitary_derived_bounds
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let V := simpleRemainder Q split j
    let D := ⁅V,V⁆
    D ≤ middleFive Q split j i ∧ Nat.card D ≤ 2^(13*b) ∧
      ⁅rankOne Q split j,D⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (D ⧸ frattini D) ∧
      D ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
        V ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ∧
      IsMulCommutative ↥(D ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have habelian := original_linear_unitary_cubic_radical_abelian Q e h split hm i j hij ha hb hi hj
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
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
  have hlin := simpleRoot_commutator_eq_bot_of_linear Q split i μi
  have hri : Nat.card (simpleRoot Q split i)=2^(2*b) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi μ,hEcard,hab]
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x, J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      let V := simpleRemainder Q split j
      let D := ⁅V,V⁆
      D ≤ middleFive Q split j i ∧ Nat.card D ≤ 2^(13*b) ∧
        ⁅rankOne Q split j,D⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (D ⧸ frattini D) ∧
        D ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
          V ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ∧
        IsMulCommutative ↥(D ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
    obtain ⟨μj,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j (hregular j).1 hmodel.symm
    have hroot : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
    obtain ⟨hsupp,hupper⟩ := unitary_derived_card_le Q split hm i j hij (hregular i).1 hlin hri hroot
    have hne := unitary_root_commutator_ne_bot Q split J hb hcard hconj j (hregular j).1 μj
    have hlower : 2^(6*b) ≤ Nat.card ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup (X ⧸ Q.D)) ⧸ frattini (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
          Subgroup (X ⧸ Q.D))) := by
      apply unitary_derived_frattini_card_ge Q split J hb hcard hconj hm i j hij
        (hregular j).1 μj σ hσ hroot
      intro _
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · have hcj := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
          J hb hcard hconj ν
        exact Or.inr ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
      · have hcj := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
          J hb hcard hconj ν
        exact Or.inl ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
    have hcentralizer := unitary_derived_threeCore_fixed Q split hm i j hij
      (fun w => (hfixed w).1) (fun w => (hfixed w).2.1)
      (unitary_rootFrattini_eq_commutator Q split J hb hcard hconj j (hregular j).1 μj)
    refine ⟨hsupp,hupper,unitary_derived_not_centralized Q split hm i j hij (hregular j).1 hne,
      hlower,hcentralizer,?_⟩
    rw [hcentralizer]
    exact habelian
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,ν⟩ | ⟨F,hF,hfin,J,hcard,hconj,ν⟩
  · exact applyModel J hcard hconj (Or.inl ν)
  · exact applyModel J hcard hconj (Or.inr ν)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
