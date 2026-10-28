module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedUnitarySeparation

/-!
# Excluding every mixed linear–regular unitary hexagon

If the linear degree a is smaller than 4n, the actual radical derived
subgroup lies in the three middle roots and has order at least 2^(6n).
Its central-coordinate product has order at most 2^(a+2n), so it escapes.
The literal commutator/reflection propagation then contradicts nilpotence.
The existing separating-prime argument excludes a > 2n. These two ranges
cover every parameter, including a = 2n, without using the square profile.

All canonical roots, local quotient markings, unitary covers, and Frattini
identities are constructed from the original factors. Both endpoint
orientations and special/projective unitary conventions are allowed;
no perfectness of either original factor is assumed. The separate degree-one
unitary exclusions retain their binary nonperfect cases.
Source: Fong--Seitz I (6D), printed p.43, using (3G), (4D), and (5D).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
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
  (hconj : ∀ x, J.conj x=x^(2^n))

include e h split hn hcard hconj in
private theorem mixed_unitary_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
  · exact specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ

include e h split in
private theorem mixed_linear_inputs
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (i : Fin 2) (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (localGroup Q split i ≃* PSL(2,E)) ∧
      Nat.card (simpleRoot Q split i) = Nat.card E := by
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
  exact ⟨hKi,⟨(regularFactorLocalEquiv Q e h split i T hT hKi hc hz).trans μi⟩,
    simpleRoot_card_linear Q e h split i T hT μi⟩

include e h split hn hcard hconj in
/-- The small-degree mixed branch has an actual derived escape, so propagation excludes it. -/
theorem original_mixed_unitary_small_degree_excluded
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (ha : a < 4*n) : False := by
  obtain ⟨hKi,⟨μ⟩,hci⟩ := mixed_linear_inputs Q e h split i μi
  have hKj := mixed_unitary_inputs Q e h split J hn hcard hconj j hj
  obtain ⟨_,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J (by omega) hcard hconj j hKj hj.symm
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  have hphi : frattini V = _root_.commutator V := by
    apply radical_frattini_eq_commutator_of_root_squares Q split hhex i j hij
    intro k
    by_cases hk : k=i
    · subst k
      let := simpleRoot_elementary_of_linear Q split i μ
      intro x
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _) x]
      exact one_mem _
    · have hk' : k=j := by omega
      subst k
      exact original_unitary_root_square_mem_commutator Q e h split J hn hcard hconj j hj
  have hD : 2^(6*n) ≤ Nat.card D := by
    have hb := unitary_frattini_radical_card_bound J hn hcard hconj Q split j σ hσ hhex i hij
      (UnitarySource.actorReflection Q split j) hKj
      (original_unitary_root_square_witness Q e h split J hn hcard hconj j hj)
    have hc : Nat.card (frattini V) = Nat.card D := by
      rw [hphi]
      change Nat.card (_root_.commutator V) = Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D))
      rw [←map_subtype_commutator]
      exact Nat.card_congr ((_root_.commutator V).equivMapOfInjective V.subtype V.subtype_injective).toEquiv
    exact (hb.trans (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective (frattini (frattini V))))).trans_eq hc
  have hsmall : Nat.card (middleCentralProduct Q split i j) < 2^(6*n) := by
    have hZ := original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j 1 hj
    have hcj : Nat.card (center (simpleRoot Q split j)) = 2^n := by
      have hz := hZ.1 ▸ hZ.2.1
      change Nat.card (center (rootAt Q split j 1)) = 2^n at hz
      rwa [rootAt_one] at hz
    have hb := middleCentralProduct_card_le Q split i j
    rw [hci,hE,hcj,←pow_mul,←pow_add] at hb
    exact hb.trans_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mpr (by omega))
  have hmid : D ≤ middleRoots Q split i j := radical_commutator_le_middle_of_linear Q split hhex i j hij hKi μ
  have hescape : ¬ ((D ⊓ middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
      middleCentralProduct Q split i j := by
    intro he
    have hi : (D : Set (X ⧸ Q.D)) ⊆ middleCentralProduct Q split i j := fun x hx => he ⟨hx,hmid hx⟩
    exact (not_le_of_gt hsmall) (hD.trans
      (Nat.card_le_card_of_injective (Set.inclusion hi) (Set.inclusion_injective hi)))
  have hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥ := by
    rw [simpleRoot_commutator_eq_bot_of_linear Q split i μ,commutator_bot_left]
  exact unitary_escape_contradiction Q split hhex i j hij
    (UnitarySource.actorReflection Q split j) hKi hKj hclass J hn hcard hconj σ hσ hsmall hescape

include e h split hn hcard hconj in
/-- No original linear–regular unitary pair occurs at rotation order six. -/
theorem original_mixed_linear_unitary_excluded
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  by_cases ha : a < 4*n
  · exact original_mixed_unitary_small_degree_excluded Q e h split J hn hcard hconj
      hhex i j hij μi hE hj ha
  · exact original_mixed_unitary_no_larger_linear_field Q e h split J hn hcard hconj
      hhex i j hij μi hE hj (by omega)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full mixed exclusion for the original source quotient; its Sylow
radical and both endpoint actions are the literal Q.q images. -/
theorem quotient_mixed_linear_unitary_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    {a : ℕ} (hE : Nat.card E = 2^a)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_mixed_linear_unitary_excluded Q (originalMarkedIso Q) h split
    J hn hcard hconj hhex i j hij μi hE hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
