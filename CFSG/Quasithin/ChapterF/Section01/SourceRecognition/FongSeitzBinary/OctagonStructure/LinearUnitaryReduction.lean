module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryParity
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryCenter

/-!
# The original linear/unitary octagon degree reduction

The original factors supply the full linear panel marking and the regular
unitary root actor, with either special or projective scalar convention.
The already proved parity makes the unitary degree odd. Its center torus
therefore embeds in the opposite linear Cartan, so 2^b-1 divides 2^a-1.
Together with the original polygon bounds this leaves precisely the ratios
two, four and six, without an original-factor perfectness assumption.

Source: Fong--Seitz I (1J)--(1K), (6F), pp.6--7,45--46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The actual unitary center field-unit order divides the opposite linear order. -/
theorem original_linear_unitary_center_divisibility
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    2^b-1 ∣ 2^a-1 := by
  by_cases hb1 : b=1
  · simp only [hb1,pow_one,Nat.reduceSub,one_dvd]
  have hb2 : 2 ≤ b := by omega
  have hob := (original_linear_unitary_parity Q e h split hm i j hij ha hb hi hj).2
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨μi⟩ : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* PSL2BinaryMatrixGroup a) := by
    obtain ⟨F, hF, hfin, hcard, ⟨μ⟩⟩ := hi
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 a) := Fintype.ofFinite _
    let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using
        hcard.trans (GaloisField.card 2 a ha.ne').symm)
    exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩
  obtain ⟨σi,Ti,νi,hBi,_,_,_,_⟩ := LinearPanel.original_panel Q e h split i μi
  have hci := linear_cartanImage_card Q split i a ha σi Ti hBi (UnitarySource.actorReflection Q split i)
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x : F, J.conj x=x^(2^b))
      (hK : simpleRemainder Q split j ≤ localKernel Q j)
      (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
      (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (hmodel : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
        Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
      2^b-1 ∣ 2^a-1 := by
    have hd := Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.unitary_center_dvd_opposite
      Q split J hb2 hob hcard hconj hm i j hij hK hroot μ hmodel
    rwa [hci] at hd
  rcases hj with hj | hj
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hj
    have hK := projectiveUnitary_remainder_le_kernel Q e h split j Tj hTj J hb2 hcard hconj μj
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj J hb hcard hconj μj
    exact applyModel J hcard hconj hK
      (projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μj)
      (projectiveUnitaryFactorLocalEquiv Q e h split j Tj hTj J hb hcard hconj hK μj)
      (Or.inr ⟨(regularFactorRootEquiv Q e h split j Tj hTj hK hc).trans μj⟩)
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hj
    have hK := specialUnitary_remainder_le_kernel Q e h split j Tj hTj J hb2 hcard hconj μj
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj J hb hcard hconj μj
    exact applyModel J hcard hconj hK
      (specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μj)
      (specialUnitaryFactorLocalEquiv Q e h split j Tj hTj J hb hcard hconj hK μj)
      (Or.inl ⟨(regularFactorRootEquiv Q e h split j Tj hTj hK hc).trans μj⟩)

/-- The original linear/unitary octagon has even linear degree, odd unitary degree,
and degree ratio two, four or six. All Cartan divisibility premises are discharged. -/
theorem original_linear_unitary_degrees
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    Even a ∧ Odd b ∧ (a=2*b ∨ a=4*b ∨ a=6*b) :=
  original_linear_unitary_degrees_of_center_divisibility Q e h split hm i j hij ha hb hi hj
    (original_linear_unitary_center_divisibility Q e h split hm i j hij ha hb hi hj)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
