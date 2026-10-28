module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryDegrees
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction

/-!
# The parity orientation of the original linear/unitary octagon

The original factor marking completes the linear endpoint and identifies
the regular unitary local action. An odd linear degree would make its
field-unit order divide the quadratic unitary field-unit order, hence make
the linear degree divide the unitary degree. This contradicts the lower
octagon bound. The square condition therefore leaves even linear degree
and odd unitary degree, including unitary degree one.

Source: Fong--Seitz I (1J)--(1K), (6F), pp.6--7,45--46. The remaining
unitary-to-linear degree divisibility is needed for the ratios two, four
and six; it is not asserted by this parity theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal ReeSource

private theorem binary_linear_marking {Y : Type*} [Group Y] {a : ℕ}
    (ha : 0 < a) (hlinear : ClassicalGroup.IsPSL Y 2 (2^a)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup a) := by
  obtain ⟨F, hF, hfin, hcard, ⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 a ha.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The original linear/unitary octagon has even linear degree and odd
unitary degree. No original-factor perfectness or extra torus hypothesis is used. -/
theorem original_linear_unitary_parity
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : Even a ∧ Odd b := by
  obtain ⟨hpar,hupper,hlower⟩ := original_linear_unitary_degree_bounds Q e h split hm i j hij ha hb hi hj
  apply linear_unitary_degree_parity_of_odd_divisibility hb hpar hlower
  intro hoa
  have hb2 : 2 ≤ b := by
    have hodd := Nat.odd_iff.mp hoa
    omega
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨μi⟩ := binary_linear_marking ha hi
  obtain ⟨σi,Ti,νi,hBi,_,_,_,_⟩ := LinearPanel.original_panel Q e h split i μi
  have hci : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [rootAt_one] using linear_rootAt_card Q split i a σi Ti hBi ha 1
  have hEi : IsElementaryAbelian 2 (simpleRoot Q split i) := by
    rw [←rootAt_one Q split i]
    exact linear_rootAt_elementary Q split i a σi Ti hBi 1
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F = (2^b)^2) (hconj : ∀ x : F, J.conj x = x^(2^b))
      (hKj : simpleRemainder Q split j ≤ localKernel Q j)
      (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
      2^a-1 ∣ 2^(2*b)-1 :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.linear_unitary_odd_cartan_dvd
      Q split J hb2 hcard hconj hm i j hij hoa σi Ti hBi hKj μj hEi hci
      (UnitarySource.actorReflection Q split) (LinearThreePresentation.borel_core_eq_bot Q e h)
  rcases hj with hj | hj
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hj
    have hKj := projectiveUnitary_remainder_le_kernel Q e h split j Tj hTj J hb2 hcard hconj μj
    exact applyModel J hcard hconj hKj
      (projectiveUnitaryFactorLocalEquiv Q e h split j Tj hTj J hb hcard hconj hKj μj)
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hj
    have hKj := specialUnitary_remainder_le_kernel Q e h split j Tj hTj J hb2 hcard hconj μj
    exact applyModel J hcard hconj hKj
      (specialUnitaryFactorLocalEquiv Q e h split j Tj hTj J hb hcard hconj hKj μj)

/-- The original parameter reduction now needs only the unitary-center
field-unit divisibility; the parity and opposite Cartan premises are discharged. -/
theorem original_linear_unitary_degrees_of_center_divisibility
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (hcenter : 2^b-1 ∣ 2^a-1) :
    Even a ∧ Odd b ∧ (a = 2*b ∨ a = 4*b ∨ a = 6*b) := by
  obtain ⟨hev,hob⟩ := original_linear_unitary_parity Q e h split hm i j hij ha hb hi hj
  obtain ⟨hpar,hupper,hlower⟩ := original_linear_unitary_degree_bounds Q e h split hm i j hij ha hb hi hj
  exact linear_unitary_degree_reduction_of_odd_divisibility ha hb hpar hupper hlower
    (fun hoa => ((Nat.not_odd_iff_even.mpr hev) hoa).elim) hcenter

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
