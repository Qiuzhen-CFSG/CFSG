module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OctagonSixH
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiPanelCompletion

/-!
# Original factor markings and the octagonal Ree input

Complete original linear and Suzuki factor markings to the full faithful
panels, retaining their whole Borels and both original quotient squares.
The finite octagon supplies odd degree; the source (6H) constructor then
supplies all subgroup relations. The dihedral factor is completed to
Sz(2), so its common field forces linear degree one. Two factors drawn
from the Suzuki/dihedral alternatives are excluded in either orientation.

Source: Fong--Seitz I (1J), (5C), (6H), pp.6,25--26,51--56;
Aschbacher--Smith F.1.1. Family and rotation selection, and the subsequent
Section 10 angular equations, remain separate source obligations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)

/-- Source (6H) data with both original faithful panels and their literal
endpoint squares. The full original and marked Borels are retained. -/
structure OriginalReeSixHData (split : SplitData Q.tits) (n m : ℕ)
    extends ReeSixHData Q split n m where
  originalLinear : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃*
    PSL2BinaryMatrixGroup n
  originalSuzuki : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃*
    SuzukiMatrixGroup m
  originalLinearBorel :
    (originalFaithfulBorel (L := L) (S := S) 0).map originalLinear.toMonoidHom =
      normalizer (linearSylow : Set _)
  originalSuzukiBorel :
    (originalFaithfulBorel (L := L) (S := S) 1).map originalSuzuki.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set _)
  linear_square : ∀ x : parabolic L S 0,
    originalLinear (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) 0) x) =
      linear (QuotientGroup.mk' (panelKernel Q 0) (endpoint Q e 0 x))
  suzuki_square : ∀ x : parabolic L S 1,
    originalSuzuki (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) 1) x) =
      suzuki (QuotientGroup.mk' (panelKernel Q 1) (endpoint Q e 1 x))

variable (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)

/-- Retain the original squares while applying the source-proved (6H) constructor. -/
def originalReeSixHData_of_panels
    (τ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃*
      PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map τ₀.toMonoidHom =
      normalizer (T : Set _))
    (τ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃*
      SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map τ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set _)) : OriginalReeSixHData Q e split n m where
  toReeSixHData := originalSourceReeSixHData_of_octagon Q e h split hm n hn m
    τ₀ T hB₀ τ₁ hB₁
  originalLinear := τ₀
  originalSuzuki := τ₁
  originalLinearBorel := hB₀
  originalSuzukiBorel := hB₁
  linear_square x := by
    change τ₀ _ = τ₀ ((originalPanelQuotientEquiv Q e h 0).symm _)
    congr 1
    apply (originalPanelQuotientEquiv Q e h 0).injective
    rw [MulEquiv.apply_symm_apply, originalPanelQuotientEquiv_mk]
  suzuki_square x := by
    change τ₁ _ = τ₁ ((originalPanelQuotientEquiv Q e h 1).symm _)
    congr 1
    apply (originalPanelQuotientEquiv Q e h 1).injective
    rw [MulEquiv.apply_symm_apply, originalPanelQuotientEquiv_mk]

include e h split hm hn in
/-- The actual factor quotients construct all (6H) data; the original linear
marking is extended exactly and the Suzuki marking up to its chosen inner conjugacy. -/
theorem original_factor_sixH_data
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL2BinaryMatrixGroup n)
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup m) :
    ∃ c : OriginalReeSixHData Q e split n m,
      (∀ l : L 0, c.originalLinear (QuotientGroup.mk'
        (originalPanelKernel (L := L) (S := S) 0)
        ⟨l,(show L 0 ≤ parabolic L S 0 from le_sup_left.trans le_sup_left) l.property⟩) =
          μ₀ (QuotientGroup.mk' (pCore 2 (L 0)) l)) ∧
      ∃ g : SuzukiMatrixGroup m, ∀ l : L 1,
        c.originalSuzuki (QuotientGroup.mk'
          (originalPanelKernel (L := L) (S := S) 1)
          ⟨l,(show L 1 ≤ parabolic L S 1 from le_sup_left.trans le_sup_left) l.property⟩) =
            g * μ₁ (QuotientGroup.mk' (pCore 2 (L 1)) l) * g⁻¹ := by
  obtain ⟨_,T,τ₀,_,hB₀,_,_,hfactor₀⟩ := LinearPanel.original_panel Q e h split 0 μ₀
  obtain ⟨g,_,τ₁,_,hB₁,_,_,hfactor₁⟩ := SuzukiPanel.original_panel Q e h split 1 μ₁
  exact ⟨originalReeSixHData_of_panels Q e h split hm n hn m τ₀ T hB₀ τ₁ hB₁,
    hfactor₀,g,hfactor₁⟩

include e h split hm hn in
/-- A dihedral original second factor gives the full binary Suzuki panel and
forces the linear field to be binary, without a perfectness premise. -/
theorem original_dihedral_sixH_data
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL2BinaryMatrixGroup n)
    (μD : ((L 1) ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) :
    n = 1 ∧ Nonempty (OriginalReeSixHData Q e split n 0) := by
  obtain ⟨_,T,τ₀,_,hB₀,_,_,_⟩ := LinearPanel.original_panel Q e h split 0 μ₀
  obtain ⟨τ₁,_,hB₁,_⟩ := SuzukiPanel.dihedral_original_coordinates Q e h split 1 μD
  let c := originalReeSixHData_of_panels Q e h split hm n hn 0 τ₀ T hB₀ τ₁ hB₁
  exact ⟨by simpa using c.common_field,⟨c⟩⟩

include e h split in
private theorem suzuki_or_dihedral_original_panel (i : Fin 2)
    (hi : (∃ a, Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)) :
    ∃ a, ∃ τ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃*
      SuzukiMatrixGroup a,
      (originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (SuzukiRootSubgroup a : Set _) := by
  rcases hi with ⟨a,⟨μ⟩⟩ | hD
  · obtain ⟨_,_,τ,_,hB,_,_,_⟩ := SuzukiPanel.original_panel Q e h split i μ
    exact ⟨a,τ,hB⟩
  · obtain ⟨τ,_,hB,_⟩ := SuzukiPanel.dihedral_original_coordinates Q e h split i hD.some
    exact ⟨0,τ,hB⟩

include e h split hm in
/-- The square obstruction excludes all Suzuki/dihedral pairs, including the
order-ten original factors and either original endpoint orientation. -/
theorem original_suzuki_dihedral_pair_excluded
    (i j : Fin 2) (hij : i ≠ j)
    (hi : (∃ a, Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : (∃ a, Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) : False := by
  obtain ⟨a,τ₀,hB₀⟩ := suzuki_or_dihedral_original_panel Q e h split i hi
  obtain ⟨b,τ₁,hB₁⟩ := suzuki_or_dihedral_original_panel Q e h split j hj
  exact original_two_suzuki_panels_excluded_of_octagon Q e h split hm i j hij a b
    τ₀ hB₀ τ₁ hB₁

private theorem binary_linear_marking {Y : Type*} [Group Y] {a : ℕ}
    (ha : 0 < a) (hlinear : ClassicalGroup.IsPSL Y 2 (2^a)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup a) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hlinear
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 2 a)
  let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 a ha.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

include e h split hm hn in
/-- The literal F.1.1 factor assertions suffice for the selected linear/Suzuki
or linear/dihedral branch, with no full-panel, oddness or relation premise. -/
theorem original_suzuki_or_dihedral_sixH_data
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n))
    (hother : (∃ a, Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5)) :
    ∃ a, Nonempty (OriginalReeSixHData Q e split n a) := by
  obtain ⟨μ₀⟩ := binary_linear_marking hn hlinear
  rcases hother with ⟨a,⟨μ₁⟩⟩ | hD
  · obtain ⟨c,_⟩ := original_factor_sixH_data Q e h split hm n hn a μ₀ μ₁
    exact ⟨a,⟨c⟩⟩
  · exact ⟨0,(original_dihedral_sixH_data Q e h split hm n hn μ₀ hD.some).2⟩

include e h split hm hn in
/-- On the nonbinary linear branch the original dihedral factor is impossible;
this uses the source common field, including the genuine binary completion. -/
theorem original_nonbinary_linear_dihedral_excluded
    (hnlarge : 1 < n)
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n))
    (hdihedral : Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5)) : False := by
  obtain ⟨μ₀⟩ := binary_linear_marking hn hlinear
  have he := (original_dihedral_sixH_data Q e h split hm n hn μ₀ hdihedral.some).1
  omega

include e h split hm hn in
/-- Exhaust the original opposite-factor catalogue at the linear endpoint.
The unresolved source alternatives are precisely linear and the two unitary
quotients; every Suzuki or dihedral alternative already constructs (6H). -/
theorem original_octagon_sixH_or_linear_or_unitary
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    (∃ a, Nonempty (OriginalReeSixHData Q e split n a)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 (2^b)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU ((L 1) ⧸ pCore 2 (L 1)) 3 (2^b)) ∨
      (∃ b, 0 < b ∧ IsSU ((L 1) ⧸ pCore 2 (L 1)) 3 (2^b)) := by
  cases h.quotient 1 with
  | linear b hb hmodel => exact Or.inr (Or.inl ⟨b,hb,hmodel⟩)
  | suzuki a hmodel =>
    exact Or.inl (original_suzuki_or_dihedral_sixH_data Q e h split hm n hn
      hlinear (Or.inl ⟨a,hmodel⟩))
  | projective_unitary b hb hmodel => exact Or.inr (Or.inr (Or.inl ⟨b,hb,hmodel⟩))
  | special_unitary b hb hmodel => exact Or.inr (Or.inr (Or.inr ⟨b,hb,hmodel⟩))
  | dihedral hmodel =>
    exact Or.inl (original_suzuki_or_dihedral_sixH_data Q e h split hm n hn
      hlinear (Or.inr hmodel))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
