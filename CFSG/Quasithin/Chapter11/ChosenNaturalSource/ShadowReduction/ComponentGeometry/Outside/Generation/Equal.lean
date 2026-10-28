module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.LinearAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.G2Action

/-!
# Generation one for every equal-component source row

The three genuine natural-action markings exhaust the chosen coordinates.
Their Hall-action theorems prove n(H)=1 for every original outside H in
the equality row K=L₁. Selection then gives the same literal H, its O²
alternative, and the escaping R₁ O²(H) carrier with its actual R₁ Sylow
subgroup. Normality is relative to H and the embedded two-residuals agree.

The exact OddKernelNormalizer input remains with
qt-d-1222-natural-odd-kernel-normalizer. Earlier geometry, 11.3.2, the
linear fixed-space input and Kz=K retain qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison, with final discharge by
qt-d-1222-shadow-components. Generation of the smaller carrier and the
strict-component Hall reduction remain with qt-d-1222-shadow-component-witness.
This module does not assert the full 11.4.4 or 11.5.1.
Source: Aschbacher--Smith, printed pp.778--779 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Source 11.4.4 for every original equal-component natural row. -/
theorem ofFlag_equal_generation_eq_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) : ChapterE.generationParameter H = 1 := by
  cases c with
  | sl3 m => exact ofFlag_sl3_equal_generation_eq_one S m f X z H h he hK hcontrol hH hHz
  | sp4 m => exact ofFlag_sp4_equal_generation_eq_one S m f X z H h he hK hlinear h1132 hcontrol hH hHz
  | g2 m => exact ofFlag_g2_equal_generation_eq_one S m f X z H h he hK hlinear h1132 hcontrol hH hHz

/-- The selected H has generation one, and its literal R₁ O²(H) carrier
has the proved containment, escape, Sylow, normality and residual properties. -/
theorem ofFlag_equal_selected_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 ∧
      let J₁ := (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype
      J₁ ≤ J ∧ ¬ J₁ ≤ normalizer (L : Set G) ∧
        Chapter1.IsSylowIn 2 (ofFlag S f X z J).R₁ J₁ ∧
        (J₁.subgroupOf J).Normal ∧
        (pResidual 2 J₁).map J₁.subtype = (pResidual 2 J).map J.subtype := by
  obtain ⟨J,hJ,hJz,hs,hJ₁J,hout,hSyl,_⟩ :=
    ofFlag_equal_selected_radical_carrier S f X z H h he hK hNT h1132
  refine ⟨J,hJ,hJz,hs,?_,hJ₁J,hout,hSyl,
    radical_carrier_normal _ hJ.1.1.2,radical_carrier_residual _ hJ.1.1.2⟩
  exact ofFlag_equal_generation_eq_one S f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
    he hK hlinear h1132 hcontrol hJ hJz

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
