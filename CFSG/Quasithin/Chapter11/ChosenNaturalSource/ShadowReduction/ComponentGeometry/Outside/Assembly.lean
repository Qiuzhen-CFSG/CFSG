module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.SelectedSource

/-!
# Applying the completed outside family to component reduction

The original component-reduction and selected-source consumers now receive
the proved odd-kernel normalizer theorem on their unchanged chosen module.
This includes the full SL₃(4) central cover and the literal O²(H) alternative.
The last application uses the constructed G₂ radical witness in E.3.19 and
returns the surviving marked SL₃/Sp₄ endgame, with its radical bounds.

Only the independently owned preceding geometry and source implications
remain. Their discharge belongs to qt-d-1222-shadow-components and
qt-d-1222-natural-shadow-reduction. These results complete the outside
family's contribution; they do not assert unconditional earlier geometry.

Source: Aschbacher–Smith, refs/quasithin.pdf, 11.4.3–4 and 11.5.1,
printed pp.778–779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (hcent : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G))
    (hcartan_line : f.Vi 0 = ⁅zpowers z, X⁆)
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : (ofFlag S f X z H).K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h1132 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z H).K X 0 S.field.degree)
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)

include h hNT hlinear hcent hcartan_line hX hXR hKZ h701 h1132 h1122 href h1115

/-- Apply the completed outside family to original component reduction.
There is no odd-kernel, native-cover or quotient-marking premise. -/
theorem ofFlag_source_reduction_of_preceding :
    SourceReductionAt (ofFlag S f X z H) := by
  exact ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S)

variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- The parent's actual selected-source consumer, including the original
G₂ witness before the terminal contradiction, with normalizer control proved. -/
theorem ofFlag_selected_source_of_preceding :
    ∃ J, SourceReductionAt (ofFlag S f X z J) ∧
      (EndgameAt (ofFlag S f X z J) ∨ SelectedG2At (ofFlag S f X z J)) := by
  exact ofFlag_selected_source S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115 hunique hthree hline hcomponent
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S)

/-- Original 11.5.1 removes the G₂ marking and feeds the surviving marked
endgame. The same selected H retains both products, its O² alternative,
generation one and the literal radical bounds. -/
theorem ofFlag_source_endgame_of_preceding :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact ofFlag_source_endgame S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S)
    hunique hthree hline hcomponent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
