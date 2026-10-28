module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.Complete
public import CFSG.Quasithin.Chapter13.Section05.Endgame

/-!
# Original A₅ source orders and the complete chief count

The constructed G.2.4 marking and the actual equality K=L supply both
order formulas with one common multiplicity s. The complete chief-series
calculation gives2s+2 on the literal residual O²(C_L(V₁)), yielding the
three-factor exclusion in13.5.24. The second layer used by13.5.25 is
also elementary abelian on these same source subgroups and conjugator.
The preceding component-module row must still supply its three-factor
calculation or its order-four fixed element.
Source: Aschbacher–Smith13.5.22–25, printed pp.924–925.
-/
public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterG.Section02.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  {g : G} (hg : g ∈ L) (hg₁ : g ∉ normalizer (V₁ : Set G))
include d hA312 hH hU hg hg₁

/-- The original second layer is elementary, before any order-four contradiction. -/
theorem second_layer_elementary :
    IsElementaryAbelian 2 (V ⊔ (Source.UH H V₃ ⊓
      ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g) : Subgroup G) :=
  chapter13_source_second_elementary V₁ V₃ V L T H (Source.UH H V₃) g
    (blockMarking d hA312 hH hU hg hg₁) d.line_span_eq rfl

variable (htilde : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
include htilde

/-- Both orders and the complete2s+2 count, on the original L and L₁. -/
theorem source13_5_22 : ∃ s : ℕ,
    Nat.card (L.pCoreIn 2) = 2 ^ (4 * s + 4) *
      V.relIndex (V ⊔ (Source.UH H V₃ ⊓ ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g)) ∧
    Nat.card (Source.UH H V₃) = 2 ^ (2 * s + 5) *
      V.relIndex (V ⊔ (Source.UH H V₃ ⊓ ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g)) ∧
    ∀ t : ChiefSeries (residualCentralizer L V₁), t.head = ⊥ → t.last = ⊤ →
      t.noncentralTwoCount = 2 * s + 2 := by
  let S := chapter13Setup V₁ V₃ L T H
  let b : Hypothesis S g := blockMarking d hA312 hH hU hg hg₁
  let := b.second_normal_in_core b.L_le_I
  have hgen : S.I g = S.L := block_group_eq d hA312 hH hU hg hg₁ htilde
  obtain ⟨s,c,_,_,_,hu,hs⟩ := b.source_natural_layer ChapterG.Section01.SL2FourRecognition.recognitionInput
  have hc := ComponentReduction.ChiefCount.complete_count b hgen c
  have hres : residualCentralizer L V₁ = S.L₁ := by
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    exact hf.g2_L₁.symm
  refine ⟨s,?_,?_,?_⟩
  · change Nat.card ((S.I g).pCoreIn 2) = _ at hs
    rw [hgen] at hs
    change Nat.card (L.pCoreIn 2) = 2 ^ (4 * s + 4) *
      (conjugateSpanBy V₁ L).relIndex ((conjugateSpanBy V₁ L) ⊔
        (Source.UH H V₃ ⊓ ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g)) at hs
    simpa only [d.line_span_eq] using hs
  · change Nat.card (Source.UH H V₃) = 2 ^ (2 * s + 5) *
      (conjugateSpanBy V₁ L).relIndex ((conjugateSpanBy V₁ L) ⊔
        (Source.UH H V₃ ⊓ ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g)) at hu
    simpa only [d.line_span_eq] using hu
  · rw [hres]
    exact hc

/-- The three-chief-factor source alternative is incompatible with the
original marked A₅ branch, as required in13.5.24. -/
theorem source_three_factor_exclusion
    (t : ChiefSeries (residualCentralizer L V₁)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount ≠ 3 := by
  obtain ⟨s,_,_,hc⟩ := source13_5_22 d hA312 hH hU hg hg₁ htilde
  have hh := hc t ht0 ht1
  omega

end CFSG.Quasithin.Chapter13.Section05.A5Source
