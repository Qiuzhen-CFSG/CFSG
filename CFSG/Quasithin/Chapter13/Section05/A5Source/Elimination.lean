module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefCount
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ResidualStructure

/-!
# Literal A₅ source consumers of the final component obstructions

The original source context now supplies the G.2.4 marking, recognition,
complete chief count, elementary second layer and local-core upper bound.
Thus the A₈ order contradiction only retains its two concrete module
orders. The G₂(2)′ contradiction only retains its original order-four
element and cubic fixed-space calculation. The A₆ three-factor
contradiction is the complete chief-series result in ChiefCount.
These explicit component-module inputs still belong to13.5.21–25;
this module does not assert the full classification13.5.12.
Source: Aschbacher–Smith13.5.23–25, printed pp.924–925.
-/
public section
open Subgroup Theory.GroupTheory
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
include d hA312 hH hU

/-- The13.5.23 contradiction retains only the actual two model orders and
preceding tilde commutator. The source conjugator is constructed internally. -/
theorem source_a8_order_exclusion
    (htilde : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hcard : Nat.card (Source.UH H V₃) = 128)
    (himage : Nat.card (Source.starImage H ((residualCentralizer L V₁).pCoreIn 2)) = 32) :
    False := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have he : NormalBranch.K D g = L := block_group_eq d hA312 hH hU hg hg₁ htilde
  have hbound := residual_core_card_bound d hA312 hH hU
  have hupper : Nat.card (D.L₁.pCoreIn 2) ≤
      4 * Nat.card ((NormalBranch.K D g).pCoreIn 2) := by
    rw [he]
    exact hbound
  exact a8_order_contradiction V₁ V₃ L T H (residualCentralizer L V₁) g
    (blockMarking d hA312 hH hU hg hg₁)
    ChapterG.Section01.SL2FourRecognition.recognitionInput hcard
    (le_sup_left.trans hf.local_le)
    ((closure_reduction_of_tilde d hA312 hH htilde).2.1.trans (pCoreIn_le 2 _))
    hupper himage

/-- The13.5.25 fixed-space contradiction uses the original residual,
original cubic subgroup and original order-four element. -/
theorem source_g2_fixed_point_exclusion
    {g j : G} (hg : g ∈ L) (hg₁ : g ∉ normalizer (V₁ : Set G))
    (X : Subgroup G) (hj : orderOf j = 4)
    (hjcore : j ∈ (residualCentralizer L V₁).pCoreIn 2)
    (hjfixed : j ∈ centralizer (X : Set G))
    (hfixed : (residualCentralizer L V₁).pCoreIn 2 ⊓ centralizer (X : Set G) ≤
      V ⊔ (Source.UH H V₃ ⊓ ChapterG.Section02.Setup.conjugate (Source.UH H V₃) g)) :
    False :=
  g2_fixed_point_contradiction V₁ V₃ V L T H (residualCentralizer L V₁) X g j
    (blockMarking d hA312 hH hU hg hg₁) d.line_span_eq hj hjcore hjfixed hfixed

end CFSG.Quasithin.Chapter13.Section05.A5Source
