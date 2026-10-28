module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SixFalse
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Elimination
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.CubicFixed
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.G2FixedFour

/-!
# The original A₅ G₂ exclusion

The original G₂ central quotient supplies a cubic-fixed element of order four
in U_H. Whole-module generation puts it in the actual residual two-core.
The original G.2.4 natural upper section forces every such cubic fixed point
into the elementary second layer, where an element of order four is impossible.
Source: Aschbacher–Smith13.5.25, printed p.925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule
open ChapterG.Section02.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hU : ¬ IsMulCommutative D.UH)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (hnot : ¬ ModelConclusion G 5)
include d h hA312 hH hU hnot

/-- The G₂ natural central quotient is impossible in the original A₅ setup. -/
theorem g2_source_false
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u) =
        g2DerivedNatural (ZMod 2) (f b) (fV u)) : False := by
  let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm := source_local_component_commutator d h hA312 hH hnot K s
  have hgroup := group_conclusions s h hSQ d.third_index hU hLK d.third_eq_commutator hm
    (selected_actor_normalization s h d.third_index hU).2
  have hgen := linear_generation D h s hLK hgroup.1 d.third_eq_commutator
  have hne : starImage D.H K ≠ ⊥ := by
    intro he
    exact s.moved (by rw [he,commutator_bot_left])
  obtain ⟨A,hAL,hA⟩ := source_exists_cubic d hA312 hH hU
  obtain ⟨j,hjU,hj,hjA⟩ := OriginalSix.G2FixedFour.exists_cubic_fixed_order_four h hU
    K hn hne hgen f fV hfV A (hAL.trans hLK) (hAL.trans (hLK.trans s.le_H)) hA
  have htilde := (g2_source_conclusions d h hA312 hH hnot hU K s hLK hn f fV hfV).2.2.2.2
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  let S := chapter13Setup D.V₁ D.Vplus D.L D.T D.H
  let b : Hypothesis S g := blockMarking d hA312 hH hU hg hg₁
  have hres : S.L₁ = D.L₁ := h.g2_L₁
  have hfixed := b.cubic_fixed_le_second A (hres.symm ▸ hAL) hA
  rw [hres] at hfixed
  have hfixed' : D.L₁.pCoreIn 2 ⊓ centralizer (A : Set G) ≤
      D.V ⊔ (D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g) := by
    change D.L₁.pCoreIn 2 ⊓ centralizer (A : Set G) ≤
      conjugateSpanBy D.V₁ D.L ⊔ (D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g) at hfixed
    simpa only [d.line_span_eq] using hfixed
  exact source_g2_fixed_point_exclusion d hA312 hH hU hg hg₁ A hj
    ((closure_reduction_of_tilde d hA312 hH htilde).2.1 hjU) hjA hfixed'
end CFSG.Quasithin.Chapter13.Section05.A5Source
