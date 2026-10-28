module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.CentralCoverNormalizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ActionCentralizer

/-!
# Central-cover normalization in the original A₅ configuration

The genuine F.9 setup and the source index-two seed supply the component
centralizer transport. Original module-normalizer control discharges its
remaining normalizer bound. The quotient normality instance is constructed
by the same selected-component normalization used by the source prefix,
so the conclusion uses literally the same Khat, Vhat and L1hat.

This supplies the remaining central-cover normalization input to the
configuration owner's O₂,₃ argument in Aschbacher–Smith13.5.21(ii), p.923.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction.Recognition ComponentReduction.Recognition.Configuration
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

theorem source_Khat_actor_centralizer_normalizes_local :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    ∀ (K : Subgroup G) (s : Selected D K),
      let := componentCentralizer_normal s hf
        (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
      Khat s hf ⊓ centralizer (Vhat s hf : Set (Xhat s hf)) ≤
        normalizer (L1hat s hf : Set (Xhat s hf)) := by
  intro D hf K s
  let := componentCentralizer_normal s hf
    (selected_star_local_normalization s hf d.hypothesis.qtke hH.1.1)
  exact Khat_actor_centralizer_normalizes_local s hf d.third_index hU
    (inf_le_right.trans d.module_normalizer)
end CFSG.Quasithin.Chapter13.Section05.A5Source
