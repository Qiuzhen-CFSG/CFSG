module
public import CFSG.Quasithin.ChapterF.Section09.SeedNormalizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceGeometry

/-!
# The original A₅ centralizer-normalizer input to13.5.21(ii)

The actual A₅ source context places N_G(V) in N_G(L). Every member of
N_H(V) centralizes the original line, so it normalizes C_L(V₁) and its
two-residual L₁. The genuine13.5.7 producer supplies F.9.1, the original
seed has index two, and nonabelian U_H makes V* nontrivial. The proved
F.9.5(3) therefore identifies C_{H*}(V*) and C_{K*}(V*) with the literal
normalizer images and makes them normalize the same L₁*.

The main source theorem includes L₁≤N_H(V) and relative normality there.
These are the original action-centralizer inputs to configuration(ii).
The separate central-cover comparison in X/C_X(K*) and O₂,₃ assembly
remain with the configuration consumer; no such conclusion is assumed here.
Source: Aschbacher–Smith13.5.21(ii), printed p.923, using F.9.5(3), p.319.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original A₅ module normalizer normalizes the same point residual. -/
theorem source_module_normalizer_normalizes_local
    (hHZ : H ≤ centralizer (V₁ : Set G)) :
    H ⊓ normalizer (V : Set G) ≤ normalizer (residualCentralizer L V₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer (V₁ : Set G)) (pResidual 2 (L ⊓ centralizer (V₁ : Set G) : Subgroup G)))
  exact (le_inf (inf_le_right.trans d.module_normalizer)
    (inf_le_left.trans (hHZ.trans (centralizer (V₁ : Set G)).le_normalizer))).trans
    inf_normalizer_le_normalizer_inf

/-- Relative normality is proved on the original N_H(V), before any star map. -/
theorem source_local_normal_in_module_normalizer
    (hHZ : H ≤ centralizer (V₁ : Set G)) :
    ((residualCentralizer L V₁).subgroupOf (H ⊓ normalizer (V : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer (source_module_normalizer_normalizes_local d hHZ)

variable [IsElementaryAbelian 2 V]
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include hA312 hH hU

/-- The original13.5.21(ii) normalization input, with genuine F.9.5(3)
and the actual local-module normalizer bound both discharged. -/
theorem source_action_centralizer_normalizer :
    centralizer (Source.starImage H V : Set (Source.Hstar H)) =
      Source.starImage H (H ⊓ normalizer (V₃ : Set G)) ∧
    centralizer (Source.starImage H V : Set (Source.Hstar H)) =
      Source.starImage H (H ⊓ normalizer (V : Set G)) ∧
    residualCentralizer L V₁ ≤ H ⊓ normalizer (V : Set G) ∧
    ((residualCentralizer L V₁).subgroupOf (H ⊓ normalizer (V : Set G))).Normal ∧
    centralizer (Source.starImage H V : Set (Source.Hstar H)) ≤
      normalizer (Source.starImage H (residualCentralizer L V₁) : Set (Source.Hstar H)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hn : ¬ D.V ≤ D.QH := (hf.star_module_ne_bot_iff_not_le_core).mp
    (source13_5_13 d hA312 hH hU).1
  have he := hf.star_centralizer_eq_normalizer_images d.third_index hn
  have hlocal : D.L₁ ≤ D.H ⊓ normalizer (D.V : Set G) := by
    intro x hx
    exact hf.normalizer_control ⟨hf.local_le (mem_sup_left hx),
      hf.local_normalizes (mem_sup_left hx)⟩
  refine ⟨he.1,he.2,hlocal,source_local_normal_in_module_normalizer d hf.H_centralizes,?_⟩
  exact hf.star_centralizer_normalizes_local d.third_index hn
    (inf_le_right.trans d.module_normalizer)

/-- Restrict F.9.5(3) to the literal selected component, retaining its star map. -/
theorem source_relative_action_centralizer (K : Subgroup G) :
    Source.starImage H K ⊓ centralizer (Source.starImage H V : Set (Source.Hstar H)) =
      Source.starImage H (K ⊓ normalizer (V : Set G)) ∧
    Source.starImage H K ⊓ centralizer (Source.starImage H V : Set (Source.Hstar H)) ≤
      normalizer (Source.starImage H (residualCentralizer L V₁) : Set (Source.Hstar H)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hn : ¬ D.V ≤ D.QH := (hf.star_module_ne_bot_iff_not_le_core).mp
    (source13_5_13 d hA312 hH hU).1
  exact ⟨hf.star_relative_centralizer_eq_normalizer_image d.third_index hn K,
    inf_le_right.trans (source_action_centralizer_normalizer d hA312 hH hU).2.2.2.2⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
