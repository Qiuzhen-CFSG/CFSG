module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Escape

/-!
# Conditional assembly of the genuine local collapse

The ambient proof now derives every conclusion of 14.7.74 and the literal
Ru center/centralizer from three remaining module steps: the marked Steinberg
splitting, the first Gaschütz commutator bound, and natural-extension rigidity.
The second Gaschütz centralization is consumed by genuine maximal-overgroup
uniqueness to discharge the fixed-subgroup premise of rigidity.

These premises are not assumed to be source theorems. Their construction
remains with the projective/Gaschütz and natural-rigidity branches; final
14.7.74 assembly remains here. The preceding 71--73 fields of `Prior` are
owned by the chief-factor, Steinberg and root branches of SourceEndgame.
No existing SourceEndgame or CriticalFusion interface has been changed.

The final core equality uses 14.7.73(2) and the original alternating star
image instead of the R₁ count. This avoids an additional parabolic counting
premise; the original marked Steinberg section still gives |S|=2¹¹.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.74--75, printed pp.1077--1078 (PDF pp.1094--1095).
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)
include a

/-- The complete ambient assembly with the remaining module steps explicit.
This conditional theorem is not the completed source Lemma 14.7.74. -/
theorem source_conclusions_of_module_steps
    (hsplit : Q T L = QC T L V ⊔ S L F)
    (hKC : ⁅QC T L V, K F⁆ ≤ F.U)
    (hKQL : K F ≤ centralizer (QL T L : Set G))
    (hrigid : QL T L = ⊥ → V < QC T L V →
      ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) :
    normalizer (L : Set G) = L ∧
    S L F = (normalizer (L : Set G)).pCoreIn 2 ∧
    F.H = K F ⊔ (T : Subgroup G) ∧
    F.H.pCoreIn 2 = (K F).pCoreIn 2 ∧
    sylowCenter T = F.Vi 1 ∧ F.H = centralizerOfSylowCenter T ∧
    Nat.card (S L F) = 2 ^ 11 ∧ Nat.card (F.H.pCoreIn 2) = 2 ^ 11 := by
  have hQL := QL_eq_bot_of_K_centralizes d a hKQL
  obtain ⟨hm, hs, hh, hp, hz, hc⟩ :=
    conclusions_of_extension_inputs d a hsplit hKC (hrigid hQL)
  exact ⟨hm, hs, hh, hp, hz, hc, card_S d a, by rw [hp]; exact a.core_order⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
