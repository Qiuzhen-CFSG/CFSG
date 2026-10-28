module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryDiagonal
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNormalizers

/-!
# The actual selected component in ordinary 13.3.14

The contrary plane-centralization assumption and the original nonabelian
full-span hypothesis give the selected faithful C-component of the point
normalizer. This module collects reductions (a–f), including normality,
the unique maximal normalizer, and the plane-parabolic escape, using the
literal original subgroup maps.

The earlier 13.3.2 restriction and guarded 3.1.8(1) are explicit source
inputs. The later offender generation, reduced module marking, and diagonal
geometry are separate inputs; no F.9 hypothesis is used to construct them.
Source: Aschbacher–Smith, 13.3.14, printed pp.891–893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

theorem ordinary_selected_component_from_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) :
    ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ ∧
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) ∧
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ ∧
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map H.subtype ∈ Chapter1.LStar G T ∧
      H ≤ normalizer (K.map H.subtype : Set G) ∧
      IsMaximalTwoLocal (normalizer (K.map H.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N → K.map H.subtype ⊔ (T : Subgroup G) ≤ N →
        N = normalizer (K.map H.subtype : Set G)) ∧
      ¬L ≤ normalizer (K.map H.subtype : Set G) ∧ ¬K.map H.subtype ≤ M ∧
      ¬sourceOne L T E ≤ normalizer (K.map H.subtype : Set G) := by
  obtain ⟨K,hK,hKs,hm,hn,hgen,hq,hU,hfaithful⟩ :=
    ordinary_faithful_component_of_guarded_sources d e h1221 h1332 h318 hV hc
  obtain ⟨hs,hHN,hmax,huniq,hL,hM⟩ :=
    ordinary_component_normalizer_conclusions d h1221 hV h1332 K hK hfaithful
  exact ⟨K,hK,ordinary_component_normal d h1332 K hK hfaithful,hKs,hm,hn,hgen,hq,hU,
    hfaithful,hs,hHN,hmax,huniq,hL,hM,ordinary_reduction_f d e h1221 hV h1332 K hK hfaithful⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
