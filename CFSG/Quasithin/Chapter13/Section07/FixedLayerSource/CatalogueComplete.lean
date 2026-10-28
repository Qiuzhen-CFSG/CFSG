module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.Complete
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.AlternatingExclusion
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerCatalogue

/-!
# The complete original fixed-layer centralization

If the selected component moves U₀, the genuine earlier 13.3.2(1–2)
source input gives the A₅, PSL₃(2), or A₆ rows. The two-layer FF argument
excludes both alternating rows, and the original marked fixed-line
contradiction excludes PSL₃(2). Thus the selected component centralizes U₀.
Every row exclusion is proved on the original action and quotient maps.
Source: Aschbacher–Smith 13.7.16(2), printed p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_component_centralizes_fixedLayer_of_source1332
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T) :
    K.map H.subtype ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  by_contra hm
  have ha := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).2
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  rcases PlusAction.component_model_of_fixedLayer_movement h
      (conjugateSpanBy_elementary_of_commutative V₃ H) h1332 K hKC hm ha with h5 | h3 | h6
  · exact source_no_fixed_layer_alternatingFive d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm h5
  · exact source_no_fixed_layer_linear_three d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm h3
  · exact source_no_fixed_layer_alternatingSix d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm h6

end CFSG.Quasithin.Chapter13.Section07
