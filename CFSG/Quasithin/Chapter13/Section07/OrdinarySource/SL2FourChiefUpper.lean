module
public import CFSG.Quasithin.Chapter13.Section07.ComponentFaithfulness
public import CFSG.Quasithin.Chapter13.Section07.L1ChiefCount
public import Theory.SpecificGroups.Alternating.FiveElementaryActors

/-!
# The selected SL₂(4) actor and chief-count upper bound

For the component selected by the original Section 13.7 offender construction,
13.7.16(1) makes the actual elementary actor act faithfully on the component.
An SL₂(4) quotient is A₅, whose automorphism group is S₅. Thus the actor has
order at most four. The literal local chief-count identity then bounds every
complete L₁ chief series by four noncentral binary factors.

This is the upper half of the rank-four specialization used by the original
natural SL₂(4) terminal branch. The lower half retains the original source
geometry and the marked natural action.
Source: Aschbacher–Smith, 13.7.13 and 13.7.16(1), printed pp.942–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The selected elementary actor has order at most four in the A₅ case. -/
theorem source_five_actor_card_le_four
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
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
    (e : K.map (QuotientGroup.mk' (pCore 2 H)) ≃* alternatingGroup (Fin 5)) :
    Nat.card (((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))) ≤ 4 := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  let A := conjugate (Section08.Source.VH H V) (g : G) ⊓
    (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
  let Astar := (A.subgroupOf H).map π
  let S := ((T : Subgroup G).subgroupOf H).map π
  have hn := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  let : J.Normal := hn.map π (QuotientGroup.mk'_surjective _)
  have hc := source_plus_sylow_centralizer_eq_bot d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hAT : A ≤ (T : Subgroup G) := inf_le_right.trans
    (h.sylow_centralizer.symm.le.trans inf_le_left)
  have hAS : Astar ≤ S := map_mono (subgroupOf_mono H hAT)
  have hd : Disjoint Astar (centralizer (J : Set (H ⧸ pCore 2 H))) := by
    apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_right _ hAS).trans hc.le)
  have hEA := (pair_actor_elementary_nontrivial d h hU hV g hs hout).2.1
  let : IsElementaryAbelian 2 Astar := hEA
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.elementary_card_le_four_of_disjoint
    J e Astar hd

/-- The actual local chief-count formula bounds a complete series by four. -/
theorem source_five_chief_count_le_four
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
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
    (e : K.map (QuotientGroup.mk' (pCore 2 H)) ≃* alternatingGroup (Fin 5))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : t.head = ⊥) (h1 : t.last = ⊤) : t.noncentralTwoCount ≤ 4 := by
  have hc := source_five_actor_card_le_four d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm e
  have hl := Nat.log_mono_right (b := 2) hc
  have ht := source_L1_full_chief_count d h hU hV g hs hspan hout t h0 h1
  rw [show Nat.log 2 4 = 2 from by decide] at hl
  omega

/-- Five source chief factors are incompatible with the selected A₅ packet. -/
theorem source_five_false_of_five_chief_factors
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
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
    (e : K.map (QuotientGroup.mk' (pCore 2 H)) ≃* alternatingGroup (Fin 5))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : t.head = ⊥) (h1 : t.last = ⊤) (hfive : 5 ≤ t.noncentralTwoCount) : False := by
  have hf := source_five_chief_count_le_four d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm e hspan t h0 h1
  omega

end CFSG.Quasithin.Chapter13.Section07
