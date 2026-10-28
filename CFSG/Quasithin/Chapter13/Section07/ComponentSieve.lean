module
public import CFSG.Quasithin.Chapter13.Section07.OffenderClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentPlane
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# The source component sieve after the actual B.5 application

The plus action determines its normal offender subgroup, and complete B.5
classifies that literal action. The original seed plane bounds the whole
displacement of the selected minimal offender after restriction. The
quasisimple adequate alternative therefore gives both original13.7.15
conclusions via the complete small-displacement sieve, and the solvable
alternative is impossible. The result keeps exactly the remaining two-factor,
outer A₆–C₃ and hyperplane structures. No B.5 row is assumed.

Source: Aschbacher–Smith13.7.15(1–2), printed pp.943–944.
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
theorem source_plus_component_sieve_or_remaining
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
    (K : Subgroup H) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H))) :
    (IsIrrPlus σ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (moved σ (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧ SmallMoved.ActorList (K.map (QuotientGroup.mk' (pCore 2 H)))) ∨
      ChapterB.SourceInduction.RemainingComponentCases (σ.comp (offenderSubgroup σ).subtype) := by
  let J := K.map (QuotientGroup.mk' (pCore 2 H))
  let N := offenderSubgroup σ
  obtain ⟨hc,hJN,_,hJ⟩ := source_plus_selected_component_classification d h σ s hk K hK B hB.1 hcomm
  have hBN : B ≤ N := hB.1.le_offenderSubgroup σ
  have hplane := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hd : Module.finrank (ZMod 2) (moved σ B) ≤ 2 :=
    (Submodule.finrank_mono hplane.2).trans_eq hplane.1
  have hcomp (A : Subgroup N) : moved (σ.comp N.subtype) A = moved σ (A.map N.subtype) := by
    change subspaceCommutator (σ.comp N.subtype) ⊤ A = _
    rw [subspaceCommutator_comp_map]
  have hdB : Module.finrank (ZMod 2) (moved (σ.comp N.subtype) (B.subgroupOf N)) ≤ 2 := by
    rw [hcomp, map_subgroupOf_eq_of_le hBN]
    exact hd
  rcases ChapterB.SourceInduction.component_plane_of_adequate (σ.comp N.subtype) hJ
      ((hB.1.isOffender σ).subgroupOf σ hBN) hdB hc with ⟨hi,hg⟩ | hr
  · apply Or.inl
    rw [hcomp, map_subgroupOf_eq_of_le hJN] at hi
    exact ⟨(IsIrrPlus.subgroupOf_iff σ J N hJN _).mp hi,
      SmallMoved.ActorList.of_mulEquiv hg (subgroupOfEquivOfLe hJN).symm⟩
  · exact Or.inr hr

end CFSG.Quasithin.Chapter13.Section07
