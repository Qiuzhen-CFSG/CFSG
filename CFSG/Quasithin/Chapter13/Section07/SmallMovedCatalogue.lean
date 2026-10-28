module

public import CFSG.Quasithin.Chapter13.Section07.SmallMovedIrrPlus
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Catalogue

/-!
# The original 13.7.15 component and its small actor catalogue

The same plus action, selected quotient component and seed plane give Irr⁺
on the original moved module. Every B.4 and B.5 source row is then inspected:
only the four source group families or the precise covered-A6 quotient row
remain. The latter retains its faithful action and a best offender inside
B*, with the full displacement bound. No original central extension is split.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The literal source component sieve, retaining only the covered-A6 geometry. -/
theorem source_plus_component_small_models_or_triple
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
    (sK : MovedSection (σ.comp
      (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B).subtype)
      ((K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
        (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B)))
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase (σ.comp
      (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B).subtype)
      ((K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
        (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B)) sK) :
    IsIrrPlus σ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (moved σ (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧
    (SmallMoved.ActorList (K.map (QuotientGroup.mk' (pCore 2 H))) ∨
      (Function.Injective sK.central.quotientRepresentation ∧
        offenderSubgroup sK.central.quotientRepresentation =
          (K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
            (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B) ∧
        Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
          sK.central.quotientRepresentation
          ((K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
            (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B))) ∧
        ∃ C ≤ B.subgroupOf (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B),
          IsBestOffender sK.central.quotientRepresentation C ∧
          Module.finrank (ZMod 2) (moved sK.central.quotientRepresentation C) ≤ 2)) := by
  refine ⟨source_plus_component_irrPlus d h hU hV hne g hs hout σ s B hB hBA K hK sK hc, ?_⟩
  let J := K.map (QuotientGroup.mk' (pCore 2 H))
  let D := J ⊔ B
  have hplane := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hd : Module.finrank (ZMod 2) (moved σ B) ≤ 2 :=
    (Submodule.finrank_mono hplane.2).trans_eq hplane.1
  have hdB : Module.finrank (ZMod 2) (moved (σ.comp D.subtype) (B.subgroupOf D)) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (σ.comp D.subtype) ⊤ (B.subgroupOf D)) ≤ 2
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le (show B ≤ D from le_sup_right)]
    exact hd
  have hoff := (hB.1.isOffender σ).subgroupOf σ (show B ≤ D from le_sup_right)
  have hmodels := SmallMoved.source_actor_or_triple_of_plane (σ.comp D.subtype)
    (L := J.subgroupOf D) hoff hdB sK hc
  rcases hmodels with hg | ht
  · let e : J ≃* J.subgroupOf D := (subgroupOfEquivOfLe (show J ≤ D from le_sup_left)).symm
    exact Or.inl (SmallMoved.ActorList.of_mulEquiv hg e)
  · exact Or.inr ht
end CFSG.Quasithin.Chapter13.Section07
