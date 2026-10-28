module

public import CFSG.Quasithin.Chapter13.Section07.SourceSeedPlane
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Rows
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# The original plus moved component belongs to Irr⁺

The original seed plane bounds the entire commutator span of B*. Restricting
to the actual overgroup K*B* preserves that bound and the offender inequality.
The complete B.5.1 alternatives then force Irr⁺ on the literal moved space,
which the ambient-section equivalence returns to the original H* action.
The B.5.1 source conclusion is the sole classification input retained here;
the Chapter 13 component-selection owner constructs its actual component.

Source: Aschbacher–Smith 13.7.15(2), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The literal Chapter 13 consumer of the reducible B.5.1 row exclusions. -/
theorem source_plus_component_irrPlus
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
      (moved σ (K.map (QuotientGroup.mk' (pCore 2 H)))) := by
  let J := K.map (QuotientGroup.mk' (pCore 2 H))
  let D := J ⊔ B
  let : IsQuasisimple J := hK.2
  let : IsQuasisimple (J.subgroupOf D) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show J ≤ D from le_sup_left)).symm
  have hplane := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hd : Module.finrank (ZMod 2) (moved σ B) ≤ 2 :=
    (Submodule.finrank_mono hplane.2).trans_eq hplane.1
  have hcomp (A : Subgroup D) : moved (σ.comp D.subtype) A = moved σ (A.map D.subtype) := by
    simpa only [Submodule.map_id] using subspaceCommutator_map_embedding
      (σ.comp D.subtype) σ D.subtype (LinearMap.id : W →ₗ[ZMod 2] W)
      (fun _ _ => rfl) A ⊤
  have hAB := (hB.1.isOffender σ).subgroupOf σ (show B ≤ D from le_sup_right)
  have hdB : Module.finrank (ZMod 2) (moved (σ.comp D.subtype) (B.subgroupOf D)) ≤ 2 := by
    rw [hcomp, map_subgroupOf_eq_of_le (show B ≤ D from le_sup_right)]
    exact hd
  have hi := SmallMoved.source_irrPlus_of_plane (σ.comp D.subtype) hAB hdB sK hc
  rw [hcomp, map_subgroupOf_eq_of_le (show J ≤ D from le_sup_left)] at hi
  exact (IsIrrPlus.subgroupOf_iff σ J D le_sup_left _).mp hi
end CFSG.Quasithin.Chapter13.Section07
