module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentPlaneComplete
public import CFSG.Quasithin.Chapter13.Section07.OffenderClassification

/-!
# Full original13.7.15(1–2) on the constructed plus component

The original point normalizer supplies the actual SQTK cover of H*. The
constructed minimal offender and original seed plane now give both the
small actor catalogue and Irr⁺ for the entire K*-moved module. All B.5
preparation and classifier premises are proved from full earlier sources.
The existential application constructs every original marked object.

The genuine prior inputs remain NaturalSetup, F.9 applicability, abelian
U_H, nonabelian V_H, seed-core noncentrality and13.7.4 kernel equality.
Clause(3), normality of K in H, remains a separate source assertion.
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
theorem source_plus_component_irrPlus_and_actor
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
    IsIrrPlus σ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧ SmallMoved.ActorList (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  have hp := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  exact ChapterB.SourceInduction.component_irrPlus_and_actor_of_minimal_plane σ
    (source_plus_faithful_of_kernel_eq σ s hk) (pCore_quotient_pCore_eq_bot 2)
    (source_plus_sqtk_cover d h) hK hB hcomm
    ((Submodule.finrank_mono hp.2).trans_eq hp.1)

/-- Construct the original conjugator, faithful plus action, minimal offender,
and moved C-component, retaining the exact quotient image and seed plane. -/
theorem exists_source_component_irrPlus_and_actor
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      let U := Section08.Source.UH H V₃
      let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
      let π := QuotientGroup.mk' (pCore 2 H)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ U₀.subgroupOf U)))
          (s : Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (B : Subgroup (H ⧸ pCore 2 H)) (K : Subgroup H),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧
          B ≤ (A.subgroupOf H).map π ∧
          B ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) ∧
          K.IsCComponent ∧ IsComponent (H ⧸ pCore 2 H) (K.map π) ∧
          B ≤ normalizer (K.map π : Set (H ⧸ pCore 2 H)) ∧
          ⁅K.map π,B⁆ = K.map π ∧
          Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
          subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ ∧
          IsIrrPlus σ (K.map π) (subspaceCommutator σ ⊤ (K.map π)) ∧
          SmallMoved.ActorList (K.map π) := by
  obtain ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hc,hK,hKs,hn,hcomm,hd,hm⟩ :=
    exists_source_selected_component d h hU hV hne hk
  let := hE
  have hh := source_plus_component_irrPlus_and_actor d h hU hV hne
    (inclusion le_sup_left g) hs hout σ s B hB hBA K hKs hk hcomm
  exact ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hc,hK,hKs,hn,hcomm,hd,hm,hh⟩

end CFSG.Quasithin.Chapter13.Section07
