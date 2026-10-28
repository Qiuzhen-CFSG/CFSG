module
public import CFSG.Quasithin.Chapter13.Section07.OffenderClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.NormalOffenderClassification
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Only the two product-module alternatives remain in13.7.15

Use the normal closure of the actual selected minimal offender inside H*.
The proved13.7.14 centralizer theorem makes its Fitting subgroup central;
therefore the outer A₆–C₃ source alternative is impossible. Complete B.5
and the original seed plane yield Irr⁺ and the four group families unless
one of the two literal product-module structures occurs on this normal
closure. The selected component and its moved subspace are transported
back to the original H* action. No classification, centralizer or module
conclusion is an input.

The genuine prior inputs are F.9 applicability, the source abelian seed
span and nonabelian full span, seed-core noncentrality, and13.7.4 kernel
equality, together with the already constructed selected component.
Source: Aschbacher–Smith13.7.14–15, printed pp.943–944.
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
theorem source_plus_component_sieve_or_product
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
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
        (σ.comp (normalClosure (B : Set (H ⧸ pCore 2 H))).subtype)) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase
        (σ.comp (normalClosure (B : Set (H ⧸ pCore 2 H))).subtype)) := by
  let J := K.map (QuotientGroup.mk' (pCore 2 H))
  let N := normalClosure (B : Set (H ⧸ pCore 2 H))
  have hf := source_plus_faithful_of_kernel_eq σ s hk
  obtain ⟨hJN,_,_⟩ := ChapterB.SourceInduction.moved_component_in_normalClosure σ hf hK hB.1 hcomm
  have hcentral := source_minimal_offender_centralizes_fitting d h hU hV hne g hs hout σ s hf hB hBA
  have hplane := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hd : Module.finrank (ZMod 2) (moved σ B) ≤ 2 :=
    (Submodule.finrank_mono hplane.2).trans_eq hplane.1
  rcases ChapterB.SourceInduction.component_plane_of_fitting_centralizing_offender σ hf
    (pCore_quotient_pCore_eq_bot 2) (source_plus_sqtk_cover d h)
    hK hB.1 hcomm hcentral hd with ⟨hi,hg⟩ | hr
  · apply Or.inl
    have hcomp : moved (σ.comp N.subtype) (J.subgroupOf N) = moved σ J := by
      change subspaceCommutator (σ.comp N.subtype) ⊤ (J.subgroupOf N) = _
      rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hJN]
    rw [hcomp] at hi
    exact ⟨(IsIrrPlus.subgroupOf_iff σ J N hJN _).mp hi,
      SmallMoved.ActorList.of_mulEquiv hg (subgroupOfEquivOfLe hJN).symm⟩
  · exact Or.inr hr

/-- Construct the original conjugator, faithful plus action, minimal offender
and selected component together with the complete two-case source reduction. -/
theorem exists_source_plus_component_sieve
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
          (_s : BinaryConjugationSection H U U₀ (σ.comp π))
          (B : Subgroup (H ⧸ pCore 2 H)) (K : Subgroup H),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧ B ≤ (A.subgroupOf H).map π ∧
          K.IsCComponent ∧ IsComponent (H ⧸ pCore 2 H) (K.map π) ∧
          B ≤ normalizer (K.map π : Set (H ⧸ pCore 2 H)) ∧ ⁅K.map π,B⁆ = K.map π ∧
          ((IsIrrPlus σ (K.map π) (moved σ (K.map π)) ∧ SmallMoved.ActorList (K.map π)) ∨
            Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
              (σ.comp (normalClosure (B : Set (H ⧸ pCore 2 H))).subtype)) ∨
            Nonempty (ChapterB.SourceInduction.HyperplaneCase
              (σ.comp (normalClosure (B : Set (H ⧸ pCore 2 H))).subtype))) := by
  obtain ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,_,hK,hKs,hn,hcomm,_,_⟩ :=
    exists_source_selected_component d h hU hV hne hk
  let := hE
  have hc := source_plus_component_sieve_or_product d h hU hV hne
    (inclusion le_sup_left g) hs hout σ s B hB hBA K hKs hk hcomm
  exact ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hK,hKs,hn,hcomm,hc⟩

end CFSG.Quasithin.Chapter13.Section07
