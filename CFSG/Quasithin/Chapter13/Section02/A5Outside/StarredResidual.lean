module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FaithfulResidual
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.XiMembership
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ResidualModels
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.CyclicCenter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.StarNormalizer
/-!
# Faithful Xi placement and the source starred-family consumer

The original wreath residual is in Xi_f: its elementary quotient and
actual irreducibility come from13.2.9, and the original moving omega-center
makes its intrinsic signalizer module nontrivial. For the starred assertion,
two-perfectness places a prospective contained residual in a component's
Sylow orbit. A.4.10 makes that component faithful. The earlier normalization
of faithful components collapses the orbit, where the A₅ three-rank bound
contradicts the residual's elementary nine-group.

The normalization premise is exactly the earlier12.2.2(3) assertion used
in printed13.2.10. It is not supplied by the marked Context for arbitrary
faithful components and remains explicit. The final consumer applies the
proved1.3.7 to the original H and the literal residual normalizer.

Source: Aschbacher–Smith13.2.10–11, printedp.881, with1.3.7 and A.4.10.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The full unstarred faithful-family assertion on the original residual. -/
theorem source_wreath_residual_mem_XiF
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.XiF G (T : Subgroup G) :=
  ⟨source_wreath_residual_mem_Xi d hH hB hZ hs e,source_residual_faithful d hH hZ⟩

/-- Source13.2.10 with only its earlier faithful-component normalization retained. -/
theorem source_wreath_residual_mem_XiStarF_of_normalizes_faithful
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.XiStarF G (T : Subgroup G) := by
  have hf := source_wreath_residual_mem_XiF d hH hB hZ hs e
  refine ⟨hf,hf.1,?_⟩
  intro K hK _ hXK
  have ho := le_componentOrbit_of_twoPerfect hf.1.perfect T.isPGroup'
    (le_sup_left.trans hXK)
  have hfaith := (Terminal.lemma_1_3_9_two_source d.hypothesis.qtke T hf hK ho).2
  have he : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K _ K le_rfl (hn K hfaith))
      (le_componentOrbit K _)
  exact source_wreath_residual_not_le_faithful_component d e hfaith (he ▸ ho)

/-- The1.3.7 application in13.2.11, with the exact original overgroup H. -/
theorem source_wreath_residual_normalizer_unique_of_normalizes_faithful
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    IsMaximalTwoLocal (normalizer (((pResidual 2 H).map H.subtype) : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ H ≤ M} =
        {normalizer (((pResidual 2 H).map H.subtype) : Set G)} := by
  have hf := source_wreath_residual_mem_XiStarF_of_normalizes_faithful d hn hH hB hZ hs e
  have hu := normalizer_unique_of_XiStar_knownSimple d.hypothesis.qtke T hf.2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hgen : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map,range_subtype] using hh
  rwa [hgen] at hu
end CFSG.Quasithin.Chapter13.Section02.A5Outside
