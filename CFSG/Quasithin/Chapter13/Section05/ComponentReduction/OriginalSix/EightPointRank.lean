module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.EightApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ComponentStructure
public import Theory.Representation.BinaryPermutation.PointStabilizerRank.CentralCover

/-!
# Three-rank of the original A₈ point stabilizers

The actual selected component fills the A₈ actor. Its natural central
quotient has point stabilizers of three-rank at least two, and the same
bound lifts through the literal fixed-space kernel to every vector of
U_H/V₁. In particular it applies to a generator of the original V₂/V₁
line, supplying the rank input to the plane-centralizer contradiction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),13.5.23,
printed p.925, using the bound in13.5.4(3).
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BinaryNaturalDual.VectorStabilizers
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

/-- The original K* stabilizer of every vector in U_H/V₁ has three-rank at least two. -/
theorem alternating_eight_source_point_rank
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (f : Catalogue.actor D K ≃* alternatingGroup (Fin 8))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
          (centralProjection D h fV u)) (u : Action.Space D) :
    2 ≤ primeRank 3 ((representationStabilizer (Action.starRepresentation D h) u).subgroupOf
      (starImage D.H K)) := by
  have hLK := (source_component_structure d h e hU K s c).2.2.1
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  have hB : Catalogue.actor D K = starImage D.H K :=
    alternating_eight_actor_eq_component D h s hSQ hLK
      (source_local_component_commutator d h e h1221 hc K s) f
  have hk : (centralProjection D h fV).ker ≤
      fixedSpace ((Action.starRepresentation D h).comp (Catalogue.actor D K).subtype) ⊤ := by
    intro w hw a
    have hw' : w ∈ fixedSpace (Action.starRepresentation D h) (starImage D.H K) :=
      (centralProjection_ker D h fV).le hw
    exact hw' ⟨a.val.val, hB ▸ a.val.property⟩
  have hr := BinaryPermutation.PointStabilizerRank.two_le_central_cover_stabilizer
    ((Action.starRepresentation D h).comp (Catalogue.actor D K).subtype) f
    (centralProjection D h fV) hfV hk u
  change 2 ≤ primeRank 3 ((representationStabilizer (Action.starRepresentation D h) u).subgroupOf
    (Catalogue.actor D K)) at hr
  rwa [hB] at hr
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
