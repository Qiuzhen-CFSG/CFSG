module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAction

/-!
# The original Chapter 12 coset graph in the contrary core branch

The chosen module supplies uniqueness over LT, E.6.1 and the central-line
factorization. Thus the graph of LT and any actual H-star subgroup has odd
critical distance. If the layer lies in the centralizer core, the minimal
H-star vertex has an elementary abelian layer closure, and the actual graph
has a critical endpoint at distance at least three with mutually normalizing
closure modules.

The final theorem constructs this vertex from the exact earlier 6.1.5
centralization premise. It does not claim the remaining field-plane
contradiction in 6.2.8 or the numerical conclusion in 6.2.11.

Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The F.7 critical configuration on the original subgroups, with all
normalizer and uniqueness premises discharged by the chosen module. -/
theorem source_local_graph_contrary_configuration
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : commutatorLayer T L ≤ H.pCoreIn 2) :
    let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ∃ (d : SourceSetup F) (hne : d.V ≠ ⊥),
      d.seed.map K.subtype = commutatorLayer T L ∧
      Odd (d.track hne) ∧ 3 ≤ d.track hne ∧
      ∃ e : NormalizedEndpoint d hne,
        ⁅vertexModule F d.seed (base F true), vertexModule F d.seed e.vertex⁆ ≤
          vertexModule F d.seed (base F true) ⊓ vertexModule F d.seed e.vertex := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_graph_contrary_configuration h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hH.1.1.2 hH.1.2 hcore

/-- The minimal H-star vertex supplied by the original omega escape,
retaining the precise contrary assumption used in source 6.2.8. -/
theorem source_local_exists_contrary_graph_vertex
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      (commutatorLayer T L ≤ (centralizer ({z} : Set G)).pCoreIn 2 →
        ∃ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
          H ≤ centralizer ({z} : Set G) ∧ ChapterE.generationParameter H = 1 ∧
          H ⊓ normalizer (commutatorLayer T L : Set G) = H ⊓ normalizer (L : Set G) ∧
          H ⊓ normalizer (L : Set G) ⋖ H ∧
          (∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ H →
            X = H ⊓ normalizer (L : Set G)) ∧
          commutatorLayer T L ≤ H.pCoreIn 2 ∧
          IsElementaryAbelian 2 (⨆ g : H,
            (commutatorLayer T L).map (MulAut.conj (g : G)).toMonoidHom : Subgroup G)) := by
  obtain ⟨z, hz, ho, hT, _, _, he, _⟩ :=
    source_local_omega_geometry_of_hstar_centralization h611 hnatural hout hcentral
  refine ⟨z, hz, ho, hT, fun hcore => ?_⟩
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_exists_contrary_graph_vertex h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hz ho hT he hcore

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
