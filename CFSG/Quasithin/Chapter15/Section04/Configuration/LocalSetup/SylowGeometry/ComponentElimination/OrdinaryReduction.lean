module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels

/-!
# The ordinary-component part of the source reduction

The full first two clauses of 1.1.5 discharge the odd-core premise before
either C-component alternative is turned into an ordinary component.
For the exchanged case, the actual product, both relative component
inclusions, and the factor permutation are constructed together.

The proved comparisons with all six model/action clauses of 1.1.5(3)
identify the components themselves and construct their inner-action
witnesses. In the exchanged case, conjugation transports the seed model
and each implementing element to the other factor, retaining a common
field parameter. `ordinary_alternatives_of_source` completes this reduction
from the two C-component embedding alternatives and F*(K) ≠ O₂(K).
The full universal earlier result 1.1.5 remains an explicit input; the
subsequent elimination of these ordinary alternatives belongs to the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; 1.1.5, printed pp.501–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open OrdinaryReduction
variable {G : Type*} [Group G] [Finite G]

/-- The odd core is derived from the actual source local hypotheses. -/
theorem source_oddCore_eq_bot {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) : pPrimeCore 2 H = ⊥ :=
  oddCore_eq_bot_of_earlier115 hG earlier s.four s.local115

/-- Alternative (i) yields an ordinary relative component, without assuming
its odd core trivial or its projective cover split. -/
theorem source_binary_component {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (hK : (K.subgroupOf H).IsCComponent)
    (hF : generalizedFitting K ≠ pCore 2 K) : IsComponent H (K.subgroupOf H) := by
  apply ordinary_of_cComponent (s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _)
    hK (source_oddCore_eq_bot hG earlier s) hF

/-- Alternative (ii) yields the two actual ordinary components, with a
permutation induced by conjugation and the specified element exchanging them. -/
theorem source_component_pair {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : PairEmbedding H K U)
    (hF : generalizedFitting K ≠ pCore 2 K) :
    ∃ p : OrdinaryComponentPair H K U,
      p.factor false = b.seed.map H.subtype ∧
      p.factor true = (b.seed.map (MulAut.conj b.conjugator).toMonoidHom).map H.subtype ∧
      p.action.permutation ⟨b.conjugator, b.conjugator_mem⟩ false = true := by
  have hKH : K ≤ H := s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  have hUH : U ≤ H := s.placed.sylow_image ▸ map_subtype_le (s.placed.sylow : Subgroup H)
  have hKN : H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hKH).mp
    rw [s.closure]
    exact EmbeddingReduction.normalClosureIn_normal _ _
  exact ordinary_pair_of_cComponent hKH hUH hKN (source_oddCore_eq_bot hG earlier s)
    hF b.seed b.cComponent b.conjugator b.conjugator_mem b.moves b.product

/-- Conditional model assembly for alternative (ii). The seed model and its
inner witnesses are explicit remaining premises; all ordinary-component,
product, permutation and conjugate-factor obligations are discharged here. -/
theorem ordinary_alternatives_of_seed_model {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : PairEmbedding H K U)
    (hF : generalizedFitting K ≠ pCore 2 K)
    (hm : OrdinaryRankOneModel b.seed)
    (ha : CentralInnerAction (b.seed.map H.subtype) d.Z) :
    OrdinaryAlternatives H K U d.Z := by
  obtain ⟨p, hp0, hp1, _⟩ := source_component_pair hG earlier s b hF
  let e0 : b.seed ≃* p.factor false :=
    (b.seed.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hp0.symm)
  let e1 : b.seed ≃* p.factor true :=
    ((MulAut.conj b.conjugator).subgroupMap b.seed).trans
      (((b.seed.map (MulAut.conj b.conjugator).toMonoidHom).equivMapOfInjective
        H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hp1.symm))
  have hr : (b.conjugator : G) ∈ centralizer (d.Z : Set G) := by
    apply mem_centralizer_iff.mpr
    intro z hz
    rw [s.omega] at hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
      b.conjugator (s.placed.upper.le b.conjugator_mem) |>.symm
  have he : p.factor true = (b.seed.map H.subtype).map
      (MulAut.conj (b.conjugator : G)).toMonoidHom := by
    rw [hp1, map_map, map_map]
    congr 1
  refine Or.inr ⟨p, ?_, ?_⟩
  · rcases hm with ⟨q, hq, hq5, hqL⟩ | ⟨n, hn, hn2, hnL⟩
    · refine Or.inl ⟨q, hq, hq5, ?_⟩
      intro k
      cases k
      · exact hqL.of_mulEquiv e0.symm
      · exact hqL.of_mulEquiv e1.symm
    · refine Or.inr ⟨n, hn, hn2, ?_⟩
      intro k
      cases k
      · exact hnL.of_mulEquiv e0.symm
      · exact hnL.of_mulEquiv e1.symm
  · intro k
    cases k
    · exact hp0 ▸ ha
    · exact he ▸ centralInnerAction_conjugate ha b.conjugator hr

/-- The ordinary-component reduction in the first branch of 15.4.20.
The two source embedding alternatives yield actual ordinary models and
inner witnesses for every element of the central four-group. The odd core,
ordinary-component status, model comparisons and conjugate-factor witnesses
are all proved; only the genuine universal earlier result 1.1.5 is retained. -/
theorem ordinary_alternatives_of_source {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : EmbeddingAlternatives H K U)
    (hF : generalizedFitting K ≠ pCore 2 K) : OrdinaryAlternatives H K U d.Z := by
  have hodd := source_oddCore_eq_bot hG earlierOneTwo s
  rcases b with hb | hb
  · obtain ⟨hK, hm⟩ := hb
    have hc := source_binary_component hG earlierOneTwo s hK hF
    exact Or.inl ⟨hc, binary_models_of_ordinary hG earlierThree s hodd hc hm⟩
  · obtain ⟨b⟩ := hb
    have hKH : K ≤ H := s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
    have hKN : H ≤ normalizer (K : Set G) := by
      apply (normal_subgroupOf_iff_le_normalizer hKH).mp
      rw [s.closure]
      exact EmbeddingReduction.normalClosureIn_normal _ _
    have hc := ordinary_seed_of_pair hKH hKN hodd hF b.seed b.cComponent
      b.conjugator b.product
    obtain ⟨hm, ha⟩ := rank_one_models_of_ordinary hG earlierThree s b hodd hc
    exact ordinary_alternatives_of_seed_model hG earlierOneTwo s b hF hm ha

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
