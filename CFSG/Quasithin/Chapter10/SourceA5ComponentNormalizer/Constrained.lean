module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientStructure
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.StarRankReduction
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.RankOneExclusion
/-!
# Completing the constrained branch of source 10.2.6

Start with the original nonnormal A₅ source and a strict normal opposite
component in N_G(L). The exact R=O₂(L₀T) setup and C.2.6 eliminate the possible
nonquasisimple quotient, yielding all literal C.2.7 hypotheses. Its actual star
catalogue, the cubic-rank bound, and the surviving factor five force a binary
SL₂ quotient. The original full Sylow local-component condition excludes that
rank-one enlargement. Consequently every remaining contrary normalizer
configuration has F*(K) different from O₂(K).

No Baumann escape, embedding-list callback, quotient premise, or model premise
is retained. The separate nonconstrained branch is still needed for N_G(L)≤M.
Source: Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The actual C.2.7 catalogue and rank bounds exclude the constrained strict enlargement. -/
theorem source_a5_strict_component_not_constrained
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hKN : (K.subgroupOf (normalizer (L : Set G))).Normal)
    (hBK : L.map (MulAut.conj t).toMonoidHom < K)
    (h3 : primeRank 3 K ≤ 1) : generalizedFitting K ≠ pCore 2 K := by
  intro hF
  have hinput := source_nonnormal_constrained_component_c27_input D hn ht htn hK hKN hBK hF
  obtain ⟨F,⟨d⟩⟩ := source_rank_one_coreQuotient_linearTwo hinput h3
    (source_a5_conjugate_overgroup_five e hBK.le)
  exact source_a5_strict_component_not_binary_rank_one D e hn ht hK hBK hinput.quasisimple d

/-- Failure of source10.2.6 forces an unconstrained ordinary-component branch;
all characteristic-two overcomponents have been excluded from the original source data. -/
theorem source_a5_nonconstrained_normalizer_enlargement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (L : Set G) ≤ D.maximalLocal) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ∃ K : Subgroup G, K ∈ cComponentsIn (normalizer (L : Set G)) ∧
        (K.subgroupOf (normalizer (L : Set G))).Normal ∧
        L.map (MulAut.conj t).toMonoidHom < K ∧
        ¬ K ≤ D.maximalLocal ∧ primeRank 3 K ≤ 1 ∧ primeRank 5 K ≤ 1 ∧
        generalizedFitting K ≠ pCore 2 K := by
  obtain ⟨t,ht,htn,hpair,K,hK,hKN,hBK,houtK,h3,h5,_⟩ :=
    source_a5_strict_component_pushing_enlargement D e hn hout
  exact ⟨t,ht,htn,hpair,K,hK,hKN,hBK,houtK,h3,h5,
    source_a5_strict_component_not_constrained D e hn ht htn hK hKN hBK h3⟩

end CFSG.Quasithin.Chapter10
