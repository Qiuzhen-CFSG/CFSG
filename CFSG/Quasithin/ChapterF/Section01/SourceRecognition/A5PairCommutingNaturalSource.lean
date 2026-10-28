module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralEquivalencesSource

/-!
# Natural center in the original commuting A5 pair

A nonzero displacement supplies a moving neighbor. Its actual graph quotient
is SL₂(4), transported from the original A5 marking. The full omega subgroup
of its quotient Sylow and the original residual-fixed theorem make the
critical displacement central. The source central-equivalence theorem then
identifies it with the terminal center and makes the starting center natural.

All source hypotheses are produced from the full original F.1.1 pair and its
two A5 marks. No commuting-intersection, naturality, model-catalogue, reduced
comparison, or core-containment premise is supplied by the caller. This is the
Chapter 8 natural-center reduction; the Chapter 12 original join-core equality
and containment remain separate obligations.

Source: DGS, Groups and Graphs (1985), (8.1), (8.6)--(8.7), pp.132--140.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- In every original commuting A5/A5 critical configuration, the literal
nonzero displacement equals the terminal center and the starting center is natural. -/
theorem a5_pair_commuting_critical_natural
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v,
      Z (Reduction.reducedFamily L S) w⁆ = ⊥) :
    b (Reduction.reducedFamily L S) = 3 ∧
      ⁅V (Reduction.reducedFamily L S) u 1 ⊓ Q (Reduction.reducedFamily L S) w,
        V (Reduction.reducedFamily L S) w 1⁆ = Z (Reduction.reducedFamily L S) w ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup (Reduction.reducedFamily L S) v)
        (Z (Reduction.reducedFamily L S) v) (Q (Reduction.reducedFamily L S) v) := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  have models (z : Vertex F) : IsRankOneModel (graphLocalGroup F z ⧸
      pCore 2 (graphLocalGroup F z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hb : 1 < b F := by
    change 1 < b (Reduction.reducedFamily L S)
    omega
  obtain ⟨z, hm, _⟩ := exists_moving_neighbor F (fun t => (source_Z_Q_U ht t).1) u w hne
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := a5_pair_reduced_graph_linear_four h a z.val
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hcentral := reduced_linear_moving_commutator_central h models hc hvu hd hb hcomm z hm e
  obtain ⟨_, _, _, _, hAD, hDI, hIN, hNE⟩ :=
    reduced_critical_central_equivalences h models hc hvu hd hb hcomm hne
  have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
  exact ⟨hb3, hNE.mp hnat, hnat⟩
end CFSG.Quasithin.ChapterF.Source
