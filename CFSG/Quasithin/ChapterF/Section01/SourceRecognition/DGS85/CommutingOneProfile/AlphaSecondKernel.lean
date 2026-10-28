module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BetaCoreSpecial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel

/-!
# The alpha second kernel and the beta third kernel

Let I_alpha be the intersection of the beta cores at every alpha neighbor.
It is normalized by Q_beta and contained in Q_beta. Since Q_beta has derived
subgroup and center Z_beta, its commutator with Q_beta lies in I_alpha ∩ Z_beta.
The escaping neighboring beta core makes this intersection trivial. Thus
I_alpha lies in Z_beta and is itself trivial.

The actual radius-two kernel has two-core I_alpha. It is normal in the
alpha stabilizer, whose two-core is self-centralizing, so the full kernel
is trivial as well. The adjacent beta radius-three kernel is then trivial.
At beta, the radius-two two-core is exactly the earlier Z_beta.

The argument covers the full beta catalogue and all field degrees. It uses
the already proved special-core and remote-layer equalities, not a natural
alpha-module assumption. ReducedSecondKernels applies the result through
the original inclusion and to the nonelementary full-Borel branch. These
ball-kernel conclusions do not assert the remaining length-five path-fixer
or regularity clauses.
Source: DGS85, Groups and Graphs (1985), consequences of (11.6), pp.172--174,
and the special-core calculation in (11.7)--(11.8), pp.174--176;
ball-kernel and local-core conventions in Chapter 6.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem normal_subgroup_of_special_disjoint_center
    (N R C : Subgroup G) (hNR : N ≤ R)
    (hn : R ≤ normalizer (N : Set G))
    (hder : ⁅R,R⁆ ≤ C) (hcent : centerIn R = C)
    (hd : N ⊓ C = ⊥) : N = ⊥ := by
  have hcomm : ⁅N,R⁆ = ⊥ := by
    apply bot_unique
    apply le_trans ?_ hd.le
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      ((commutator_mono hNR le_rfl).trans hder)
  have hNC : N ≤ C := hcent ▸ le_inf hNR
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact bot_unique ((le_inf le_rfl hNC).trans hd.le)

/-- The intersection over all neighboring beta cores is trivial at alpha. -/
theorem source_alpha_neighbor_intersection_eq_bot_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    neighborCoreIntersection (family P) a = ⊥ := by
  have hab := source_critical_one_adjacent hc hb
  have hat : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hs := source_beta_core_special_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hI := source_neighbor_intersection_eq_center_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hz := source_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  rw [hI] at hz
  apply normal_subgroup_of_special_disjoint_center
    (neighborCoreIntersection (family P) a) (Q (family P) b) (Z (family P) b)
    (neighborCoreIntersection_le _ hab.symm)
  · exact ((source_Z_Q_U h b).2.trans
      ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)).trans
        (neighborCoreIntersection_normalized _ a)
  · exact hs.2.1.le
  · exact hs.1
  · apply bot_unique
    rw [inf_comm] at hz
    exact (inf_le_inf (neighborCoreIntersection_le _ hat.symm) le_rfl).trans hz.le


/-- The two source radius-two radicals, with their distinct orientations. -/
theorem source_second_kernel_cores_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    (ballKernel (family P) a 2).pCoreIn 2 = ⊥ ∧
      (ballKernel (family P) b 2).pCoreIn 2 = Z (family P) b := by
  have hab := source_critical_one_adjacent hc hb
  have hSyl := source_kernel_sylow h hB hS
  rw [←source_neighborCoreIntersection_eq_second_core h hSyl hab.symm,
    ←source_neighborCoreIntersection_eq_second_core h hSyl hab]
  exact ⟨source_alpha_neighbor_intersection_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp,
    source_neighbor_intersection_eq_center_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp⟩


private theorem source_ball_kernel_eq_bot_of_core_eq_bot
    (h : LocallyRankOneTriple P B) (a : Vertex (family P)) (r : ℕ)
    (hz : (ballKernel (family P) a r).pCoreIn 2 = ⊥) :
    ballKernel (family P) a r = ⊥ := by
  let N := ballKernel (family P) a r
  have hNa : N ≤ stabilizer (family P) a := ballKernel_le_stabilizer _ _ _
  have hnQ : N ≤ normalizer (Q (family P) a : Set G) :=
    hNa.trans (stabilizer_normalizes_Q _ a)
  have hnN : Q (family P) a ≤ normalizer (N : Set G) :=
    (Q_le_stabilizer _ a).trans (stabilizer_le_normalizer_ballKernel _ _ _)
  have hi : N ⊓ Q (family P) a = ⊥ := by
    apply bot_unique
    apply le_trans ?_ hz.le
    exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le inf_le_right)
      inf_le_left ((le_inf N.le_normalizer hnQ).trans inf_normalizer_le_normalizer_inf)
  have hc : ⁅N,Q (family P) a⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hnN)
      (le_normalizer_iff_commutator_le_right.mp hnQ)).trans hi.le
  have hNQ : N ≤ Q (family P) a :=
    (le_inf hNa (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (source_core_selfCentralizing_in_vertex h a)
  exact bot_unique ((le_inf le_rfl hNQ).trans hi.le)

/-- Faithfulness at radius two on alpha and radius three on beta. -/
theorem source_full_second_kernels_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    ballKernel (family P) a 2 = ⊥ ∧ ballKernel (family P) b 3 = ⊥ ∧
      (ballKernel (family P) b 2).pCoreIn 2 = Z (family P) b := by
  obtain ⟨hα,hβ⟩ := source_second_kernel_cores_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hfull := source_ball_kernel_eq_bot_of_core_eq_bot h a 2 hα
  refine ⟨hfull,?_,hβ⟩
  exact bot_unique ((ballKernel_succ_le (family P)
    (source_critical_one_adjacent hc hb).symm 2).trans hfull.le)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
