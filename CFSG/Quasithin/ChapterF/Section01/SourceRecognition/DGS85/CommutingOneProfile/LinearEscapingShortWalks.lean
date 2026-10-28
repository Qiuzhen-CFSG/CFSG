module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCenterEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RemoteLayerVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths

/-!
# The short escaping walks used by the commuting-one exclusion

An actual linear alpha marking already supplies center escape on an alpha
turn. Choose the turn by local transitivity and the source valence bound.
The resulting two-walk [alpha,beta,gamma] and three-walk
[g gamma,g beta,alpha,beta] are nonbacktracking. Thus the remote-layer
vanishing theorem requires only three-walk transitivity, not a transitive
four-walk containing both original and translated gamma.

The last theorem applies the construction to the literal neighbor-core
intersection used in the Suzuki exclusion. The actual alpha marking and
three-walk transitivity remain precise inputs to that consumer.
Source: DGS85, Groups and Graphs (1985), proof of (11.6), printed p.173.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem short_walk_neighbor_other (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (a b : Vertex (family P)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c := by
  let := finite_endpoints h
  have hv := card_neighbors_of_indices (family P)
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl) b
  have hcard : 1 < ((graph (family P)).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have := source_valence_ge_three h hS b.type
    omega
  obtain ⟨c,hc,hca⟩ := Set.exists_ne_of_one_lt_ncard hcard a
  exact ⟨c,hc,Ne.symm hca⟩

/-- A linear alpha mark constructs the actual escape and both shorter
source walks, without any path-transitivity premise. -/
theorem source_linear_exists_escaping_short_walks
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c ∧
      ∃ g ∈ stabilizer (family P) a, g • b ≠ b ∧
        ¬ Z (family P) b ≤ Q (family P) (g • b) ∧
        (∃ p : BasedWalk (graph (family P)) 2 a,
          p.Nonbacktracking ∧ p.vertices = [a,b,c]) ∧
        ∃ q : BasedWalk (graph (family P)) 3 (g • c),
          q.Nonbacktracking ∧ q.vertices = [g • c,g • b,a,b] := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨c,hbc,hac⟩ := short_walk_neighbor_other h hS a b
  obtain ⟨b',hab',hbb'⟩ := short_walk_neighbor_other h hS b a
  obtain ⟨t,hta,htb⟩ := locally_transitive (family P) hab hab'
  have htb' : t • b ≠ b := by rw [htb]; exact Ne.symm hbb'
  obtain ⟨g,hga,hgb,hesc⟩ := source_linear_rankOne_center_escape
    h hB d hc hb hcomm hbc hac Ma Mb ea t hta htb'
  have hb'a : (graph (family P)).Adj (g • b) a := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab.symm
    change (graph (family P)).Adj (g • b) (g • a) at hh
    rwa [show g • a = a from hga] at hh
  have hc'b' : (graph (family P)).Adj (g • c) (g • b) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc.symm
  refine ⟨c,hbc,hac,g,hga,hgb,hesc,?_,?_⟩
  · refine ⟨⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩,?_,rfl⟩
    change c ≠ a ∧ True
    exact ⟨Ne.symm hac,trivial⟩
  · refine ⟨⟨⟨g • b,hc'b'⟩,⟨⟨a,hb'a⟩,⟨⟨b,hab⟩,PUnit.unit⟩⟩⟩,?_,rfl⟩
    change a ≠ g • c ∧ b ≠ g • b ∧ True
    exact ⟨fun he => hac ((MulAction.injective g) ((show g • a = a from hga).trans he)),
      Ne.symm hgb,trivial⟩

/-- The remote layer needed by the actual Suzuki consumer vanishes under
three-walk transitivity; all escape and walk-choice inputs are discharged. -/
theorem source_linear_escaping_remote_layer_of_three_walks
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (ht : ∀ v, RootPathTransitive (graph (family P)) G v 3) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c ∧
      ∃ g ∈ stabilizer (family P) a, g • b ≠ b ∧
        ¬ Z (family P) b ≤ Q (family P) (g • b) ∧
        neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) = ⊥ := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,_,q,hq,hqv⟩ :=
    source_linear_exists_escaping_short_walks h hB hS d hc hb hcomm Ma Mb ea
  refine ⟨c,hbc,hac,g,hga,hgb,hesc,?_⟩
  exact source_linear_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb ea g hga hgb hesc (ht (g • c)) q hq
    (by rw [hqv]; simp) (by rw [hqv]; simp)
    (by rw [hqv]; simp) (by rw [hqv]; simp)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
