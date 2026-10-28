module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLowerBound

/-!
# A rooted transitivity lower bound for the source minimum

If the source graph is rooted-path transitive through a length `N` from both
vertex orbits, then no source path of length strictly below `N` can be the first
nonregular path.  This is the lower-bound half of the field-four path
parameter argument; the compatible J₂ transport supplies the rooted
transitivity premise in that application.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem right_regular_of_root_transitive
    {n : ℕ} {a : Vertex (family P)}
    (ht : RootPathTransitive (graph (family P)) G a (n + 1))
    (p : BasedWalk (graph (family P)) n a) (hp : p.Nonbacktracking) :
    RightRegular (A := G) p := by
  intro z w hz hw
  have haz := forward_adj p hz
  have haw := forward_adj p hw
  obtain ⟨g, _, hg⟩ := ht (p.snoc haz) (p.snoc haw)
    ((forward_iff_snoc_nonbacktracking p hp haz).mp hz)
    ((forward_iff_snoc_nonbacktracking p hp haw).mp hw)
  rw [vertices_snoc, vertices_snoc, List.map_append, List.map_singleton] at hg
  have hs := List.append_inj hg (by simp :
    (p.vertices.map (g • ·)).length = p.vertices.length)
  refine ⟨g, ?_, ?_⟩
  · simpa only [List.map_id, id_eq] using
      (List.map_inj_left (l := p.vertices) (f := (g • ·)) (g := id)).mp
        (hs.1.trans (List.map_id p.vertices).symm)
  · simpa only [List.singleton_inj] using hs.2

/-- Rooted transitivity through `N` forces `N ≤ sourceS`.

The proof uses the source's first nonregular path.  If it had length below
`N`, transitivity at one more step would make its right endpoint regular, a
contradiction.  The endpoint index is chosen from the first nonregular path,
so transitivity is required only at the two source orbits.
-/
theorem sourceS_ge_of_root_transitive
    (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i),
      (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {N : ℕ}
    (ht : ∀ i, RootPathTransitive (graph (family P)) G
      (base (family P) i) N) :
    N ≤ sourceS (P := P) := by
  have hdeg : HasTwoNeighbors (graph (family P)) := by
    intro a b
    apply Set.exists_ne_of_one_lt_ncard
      (s := (graph (family P)).neighborSet a) _ b
    rw [← Nat.card_coe_set_eq,
      card_neighbors_of_indices (family P)
        (fun i => ((family P (!i)).subgroupOf (family P i)).index)
        (fun _ => rfl)]
    have hh := source_valence_ge_three h hS a.type
    omega
  obtain ⟨n, hs, _, _, i, p, hp, hbad, _⟩ :=
    source_first_nonregular_parameter h hS
  have he := (sourceS_spec h hS).2.unique hs
  by_contra hle
  have hk : n + 1 + 1 ≤ N := by
    rw [he] at hle
    omega
  exact hbad (right_regular_of_root_transitive
    ((ht i).mono hdeg hk) p hp)

end CFSG.Quasithin.ChapterF.Source.DGS85
