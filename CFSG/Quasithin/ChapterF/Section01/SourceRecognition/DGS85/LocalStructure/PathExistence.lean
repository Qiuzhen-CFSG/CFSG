module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathComplement
public import Theory.GroupTheory.AmalgamGraph.PathExistence
/-!
# Finite source paths and their full-Borel complements

Properness and the literal vertex Sylow marking make each Borel index an
odd integer at least three. Finite vertex stabilizers then give a positive
first nonregular length, with rooted path transitivity in both vertex
orbits up to that length. A failing path is transported through the marked
edge. The path supplement and Schur--Zassenhaus choose its complement
inside the actual full Borel.

The reduced F1.11 application supplies the finite-local and Sylow inputs
and retains the original Borel core under the literal inclusion. Only the
model branching premise remains in the complement statement.

Source: DGS, Groups and Graphs (1985), Part II, 3.4, pp.73--74, and
6.7--6.8, p.123. This is the first nonregular length r, not an identification
with the possibly larger last transitivity length s.
-/

public noncomputable section
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem source_borel_index_ge_three {R : Subgroup G} (d : LocalRankOneData R B)
    (hS : ∃ T : Sylow 2 R, (T : Subgroup R).map R.subtype ≤ B) :
    3 ≤ (B.subgroupOf R).index := by
  let := d.finite_P
  obtain ⟨T,hT⟩ := hS
  have hle : (T : Subgroup R) ≤ B.subgroupOf R := by
    intro x hx
    exact hT (mem_map_of_mem _ hx)
  have hodd : ¬ 2 ∣ (B.subgroupOf R).index :=
    fun hd => T.not_dvd_index (hd.trans (index_dvd_of_le hle))
  have hpos := (B.subgroupOf R).index_ne_zero_of_finite
  have hne : (B.subgroupOf R).index ≠ 1 := by
    intro he
    have hPB := subgroupOf_eq_top.mp (index_eq_one.mp he)
    exact (source_borel_lt d).not_ge hPB
  omega

theorem source_valence_ge_three (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Bool) : 3 ≤ ((family P (!i)).subgroupOf (family P i)).index := by
  have he : (family P (!i)).subgroupOf (family P i) = B.subgroupOf (family P i) := by
    rw [←inf_subgroupOf_right]
    have hi : family P (!i) ⊓ family P i = B := by
      cases i
      · exact (inf_comm _ _).trans h.intersection
      · exact h.intersection
    rw [hi]
  rw [he]
  cases i
  · exact source_borel_index_ge_three (Classical.choice (h.local_data 0)) (hS 0)
  · exact source_borel_index_ge_three (Classical.choice (h.local_data 1)) (hS 1)
/-- The source graph has a first nonregular path through its marked Borel edge.
All shorter paths are regular at both ends, and transitivity through this length
holds in both vertex orbits. -/
theorem source_first_nonregular_path (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B) :
    ∃ n : ℕ,
      (∀ k < n+1, ∀ v : Vertex (family P), ∀ p : BasedWalk (graph (family P)) k v,
        p.Nonbacktracking → Regular (A := G) p) ∧
      (∀ v : Vertex (family P), ∀ k ≤ n+1, RootPathTransitive (graph (family P)) G v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (family P)) (n+1) (base (family P) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p ∧
        base (family P) false ∈ p.vertices ∧ base (family P) true ∈ p.vertices := by
  let := finite_endpoints h
  exact exists_first_nonregular_path_on_base_edge (family P) (source_valence_ge_three h hS)

/-- The first nonregular source path supplies its own transitivity premise
for the literal 6.7 supplement and the complement choice in 6.8. -/
theorem source_exists_nonregular_path_complement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k) :
    ∃ n : ℕ, ∃ i : Bool, ∃ p : BasedWalk (graph (family P)) (n+1) (base (family P) i),
      p.Nonbacktracking ∧ ¬ RightRegular (A := G) p ∧
      (∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v (n+1)) ∧
      ∃ K : Subgroup G, K ≤ B ⊓ pathStabilizer (family P) p ∧
        Disjoint K (B.pCoreIn 2) ∧ K ⊔ B.pCoreIn 2 = B ∧ Nat.Coprime 2 (Nat.card K) := by
  obtain ⟨n,_,ht,i,p,hp,hn,ha,hb⟩ := source_first_nonregular_path h hS
  exact ⟨n,i,p,hp,hn,fun v => ht v _ le_rfl,
    source_path_complement h hB hbranch (ht _ _ le_rfl) p hp ha hb⟩

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The constructed reduced F1.11 graph has an actual first nonregular path;
no path-transitivity, finiteness, valence or tree input is added. -/
theorem reduced_first_nonregular_path (h : HypothesisF11 L S) :
    ∃ n : ℕ,
      (∀ k < n+1, ∀ v : Vertex (reducedFamily L S), ∀ p : BasedWalk (graph (reducedFamily L S)) k v,
        p.Nonbacktracking → Regular (A := G₀ L S) p) ∧
      (∀ v : Vertex (reducedFamily L S), ∀ k ≤ n+1,
        RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (reducedFamily L S)) (n+1) (base (reducedFamily L S) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧
        base (reducedFamily L S) false ∈ p.vertices ∧ base (reducedFamily L S) true ∈ p.vertices :=
  source_first_nonregular_path (reduced_triple h) (reduced_vertex_sylow h)

/-- The original full Borel core and the literal reduced-to-original inclusion
are retained for the complement of the constructed nonregular path. -/
theorem reduced_exists_nonregular_path_original_complement (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k) :
    ∃ n : ℕ, ∃ i : Bool,
      ∃ p : BasedWalk (graph (reducedFamily L S)) (n+1) (base (reducedFamily L S) i),
      p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧
      (∀ v : Vertex (reducedFamily L S),
        RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1)) ∧
      ∃ K : Subgroup G,
        K ≤ B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype ∧
        Disjoint K ((commonBorel L S).pCoreIn 2) ∧
        K ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card K) := by
  obtain ⟨n,_,ht,i,p,hp,hn,ha,hb⟩ := reduced_first_nonregular_path h
  exact ⟨n,i,p,hp,hn,fun v => ht v _ le_rfl,
    reduced_path_original_complement h hbranch (ht _ _ le_rfl) p hp ha hb⟩
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
