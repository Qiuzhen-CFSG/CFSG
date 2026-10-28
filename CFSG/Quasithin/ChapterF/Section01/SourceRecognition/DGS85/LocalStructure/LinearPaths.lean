module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathLength

/-!
# Constructed nonregular paths for the original linear factors

Finite stabilizers give a first nonregular path through the marked base
edge, with all shorter paths regular and rooted transitivity through its
length in both vertex orbits. Actual linear quotient markings give the
binary branching and transport to its endpoint. Thus 6.7 supplies an
odd-order full-Borel complement fixing this path, and 6.8(a) puts its
two-core in the endpoint core and full neighbor kernel.

For the genuine reduced F1.11 application, the linear case of 6.1 constructs
the enlarged quotient from the ORIGINAL local factors. No path existence,
branching, transitivity, or enlarged-model premise remains. The lower bound
in 6.8(b) retains the still-open adjacent-core obstruction 6.5 explicitly.
The original Borel core and reduced-to-original inclusion are preserved.

Source: DGS, *Groups and Graphs* (1985), Part II, 3.4, pp.73--74,
and the linear case of 6.1 and 6.7--6.8, pp.118--124. The constructed length
is the first nonregular length r; no identification with s is asserted.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem not_neighbor_transitive_of_not_rightRegular
    {v : Vertex (family P)} {n : ℕ} (p : BasedWalk (graph (family P)) (n+1) v)
    (h : ¬ RightRegular (A := G) p) :
    ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val := by
  intro ht
  apply h
  intro x y hx hy
  exact ht ⟨x,hx.1⟩ ⟨y,hy.1⟩ hx.2 hy.2

/-- Linear quotient markings supply the branching and endpoint action of an
actual first nonregular path. Its core and full-Borel complement require no
extra path-existence or transitivity hypothesis. -/
theorem source_exists_linear_nonregular_path (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (graphLocalGroup (family P) (base (family P) i) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) i))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (K i)) :
    ∃ n : ℕ,
      (∀ k < n+1, ∀ v : Vertex (family P), ∀ p : BasedWalk (graph (family P)) k v,
        p.Nonbacktracking → Regular (A := G) p) ∧
      (∀ v : Vertex (family P), ∀ k ≤ n+1, RootPathTransitive (graph (family P)) G v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (family P)) (n+1) (base (family P) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p ∧
        base (family P) false ∈ p.vertices ∧ base (family P) true ∈ p.vertices ∧
        (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint ∧
        ∃ D : Subgroup G, D ≤ B ⊓ pathStabilizer (family P) p ∧
          Disjoint D (B.pCoreIn 2) ∧ D ⊔ B.pCoreIn 2 = B ∧ Nat.Coprime 2 (Nat.card D) := by
  obtain ⟨n,hshort,ht,i,p,hp,hn,ha,hb⟩ := source_first_nonregular_path h hS
  have hbranch := source_linear_branching h hB hS K e
  have he := source_linear_quotient_at h K e p.endpoint
  refine ⟨n,hshort,ht,i,p,hp,hn,ha,hb,?_,?_⟩
  · exact source_path_core_le_endpoint_core h hB hS hbranch (ht _ _ le_rfl) p hp he
      (not_neighbor_transitive_of_not_rightRegular p hn)
  · exact source_path_complement h hB hbranch (ht _ _ le_rfl) p hp ha hb

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual reduced F1.11 application constructs its linear nonregular path
and complement, keeping the original full Borel core and literal inclusion.
The original local linear quotients construct the enlarged models; the
source 6.5 obstruction remains an explicit input. -/
theorem reduced_exists_linear_long_path (h : HypothesisF11 L S)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i))
    (hob : ∀ a b : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj a b →
      ¬ stabilizer (reducedFamily L S) a ≤ normalizer
        ((Q (reducedFamily L S) b ⊓ Q (reducedFamily L S) a : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    ∃ n : ℕ, 4 ≤ n+1 ∧
      (∀ k < n+1, ∀ v : Vertex (reducedFamily L S), ∀ p : BasedWalk (graph (reducedFamily L S)) k v,
        p.Nonbacktracking → Regular (A := G₀ L S) p) ∧
      (∀ v : Vertex (reducedFamily L S), ∀ k ≤ n+1,
        RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (reducedFamily L S)) (n+1) (base (reducedFamily L S) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧
        ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype).pCoreIn 2 ≤
          (Q (reducedFamily L S) p.endpoint).map (G₀ L S).subtype ∧
        ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype).pCoreIn 2 ≤
          (U (reducedFamily L S) p.endpoint).map (G₀ L S).subtype ∧
        ∃ D : Subgroup G,
          D ≤ B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype ∧
          Disjoint D ((commonBorel L S).pCoreIn 2) ∧
          D ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card D) := by
  let eSL (i : Bool) : Matrix.SpecialLinearGroup (Fin 2) (K i) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let eGraph (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  obtain ⟨n,hshort,ht,i,p,hp,hn,ha,hb,hcore,_⟩ :=
    source_exists_linear_nonregular_path (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) K eGraph
  refine ⟨n,source_path_length_ge_four_of_core (reduced_triple h) (reduced_borel_core_sylow h)
    p hp hcore hob,hshort,ht,i,p,hp,hn,?_,?_,?_⟩
  · rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
    exact map_mono hcore
  · rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
    exact map_mono (hcore.trans ((source_Z_Q_U (reduced_triple h) p.endpoint).2))
  · exact reduced_path_original_complement h
      (source_linear_branching (reduced_triple h) (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) K eGraph) (ht _ _ le_rfl) p hp ha hb
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
