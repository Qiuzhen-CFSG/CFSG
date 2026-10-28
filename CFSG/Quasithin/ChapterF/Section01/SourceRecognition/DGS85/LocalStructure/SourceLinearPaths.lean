module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnconditionalLinearPaths

/-!
# DGS 6.8 at the literal source parameter

The minimum is taken over the book's paths in both vertex orbits. The
endpoint quotient marking, source transitivity through s, full-catalogue
branching, and unconditional adjacent-core obstruction supply both 6.8
conclusions at every eligible path. Original linear endpoint markings also
construct such a simple path and retain the full-Borel complement and
literal reduced-to-original inclusion.

Source: DGS, *Groups and Graphs* (1985), pp.73--74 and 6.8, pp.123--124.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "s₀" => sourceS (P := fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Both conclusions of 6.8 at the actual source s, using only the endpoint
linear marking from its statement. The opposite endpoint may belong to any family. -/
theorem reduced_sourceS_linear_path (h : HypothesisF11 L S)
    {n : ℕ} (hs : n+1 = s₀) {v : Vertex F}
    (p : BasedWalk (graph F) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup F p.endpoint ⧸ pCore 2 (graphLocalGroup F p.endpoint)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hn : ¬ RightRegular (A := G₀ L S) p) :
    ((pathStabilizer F p).map (G₀ L S).subtype).pCoreIn 2 ≤
      (U F p.endpoint).map (G₀ L S).subtype ∧ 4 ≤ s₀ := by
  have hnot : ¬ ∀ x y : (graph F).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer F p, g • x.val = y.val := by
    intro hh
    apply hn
    intro x y hx hy
    exact hh ⟨x,hx.1⟩ ⟨y,hy.1⟩ hx.2 hy.2
  obtain ⟨hc,hl⟩ := reduced_projective_path_conclusions h (reduced_rankOne_branching h)
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) v hs.le)
    p hp e hnot (reduced_graph_core_obstruction h)
  exact ⟨hc,hs ▸ hl⟩

/-- The literal book-path form of 6.8, including its closed-path convention.
The fixer is computed in the original completion, and the supplied quotient
is the actual endpoint quotient. -/
theorem reduced_sourceS_source_linear_path (h : HypothesisF11 L S)
    {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : NoncommutingProfile.IsSourcePath p) (hl : p.length = s₀)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hn : ¬ RightRegular (A := G₀ L S) (ofWalk p)) :
    ((Theory.GroupTheory.WeakBNPair.RegularTree.pathFixer (X := G₀ L S) p).map
      (G₀ L S).subtype).pCoreIn 2 ≤ (U F b).map (G₀ L S).subtype ∧ 4 ≤ s₀ := by
  have hnb := sourceS_nonregular_nonbacktracking (reduced_triple h)
    (reduced_vertex_sylow h) p hp hl hn
  obtain ⟨n,he⟩ := Nat.exists_eq_succ_of_ne_zero
    (show p.length ≠ 0 by
      have := (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).1
      omega)
  let q : BasedWalk (graph F) (n+1) a :=
    Eq.rec (motive := fun k _ => BasedWalk (graph F) k a) (ofWalk p) he
  have hq : q.vertices = (ofWalk p).vertices := BasedWalk.vertices_cast he _
  have hqnb : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast he _).mpr hnb
  have hqend : q.endpoint = b := (BasedWalk.endpoint_cast he _).trans (endpoint_ofWalk p)
  have hqnot : ¬ RightRegular (A := G₀ L S) q := by
    intro hr
    have hr' : RightRegular (A := G₀ L S) (ofWalk p) := by
      have hsame {n k : ℕ} {x y : Vertex F} (q : BasedWalk (graph F) n x)
          (r : BasedWalk (graph F) k y) (hv : q.vertices = r.vertices)
          (hh : RightRegular (A := G₀ L S) q) : RightRegular (A := G₀ L S) r := by
        have hlen : n = k := by
          have hv' := congrArg List.length hv
          simp only [BasedWalk.length_vertices] at hv'
          omega
        subst k
        exact rightRegular_of_vertices_eq q r hv hh
      exact hsame q (ofWalk p) hq hr
    exact hn hr'
  have eq : (graphLocalGroup F q.endpoint ⧸ pCore 2 (graphLocalGroup F q.endpoint)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := by rw [hqend]; exact e
  have hc := reduced_sourceS_linear_path h (he.symm.trans hl) q hqnb eq hqnot
  have hf : pathStabilizer F q = Theory.GroupTheory.WeakBNPair.RegularTree.pathFixer
      (X := G₀ L S) p := by
    calc
      pathStabilizer F q = pathStabilizer F (ofWalk p) := by
        ext g
        change (∀ z ∈ q.vertices, g • z = z) ↔ (∀ z ∈ (ofWalk p).vertices, g • z = z)
        rw [hq]
      _ = _ := pathStabilizer_ofWalk (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) p
  rwa [hf,hqend] at hc

/-- Original linear factors supply the source-minimal simple path, both actual
endpoint-core inclusions, the bound s≥4 and the original full-Borel complement. -/
theorem reduced_sourceS_linear_path_complement (h : HypothesisF11 L S)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i)) :
    4 ≤ s₀ ∧ ∃ n : ℕ, n+1 = s₀ ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph F) (n+1) (base F i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧ p.toWalk.IsPath ∧
        ((pathStabilizer F p).map (G₀ L S).subtype).pCoreIn 2 ≤
          (Q F p.endpoint).map (G₀ L S).subtype ∧
        ((pathStabilizer F p).map (G₀ L S).subtype).pCoreIn 2 ≤
          (U F p.endpoint).map (G₀ L S).subtype ∧
        ∃ D : Subgroup G,
          D ≤ B₀ L S ⊓ (pathStabilizer F p).map (G₀ L S).subtype ∧
          Disjoint D ((commonBorel L S).pCoreIn 2) ∧
          D ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card D) := by
  obtain ⟨n,hs,i,p,hp,hn,hsimp,hcomp⟩ := reduced_sourceS_path_complement h
  let eSL (j : Bool) : Matrix.SpecialLinearGroup (Fin 2) (K j) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K j) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K j))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eGraph (j : Bool) := (reduced_graphLinearQuotient h j (e j)).trans (eSL j).symm
  let ep := source_linear_quotient_at (reduced_triple h) K eGraph p.endpoint
  have hnot : ¬ ∀ x y : (graph F).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer F p, g • x.val = y.val := by
    intro hh
    apply hn
    intro x y hx hy
    exact hh ⟨x,hx.1⟩ ⟨y,hy.1⟩ hx.2 hy.2
  have hc := source_path_core_le_endpoint_core (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (reduced_rankOne_branching h)
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) _ hs.le) p hp ep hnot
  have hl := source_path_length_ge_four_of_core (reduced_triple h)
    (reduced_borel_core_sylow h) p hp hc (reduced_graph_core_obstruction h)
  refine ⟨hs ▸ hl,n,hs,i,p,hp,hn,hsimp,?_,?_,hcomp⟩
  · rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
    exact map_mono hc
  · rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
    exact map_mono (hc.trans (source_Z_Q_U (reduced_triple h) p.endpoint).2)

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
