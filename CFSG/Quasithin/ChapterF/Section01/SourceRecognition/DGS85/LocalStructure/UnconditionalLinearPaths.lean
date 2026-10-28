module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# The linear 6.8 path with the actual 6.5 obstruction

`LinearPaths.reduced_exists_linear_long_path` leaves the adjacent-core
obstruction as an explicit argument because it predates the full graph
obstruction.  The latter is now proved for the original F.1.1 graph, including
the degree-one PSU₃(2) replacement branch.  This module performs the literal
source application: it supplies that theorem at every edge and retains the
original endpoint quotient markings, the first nonregular path, and the
full-Borel complement.

Source: DGS, *Groups and Graphs* (1985), 6.5 and 6.7--6.8, pp.121--124.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual reduced linear path application, with DGS 6.5 discharged by
the unconditional full graph obstruction.  The output keeps both endpoint
fields and the original Borel complement from the source theorem. -/
theorem reduced_exists_linear_long_path_unconditional (h : HypothesisF11 L S)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i)) :
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
  apply reduced_exists_linear_long_path h K e
  intro a b hab
  exact reduced_graph_core_obstruction h a b hab

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
