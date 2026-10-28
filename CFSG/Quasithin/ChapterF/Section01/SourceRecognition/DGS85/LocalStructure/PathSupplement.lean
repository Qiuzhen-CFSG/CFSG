module
public import Theory.GroupTheory.AmalgamGraph.PathSupplement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity

/-!
# DGS path supplements in the original and reduced graphs

Apply the path-index argument to the actual finite edge stabilizers. The
reduced F1.11 pair discharges the normal Sylow hypothesis. Mapping through
its literal inclusion gives B₀=(B₀ intersect G_gamma)O₂(B), with the original
full Borel core retained. The model branching and Chapter 3 path transitivity
premises remain explicit, so these are conditional 6.7 applications.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.7, p.123, and the reduced triple on pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Conditional source 6.7 at any edge in the actual path. -/
theorem source_path_edge_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v a b : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (hab : (graph (family P)).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) :
    ((stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G) : Set G) =
      (pathStabilizer (family P) p : Set G) *
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 : Set G) := by
  let := finite_endpoints h
  exact pathStabilizer_mul_core (family P) 2
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl)
    hbranch ht p hp hab ha hb (source_edge_core_sylow h hB hab)

/-- Literal B=(B intersect G_gamma)O₂(B), for a path containing the marked edge. -/
theorem source_path_borel_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (family P) false ∈ p.vertices) (hb : base (family P) true ∈ p.vertices) :
    (B : Set G) = ((B ⊓ pathStabilizer (family P) p : Subgroup G) : Set G) *
      (B.pCoreIn 2 : Set G) := by
  have hadj : (graph (family P)).Adj (base (family P) false) (base (family P) true) :=
    ⟨Bool.false_ne_true, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have he : stabilizer (family P) (base (family P) false) ⊓
      stabilizer (family P) (base (family P) true) = B := by
    change MulAction.stabilizer G (Subgroup.CosetGeometry.base _ false) ⊓
      MulAction.stabilizer G (Subgroup.CosetGeometry.base _ true) = B
    rw [Subgroup.CosetGeometry.stabilizer_base, Subgroup.CosetGeometry.stabilizer_base]
    exact h.intersection
  have hfix := pathStabilizer_le_edge (family P) p ha hb
  rw [he] at hfix
  rw [inf_eq_right.mpr hfix]
  simpa only [he] using source_path_edge_product h hB hbranch ht p hp hadj ha hb

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced F1.11 application discharges normal Sylow and all finiteness
premises, retaining the exact local branching and Chapter 3 transitivity inputs. -/
theorem reduced_path_borel_product (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (reducedFamily L S) false ∈ p.vertices)
    (hb : base (reducedFamily L S) true ∈ p.vertices) :
    ((B₀ L S).subgroupOf (G₀ L S) : Set (G₀ L S)) =
      (((B₀ L S).subgroupOf (G₀ L S) ⊓ pathStabilizer (reducedFamily L S) p :
        Subgroup (G₀ L S)) : Set (G₀ L S)) *
      (((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2 : Set (G₀ L S)) :=
  source_path_borel_product (reduced_triple h) (reduced_borel_core_sylow h)
    hbranch ht p hp ha hb

/-- Transport through the original inclusion preserves the full original Borel
core, rather than replacing it with the original Sylow S. -/
theorem reduced_path_original_product (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (reducedFamily L S) false ∈ p.vertices)
    (hb : base (reducedFamily L S) true ∈ p.vertices) :
    (B₀ L S : Set G) =
      ((B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype :
        Subgroup G) : Set G) * ((commonBorel L S).pCoreIn 2 : Set G) := by
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have he := reduced_path_borel_product h hbranch ht p hp ha hb
  have hm := congrArg (Set.image (G₀ L S).subtype) he
  rw [Set.image_mul] at hm
  change (((B₀ L S).subgroupOf (G₀ L S)).map (G₀ L S).subtype : Set G) =
    ((((B₀ L S).subgroupOf (G₀ L S) ⊓ pathStabilizer (reducedFamily L S) p).map
      (G₀ L S).subtype) : Set G) *
    (((((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype) : Set G) at hm
  rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hBG,
    ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hBG, B₀_core h] at hm
  exact hm
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
