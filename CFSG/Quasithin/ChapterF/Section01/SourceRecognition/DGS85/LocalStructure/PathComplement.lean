module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathSupplement
public import Theory.GroupTheory.AmalgamGraph.PathComplement

/-!
# A Borel complement fixing the chosen path

The actual path supplement permits Schur--Zassenhaus inside the path
fixer. The resulting odd-order complement lies in the full Borel and fixes
all path vertices. The reduced F1.11 application transports that complement
through the original inclusion and retains O₂ of the original full Borel.

This is the choice of K used at the start of DGS 6.8, conditional on the
Chapter 3 transitivity and model branching inputs to 6.7. It does not assert
the endpoint kernel containment or the lower bound s >= 4 of 6.8.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.0 and 6.7--6.8, pp.118 and 123.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The complement in 6.0 may be chosen inside the path fixer, as used in 6.8. -/
theorem source_path_complement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (family P) false ∈ p.vertices) (hb : base (family P) true ∈ p.vertices) :
    ∃ K : Subgroup G, K ≤ B ⊓ pathStabilizer (family P) p ∧
      Disjoint K (B.pCoreIn 2) ∧ K ⊔ B.pCoreIn 2 = B ∧ Nat.Coprime 2 (Nat.card K) := by
  let := (Classical.choice (h.local_data 0)).finite_P
  have hBP : B ≤ P 0 := h.intersection.ge.trans inf_le_left
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hn : B ≤ normalizer (B.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 B).le_normalizer_map B.subtype
  have hgen : (B ⊓ pathStabilizer (family P) p) ⊔ B.pCoreIn 2 = B := by
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hn)]
    exact (source_path_borel_product h hB hbranch ht p hp ha hb).symm
  exact exists_complement_le_of_core_supplement 2 B _ inf_le_left hB hgen

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The chosen complement fixes the actual reduced path. Its image in the
original completion complements the original full Borel core inside B₀. -/
theorem reduced_path_original_complement (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (reducedFamily L S) false ∈ p.vertices)
    (hb : base (reducedFamily L S) true ∈ p.vertices) :
    ∃ K : Subgroup G,
      K ≤ B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype ∧
      Disjoint K ((commonBorel L S).pCoreIn 2) ∧
      K ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card K) := by
  obtain ⟨D,hD,hd,hg,hcard⟩ := source_path_complement (reduced_triple h)
    (reduced_borel_core_sylow h) hbranch ht p hp ha hb
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hcore : (((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (commonBorel L S).pCoreIn 2 := by
    rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le hBG, B₀_core h]
  refine ⟨D.map (G₀ L S).subtype, ?_, ?_, ?_, ?_⟩
  · have hm := map_mono (f := (G₀ L S).subtype) hD
    rwa [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective, map_subgroupOf_eq_of_le hBG] at hm
  · rw [← hcore]
    exact disjoint_map (G₀ L S).subtype_injective hd
  · have hm := congrArg (map (G₀ L S).subtype) hg
    rwa [Subgroup.map_sup, hcore, map_subgroupOf_eq_of_le hBG] at hm
  · rwa [card_map_of_injective (G₀ L S).subtype_injective]
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
