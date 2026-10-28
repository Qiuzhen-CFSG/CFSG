module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource

/-!
# Thickness on the strict source tree

The strict `(6,7)` profile is proved on the universal tree, while the source
valence estimate is stated on the reduced graph.  The original b=1 covering
has a bijection on every neighbor set, so it transports the valence bound
without changing the endpoint or Borel maps.  This supplies exactly the
third-neighbor premise used by the Chapter 14 path-root construction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

open Reduction NoncommutingProfile

universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every marked endpoint has a neighbor outside the opposite base vertex and
the chosen reflected opposite vertex. -/
theorem strict_path_thickness_source
    (h : HypothesisF11 L S)
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (_htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) :
    ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
      z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) := by
  intro i
  let A := reducedAmalgam L S
  let E := Universal.cosetFamily A
  let v : Vertex E := base E i
  let a : Vertex E := base E (!i)
  let b : Vertex E := t i • a
  let cov := NoncommutingProfile.bOne_tree_cover h
  have hred (w : Vertex (reducedFamily L S)) :
      3 ≤ Nat.card ((graph (reducedFamily L S)).neighborSet w) := by
    rw [card_neighbors_of_indices (reducedFamily L S)
      (fun j => ((reducedFamily L S (!j)).subgroupOf (reducedFamily L S j)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) w.type
  have hcard : Nat.card ((sourceGraph A).neighborSet v) =
      Nat.card ((graph (reducedFamily L S)).neighborSet (cov.vertex v)) := by
    exact Nat.card_congr (Equiv.ofBijective (cov.hom.mapNeighborSet v)
      (cov.neighbor_bijective v))
  have hv : 3 ≤ Nat.card ((sourceGraph A).neighborSet v) := by
    rw [hcard]
    exact hred _
  let : Finite ((sourceGraph A).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by omega)
  have ha : a ∈ (sourceGraph A).neighborSet v := by
    change (sourceGraph A).Adj (base E i) (base E (!i))
    exact ⟨by change i ≠ !i; cases i <;> decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hb : b ∈ (sourceGraph A).neighborSet v := by
    change (sourceGraph A).Adj (base E i) (t i • base E (!i))
    have hab : (sourceGraph A).Adj (t i • base E i) (t i • base E (!i)) :=
      (Subgroup.CosetGeometry.translationGraphIso E (t i)).toHom.map_adj
        (show (sourceGraph A).Adj (base E i) (base E (!i)) from
          ⟨by change i ≠ !i; cases i <;> decide,
            Subgroup.CosetGeometry.incident_base _ _ _⟩)
    have hfixi : t i • base E i = base E i := htfix i
    rw [hfixi] at hab
    exact hab
  have hpair : ({a, b} : Set (Vertex E)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (Vertex E))
  have hv' : 3 ≤ ((sourceGraph A).neighborSet v).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact hv
  have hgt : ({a, b} : Set (Vertex E)).ncard <
      ((sourceGraph A).neighborSet v).ncard := by
    omega
  obtain ⟨z, hz, hzne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hgt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzne
  exact ⟨z, hz, hzne.1, hzne.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
