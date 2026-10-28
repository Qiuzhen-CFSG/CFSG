module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter

/-!
# An order bound for the source path parameter

For valences three and five, there are 768 nonbacktracking six-paths from
an alpha vertex. If the first nonregular source length were at least six,
the alpha stabilizer would act transitively on those paths. Orbit–stabilizer
would then make 768 divide its order 1152, a contradiction.

This proves the upper bound s ≤ 5 used in the field-four branch. It does
not prove the lower bound, existence of a regular six-path, or the maximum
regular length.

Source: Delgado–Goldschmidt–Stellmacher, Groups and Graphs (1985),
path transitivity pp.73–74 and the order argument in (10.9), p.163.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem six_path_count (F : Bool → Subgroup G)
    (hthree : ((F true).subgroupOf (F false)).index = 3)
    (hfive : ((F false).subgroupOf (F true)).index = 5) :
    Nat.card {p : BasedWalk (graph F) 6 (base F false) // p.Nonbacktracking} = 768 := by
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hc := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> decide)
  have hf : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w h
    have hn := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hcount := BasedWalk.card_nonbacktracking_succ (graph F)
    (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hf hc 5 (base F false)
  change Nat.card {p : BasedWalk (graph F) (5+1) (base F false) // p.Nonbacktracking} = _
  rw [hcount]
  have hbtype : (base F false).type = false := rfl
  rw [hbtype]
  decide

/-- In the (3,5) source action, alpha order 1152 bounds the first failing
path length by five. No completion isomorphism or prescribed path is assumed. -/
theorem sourceS_le_five_of_three_five_orders
    (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hthree : (((family P) true).subgroupOf ((family P) false)).index = 3)
    (hfive : (((family P) false).subgroupOf ((family P) true)).index = 5)
    (hcard : Nat.card ((family P) false) = 1152) : sourceS (P := P) ≤ 5 := by
  by_contra hs
  have ht := sourceS_transitive h hS (base (family P) false) (by omega : 6 ≤ sourceS (P := P))
  have hc := six_path_count (family P) hthree hfive
  have hn : Nonempty {p : BasedWalk (graph (family P)) 6 (base (family P) false) // p.Nonbacktracking} :=
    (Nat.card_pos_iff.mp (hc ▸ (by decide : 0 < 768))).1
  obtain ⟨p,hp⟩ := hn
  have ho := card_paths_mul_card_fixer (family P) ht p hp
  rw [hc,stabilizer,Subgroup.CosetGeometry.stabilizer_base,hcard] at ho
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85
