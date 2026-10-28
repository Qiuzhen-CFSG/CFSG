module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.RemainingOrbit
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The actual graph on the fifteen cosets

Two cosets are adjacent when the intersection of their stabilizers has order four. This gives symmetry and invariance directly. The source suborbits identify adjacency with the six-point orbit and nonadjacency off the diagonal with the eight-point orbit.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G]

private theorem coset_stabilizer_card (H:Subgroup G) (hH:Nat.card H=24) (q:G⧸H):
    Nat.card (MulAction.stabilizer G q)=24 := by
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G (((1:G):G⧸H)) q
  rw [←hg,MulAction.stabilizer_smul_eq_stabilizer_map_conj,MulAction.stabilizer_quotient,
    card_map_of_injective (MulAut.conj g).injective,hH]

theorem coset_orbit_stabilizer_card (H:Subgroup G) (q:G⧸H):
    Nat.card (MulAction.orbit H q)*Nat.card (H⊓MulAction.stabilizer G q:Subgroup G)=Nat.card H := by
  have he:MulAction.stabilizer H q=(H⊓MulAction.stabilizer G q).subgroupOf H := by
    ext x
    change x.val • q=q ↔ x.val∈H ∧ x.val • q=q
    simp only [x.property,true_and]
  have hh:=Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H q)
  rwa [Nat.card_prod,he,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hh

def cosetGraph (H:Subgroup G) (hH:Nat.card H=24):SimpleGraph (G⧸H) where
  Adj x y := Nat.card (MulAction.stabilizer G x⊓MulAction.stabilizer G y:Subgroup G)=4
  symm := ⟨by intro x y hh; rwa [inf_comm]⟩
  loopless := ⟨by
    intro x hh
    change Nat.card (MulAction.stabilizer G x⊓MulAction.stabilizer G x:Subgroup G)=4 at hh
    rw [inf_idem,coset_stabilizer_card H hH x] at hh
    norm_num at hh⟩

theorem cosetGraph_invariant (H:Subgroup G) (hH:Nat.card H=24) (g:G) (x y:G⧸H):
    (cosetGraph H hH).Adj (g • x) (g • y)↔(cosetGraph H hH).Adj x y := by
  change Nat.card (MulAction.stabilizer G (g • x)⊓MulAction.stabilizer G (g • y):Subgroup G)=4 ↔ _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,card_map_of_injective (MulAut.conj g).injective]
  rfl

theorem cosetGraph_base_adj_iff (H:Subgroup G) (hH:Nat.card H=24) (b c:G⧸H)
    (h8:Nat.card (MulAction.orbit H b)=8)
    (hcover:MulAction.orbit H c=(({((1:G):G⧸H)}:Set (G⧸H))∪MulAction.orbit H b)ᶜ)
    (h6:Nat.card (MulAction.orbit H c)=6) (q:G⧸H):
    (cosetGraph H hH).Adj ((1:G):G⧸H) q↔q∈MulAction.orbit H c := by
  have ho:=coset_orbit_stabilizer_card H q
  rw [hH] at ho
  by_cases hq:q∈MulAction.orbit H c
  · have he:Nat.card (MulAction.orbit H q)=6 := by rw [MulAction.orbit_eq_iff.mpr hq,h6]
    rw [he] at ho
    constructor
    · exact fun _=>hq
    · intro _
      change Nat.card (MulAction.stabilizer G ((1:G):G⧸H)⊓MulAction.stabilizer G q:Subgroup G)=4
      rw [MulAction.stabilizer_quotient]
      omega
  · have hh:q=((1:G):G⧸H) ∨ q∈MulAction.orbit H b := by
      simpa only [hcover,Set.mem_compl_iff,Set.mem_union,Set.mem_singleton_iff,not_not] using hq
    constructor
    · intro ha
      rcases hh with rfl|hh
      · exact False.elim ((cosetGraph H hH).irrefl ha)
      · have he:Nat.card (MulAction.orbit H q)=8 := by rw [MulAction.orbit_eq_iff.mpr hh,h8]
        rw [he] at ho
        change Nat.card (MulAction.stabilizer G ((1:G):G⧸H)⊓MulAction.stabilizer G q:Subgroup G)=4 at ha
        rw [MulAction.stabilizer_quotient] at ha
        omega
    · exact fun hh=>False.elim (hq hh)

theorem cosetGraph_base_nonadj_iff (H:Subgroup G) (hH:Nat.card H=24) (b c:G⧸H)
    (hb:b≠((1:G):G⧸H)) (h8:Nat.card (MulAction.orbit H b)=8)
    (hcover:MulAction.orbit H c=(({((1:G):G⧸H)}:Set (G⧸H))∪MulAction.orbit H b)ᶜ)
    (h6:Nat.card (MulAction.orbit H c)=6) (q:G⧸H):
    (q≠((1:G):G⧸H) ∧ ¬(cosetGraph H hH).Adj ((1:G):G⧸H) q)↔q∈MulAction.orbit H b := by
  rw [cosetGraph_base_adj_iff H hH b c h8 hcover h6,hcover]
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_singleton_iff,not_not]
  have hn:q∈MulAction.orbit H b→q≠((1:G):G⧸H) := by
    rintro ⟨g,hg⟩ he
    have hfix:g.val • (((1:G):G⧸H))=((1:G):G⧸H) := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [MulAction.stabilizer_quotient]
      exact g.property
    exact hb ((MulAction.injective g.val) ((hg.trans he).trans hfix.symm))
  tauto
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
