module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightData
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate

/-!
# Local geometry and splitting data for an order-eight separated closure

The centralizer of the selected noncentral involution is the index-two
normalizer of the transported elementary eight. An outside conjugate is
another elementary eight in that centralizer, and contains an involution
which does not centralize the original eight.

The normality of the join would otherwise contradict the absence of normal
elementary eights. This is the outside-involution construction in
Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The original involution centralizer contains every conjugate of the
selected elementary closure by an element of the Sylow subgroup. -/
public theorem conjugate_closure_le_centralizer
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S) (d : CentralizerSetup S W i) (t : S) :
    (closureInSylow d).map (MulAut.conj t).toMonoidHom ≤
      centralizer ({i} : Set S) := by
  let C := centralizer ({i} : Set S)
  let : C.Normal := normal_of_index_eq_two
    (centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC)
  rintro _ ⟨x, hx, rfl⟩
  exact (inferInstance : C.Normal).conj_mem x (closureInSylow_le_centralizer d hx) t

/-- Every outside conjugate of the elementary eight supplies an involution
outside its centralizer, still inside the original involution centralizer. -/
public theorem exists_outside_conjugate_involution
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (t : S) (ht : t ∉ centralizer ({i} : Set S)) :
    ∃ x : S, x ∈ (closureInSylow d).map (MulAut.conj t).toMonoidHom ∧
      orderOf x = 2 ∧ x ∈ centralizer ({i} : Set S) ∧
      x ∉ centralizer (closureInSylow d : Set S) := by
  have hnorm := normalizer_closureInSylow_eq S W hW z hzW hzC hz i hiW hi hiC hno d hc
  let : IsElementaryAbelian 2 (closureInSylow d) := closureInSylow_elementary d
  obtain ⟨x, hx, hx2, hxC⟩ := exists_involution_in_conjugate_not_centralizing hno
    (closureInSylow d) (by rw [card_closureInSylow, hc])
    (by rw [hnorm]; exact centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC)
    t (by rwa [hnorm])
  exact ⟨x, hx, hx2,
    conjugate_closure_le_centralizer S W hW z hzW hzC hz i hiW hi hiC d t hx, hxC⟩

/-- The concrete output of the odd-action splitting. The plane is the
order-four moving factor, the fixed factor is centralized by the chosen
outside conjugate involution, and their product is the closure centralizer.
Existence of this structure is a separate mathematical assertion. -/
public structure LocalSplitting
    {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) (z : S) where
  plane : Subgroup S
  fixed : Subgroup S
  mover : S
  outside : S
  plane_elementary : IsElementaryAbelian 2 plane
  plane_card : Nat.card plane = 4
  plane_le : plane ≤ closureInSylow d
  plane_normalized : centralizer ({i} : Set S) ≤ normalizer (plane : Set S)
  product : plane ⊔ fixed = centralizer (closureInSylow d : Set S)
  disjoint : Disjoint plane fixed
  index : (centralizer (closureInSylow d : Set S)).relIndex
    (centralizer ({i} : Set S)) = 2
  involution_mem_fixed : i ∈ fixed
  central_not_mem_fixed : z ∉ fixed
  mover_outside : mover ∉ centralizer ({i} : Set S)
  outside_mem_conjugate : outside ∈
    (closureInSylow d).map (MulAut.conj mover).toMonoidHom
  outside_order : orderOf outside = 2
  outside_not_centralizing : outside ∉ centralizer (closureInSylow d : Set S)
  outside_centralizes_fixed : outside ∈ centralizer (fixed : Set S)

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
