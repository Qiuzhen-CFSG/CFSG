module

public import Theory.AlgebraicGroup.Tori.Character.Basis
public import Theory.AlgebraicGroup.Tori.Maximal

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/- A useful reduction of the missing core: it is enough to construct a
connected closed subgroup whose point group is commutative and whose points
are all semisimple.  The character-basis theorem then identifies that subgroup
with a torus, after which maximality is formal. -/
public theorem semisimple_element_mem_maximalTorus_of_connected_commutative_semisimple_closedSubgroup
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G)
    (hSconn : Variety.IsConnected S.carrierVariety)
    (hScomm : IsMulCommutative (Variety.Point S.carrierVariety))
    (hSsemi : ∀ x : Variety.Point S.carrierVariety,
      IsSemisimpleElement S.carrierVariety x)
    (g : Variety.Point G) (hgS : g ∈ S.toSubgroup) :
    ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧ g ∈ T.toSubgroup := by
  have hStorus : IsSubtorus S :=
    isTorus_of_isConnected_isMulCommutative_all_semisimple
      hSconn hScomm hSsemi
  obtain ⟨T, hT, hST⟩ := exists_maximalTorus_containing S hStorus
  exact ⟨T, hT, hST hgS⟩

/- The cyclic Zariski closure is always commutative.  Thus, when the two
  genuinely geometric hypotheses (connectedness of the closure and
  semisimplicity of all of its points) are available, the closure itself is
  a containing torus and the maximal-torus extension is immediate.  Keeping
  this bridge explicit records exactly where the unconditional source proof
  still needs additional algebraic-group geometry. -/
public theorem element_mem_maximalTorus_of_connected_semisimple_zpowers_closure
    {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G)
    (hclosure_conn :
      Variety.IsConnected
        (subgroupZariskiClosure G (Subgroup.zpowers g)).carrierVariety)
    (hclosure_semi : ∀ x : Variety.Point
        (subgroupZariskiClosure G (Subgroup.zpowers g)).carrierVariety,
      IsSemisimpleElement
        (subgroupZariskiClosure G (Subgroup.zpowers g)).carrierVariety x) :
    ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧ g ∈ T.toSubgroup := by
  let C : ClosedSubgroup G := subgroupZariskiClosure G (Subgroup.zpowers g)
  have hCcomm : IsMulCommutative (Variety.Point C.carrierVariety) := by
    rw [isMulCommutative_iff]
    intro a b
    apply C.inclusion_injective
    rw [map_mul, map_mul]
    change (C.pointEquiv a).val * (C.pointEquiv b).val =
      (C.pointEquiv b).val * (C.pointEquiv a).val
    exact subgroupZariskiClosure_zpowers_isAbelian g
      (C.pointEquiv a).val (C.pointEquiv b).val
      (C.pointEquiv a).property (C.pointEquiv b).property
  have hgC : g ∈ C.toSubgroup := by
    change g ∈ closure (Subgroup.zpowers g : Set (Variety.Point G))
    exact subset_closure (Subgroup.mem_zpowers g)
  exact semisimple_element_mem_maximalTorus_of_connected_commutative_semisimple_closedSubgroup
    C hclosure_conn hCcomm hclosure_semi g hgC

set_option warningAsError false in
public theorem theorem_1_4_2_e
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G)
    (g : Variety.Point G) (hg : IsSemisimpleElement G g) :
    ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧ g ∈ T.toSubgroup := by sorry

end Theory.AlgebraicGroup
