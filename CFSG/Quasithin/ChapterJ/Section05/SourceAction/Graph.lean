module
public import CFSG.Quasithin.ChapterJ.Section05.SourceAction.RankThree
public import Theory.GroupAction.SwappedOrbital.Connected

/-!
# The original rank-three orbital graph

The original q exchanges its edge, defining an undirected G-invariant graph
on the unchanged G/F. Its neighbor set at F is exactly the first F-orbit.
Rank three gives strong regularity, primitivity gives connectedness, and
double counting supplies the equation used in the J.5.5 building argument.
Source: Aschbacher–Smith J.5.4(3)–J.5.5(1), pp.446–447.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F)
  (hswap:q•(q•basePoint F)=basePoint F)

omit [Finite G] in
include hq in
theorem base_ne_first : basePoint F≠q•basePoint F := by
  intro h
  exact hq ((stabilizer_quotient F).le h.symm)

/-- The actual self-paired first orbital on G/F. -/
def sourceGraph : SimpleGraph (Cosets F) :=
  SwappedOrbital.graph (basePoint F) (q•basePoint F) (base_ne_first F q hq) q rfl hswap

omit [Finite G] in
theorem sourceGraph_adj_smul (g:G) (x y:Cosets F) :
    (sourceGraph F q hq hswap).Adj (g•x) (g•y) ↔
      (sourceGraph F q hq hswap).Adj x y :=
  SwappedOrbital.adj_smul_iff _ _ _ _ _ _ g x y

omit [Finite G] in
theorem sourceGraph_neighbor_base :
    (sourceGraph F q hq hswap).neighborSet (basePoint F)=orbit F (q•basePoint F) :=
  (SwappedOrbital.neighbor_base _ _ _ _ _ _).trans (orbit_stabilizer_base F _)

attribute [local instance] Classical.propDecidable

omit [Finite G] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two common-neighbor numbers are constant on their original orbitals. -/
theorem RudvalisAction.stronglyRegular {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) [Fintype (Cosets F)] :
    (sourceGraph F q hq hswap).IsSRGWith 4060 1755
      (Nat.card ((sourceGraph F q hq hswap).commonNeighbors (basePoint F) (q•basePoint F)))
      (Nat.card ((sourceGraph F q hq hswap).commonNeighbors (basePoint F) (g•basePoint F))) := by
  have hh:=SwappedOrbital.stronglyRegular (basePoint F) (q•basePoint F)
    (base_ne_first F q hq) q rfl hswap (g•basePoint F) (by
      exact (orbit_stabilizer_base (G:=G) F _).trans
        (h.partition.trans (congrArg (fun O:Set (Cosets F)=>(({basePoint F}:Set (Cosets F))∪O)ᶜ)
          (orbit_stabilizer_base (G:=G) F _).symm)))
  have hd:(sourceGraph F q hq hswap).degree (basePoint F)=1755:=by
    rw [← SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.setCongr (sourceGraph_neighbor_base F q hq hswap))).trans h.first_length
  have hk:=(hh.regular (basePoint F)).symm.trans hd
  rw [h.degree,hk] at hh
  exact hh

/-- The exact double-counting identity of J.5.5 before the building calculation. -/
theorem RudvalisAction.parameter_equation {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    1755*(1755-Nat.card ((sourceGraph F q hq hswap).commonNeighbors
      (basePoint F) (q•basePoint F))-1)=
      2304*Nat.card ((sourceGraph F q hq hswap).commonNeighbors
        (basePoint F) (g•basePoint F)) := by
  let : Fintype (Cosets F):=Fintype.ofFinite _
  have he:=(h.stronglyRegular F q hq hswap).param_eq _ (by decide)
  norm_num only [Nat.reduceSub] at he
  exact he

omit [Finite G] in
theorem RudvalisAction.connected {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    (sourceGraph F q hq hswap).Connected := by
  let : IsPreprimitive G (Cosets F):=h.primitive
  exact SwappedOrbital.connected _ _ _ _ _ _

/-- The nonadjacent common-neighbor number is positive. -/
theorem RudvalisAction.mu_pos {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    0<Nat.card ((sourceGraph F q hq hswap).commonNeighbors
      (basePoint F) (g•basePoint F)) := by
  let : Fintype (Cosets F):=Fintype.ofFinite _
  have hg:g•basePoint F∈(({basePoint F}:Set (Cosets F))∪orbit F (q•basePoint F))ᶜ:=
    h.partition ▸ mem_orbit_self _
  apply (h.stronglyRegular F q hq hswap).mu_pos_of_connected _ (h.connected F q hq hswap)
  · intro he; exact hg (Or.inl he.symm)
  · intro he
    have hx:g•basePoint F∈(sourceGraph F q hq hswap).neighborSet (basePoint F):=he
    rw [sourceGraph_neighbor_base] at hx
    exact hg (Or.inr hx)

end CFSG.Quasithin.ChapterJ.Section05
