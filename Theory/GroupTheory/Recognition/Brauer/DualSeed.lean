module
public import Theory.GroupTheory.Recognition.Brauer.FixedFactors
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Duality of Brauer's first three postulates

Brauer, *On finite Desarguesian planes I*, pp. 118–121, interchanges the
point and line constructions by swapping `M` and `Mstar`. This module
constructs that actual dual seed. Equal subgroup orders transfer the
required nontriviality from `Mstar` to `M`; the other postulates are
symmetric. The fixed-factor order calculation proves that the dual seed
has the same derived parameter `q`.

The definition is intentionally exposed: its point and line types must
reduce to the original line and point types while preserving all group
instances. Incidence reverses because disjointness is symmetric. This
permits the source's dual counting arguments to reuse the same theorems.
The construction applies only to `BrauerPlaneSeed`: postulate (V) in
`BrauerPlaneData` is asymmetric, as Brauer explicitly observes on p. 121.
-/

namespace Theory.GroupTheory.BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G]

/-- Interchange the root subgroups, hence the point and line constructions,
while retaining the three distinguished group elements. -/
@[expose] public def dual (S : BrauerPlaneSeed G) : BrauerPlaneSeed G where
  j := S.j
  j1 := S.j1
  y := S.y
  M := S.Mstar
  Mstar := S.M
  j_order := S.j_order
  j1_order := S.j1_order
  j_ne_j1 := S.j_ne_j1
  j_commute_j1 := S.j_commute_j1
  y_conj_j := S.y_conj_j
  y_conj_j1 := S.y_conj_j1
  y_conj_j2 := S.y_conj_j2
  card_M_eq_Mstar := S.card_M_eq_Mstar.symm
  Mstar_ne_bot := by
    intro hM
    have hcard : Nat.card S.Mstar = 1 := by
      rw [← S.card_M_eq_Mstar, hM, Subgroup.card_bot]
    exact S.Mstar_ne_bot (S.Mstar.eq_bot_of_card_eq hcard)
  centralizer_le_normalizer_M := S.centralizer_le_normalizer_Mstar
  centralizer_le_normalizer_Mstar := S.centralizer_le_normalizer_M
  disjoint_M_Mstar := S.disjoint_M_Mstar.symm
  disjoint_M_centralizer := S.disjoint_Mstar_centralizer
  disjoint_Mstar_centralizer := S.disjoint_M_centralizer
  centralizer_involutions_conjugate := S.centralizer_involutions_conjugate

/-- The order parameter is unchanged under source duality. -/
public theorem dual_q (S : BrauerPlaneSeed G) : S.dual.q = S.q := by
  obtain ⟨_, _, _, _, _, _, hstar1, _, _, _⟩ := S.fixed_factors
  exact hstar1

/-- Dual incidence is precisely incidence with the point and line exchanged. -/
public theorem dual_incidence_iff (S : BrauerPlaneSeed G) (p : S.Point) (l : S.Line) :
    (show S.dual.Point from l) ∈ (show S.dual.Line from p) ↔ p ∈ l := by
  rw [S.dual.mem_iff_disjoint, S.mem_iff_disjoint]
  exact disjoint_comm

end Theory.GroupTheory.BrauerPlaneSeed
