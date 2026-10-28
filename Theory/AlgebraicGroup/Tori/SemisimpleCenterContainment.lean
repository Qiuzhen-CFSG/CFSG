module

public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
The algebraic final step of semisimple center containment in maximal tori.

A connected solvable reductive group is a torus: the whole group is its
radical, and the radical is toral. Applied to a maximal-torus centralizer,
maximality then identifies the centralizer with the original torus. Every
central point consequently lies in that torus. Semisimplicity supplies
ambient reductivity, since the trivial closed subgroup is a torus.

The geometric inputs remain explicit here. They are the connectedness and
solvability of the maximal-torus centralizer (Bor1, Chapter IV, 11.7 and
11.12), and torality of its radicals in a reductive ambient group (13.17,
Corollary 2(a)). Thus the conditional results below do not yet establish
GLS3, Theorem 1.9.5(h), or Bor1, 13.17, Corollary 2(c,d).
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A semisimple group is reductive, with the rank-zero torus as radical. -/
public theorem isReductive_of_isSemisimple
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K) : IsReductiveAlgebraicGroup K := by
  refine ⟨hK.1, ?_⟩
  intro R hR
  have hRbot : R = ClosedSubgroup.bot := by
    apply SetLike.coe_injective
    change (R.toSubgroup : Set (Variety.Point K)) =
      ((⊥ : Subgroup (Variety.Point K)) : Set (Variety.Point K))
    rw [hK.2 R hR]
  rw [hRbot]
  exact closedSubgroup_bot_isTorus K

omit [IsAlgClosed k] in
/-- A connected solvable reductive group is a torus. The isomorphism here
uses the regular inclusion and its regular inverse, not merely a bijection
on points. -/
public theorem isTorus_of_isSolvable_of_isReductive
    {C : Variety k} [AlgebraicGroup C]
    (hC : IsReductiveAlgebraicGroup C)
    (hsolv : Group.IsSolvable (Variety.Point C)) : IsTorus C := by
  let H : ClosedSubgroup C := ClosedSubgroup.top
  have hHrad : IsRadicalSubgroup H := by
    refine ⟨Subgroup.normal_top, hC.1, ?_, ?_⟩
    · let : Group.IsSolvable (Variety.Point C) := hsolv
      exact Group.isSolvable_of_isSolvable_injective H.inclusion_injective
    · intro N _ _ _ x _
      trivial
  obtain ⟨n, ⟨e⟩⟩ := hC.2 H hHrad
  let lift : AlgebraicGroup.Morphism C H.carrierVariety :=
    (AlgebraicGroup.Morphism.id C).codRestrictClosedSubgroup H (fun _ => trivial)
  let topIso : AlgebraicGroup.Iso H.carrierVariety C :=
    { hom := H.inclusion
      inv := lift
      hom_inv_id := by
        intro x
        apply H.inclusion_injective
        rfl
      inv_hom_id := by intro x; rfl }
  exact ⟨n, ⟨topIso.comp e⟩⟩

omit [IsAlgClosed k] in
/-- The centralizer calculation, conditional on the two independent Cartan
and radical inputs from Bor1. -/
public theorem maximalTorus_centralizer_eq_of_connected_solvable_of_toral_radicals
    {K : Variety k} [AlgebraicGroup K]
    {S : ClosedSubgroup K} (hS : IsMaximalTorus S)
    (hconnected : Variety.IsConnected S.centralizer.carrierVariety)
    (hsolvable : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hradicals : ∀ R : ClosedSubgroup S.centralizer.carrierVariety,
      IsRadicalSubgroup R → IsSubtorus R) :
    S.centralizer.toSubgroup = S.toSubgroup := by
  exact maximalTorus_centralizer_eq_of_isTorus hS
    (isTorus_of_isSolvable_of_isReductive ⟨hconnected, hradicals⟩ hsolvable)

omit [IsAlgClosed k] in
/-- Conditional center containment. The geometric premises must be proved
from ambient semisimplicity before applying this to GLS3, Theorem 1.9.5(h). -/
public theorem center_le_maximalTorus_of_connected_solvable_of_toral_radicals
    {K : Variety k} [AlgebraicGroup K]
    {S : ClosedSubgroup K} (hS : IsMaximalTorus S)
    (hconnected : Variety.IsConnected S.centralizer.carrierVariety)
    (hsolvable : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hradicals : ∀ R : ClosedSubgroup S.centralizer.carrierVariety,
      IsRadicalSubgroup R → IsSubtorus R) :
    Subgroup.center (Variety.Point K) ≤ S.toSubgroup := by
  rw [← maximalTorus_centralizer_eq_of_connected_solvable_of_toral_radicals
    hS hconnected hsolvable hradicals]
  exact Subgroup.center_le_centralizer _

end Theory.AlgebraicGroup.SemisimpleCenterContainment
