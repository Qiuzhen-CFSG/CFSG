module
public import Theory.GroupTheory.InvolutionFusionFromCentralizer

/-!
# Brauer's involution geometry: original postulates

This module records postulates (I)–(V) of Richard Brauer, *On finite
Desarguesian planes I*, Math. Z. 90 (1965), pp. 117–121. The first three
postulates form `BrauerPlaneSeed`; the final two form `BrauerPlaneData`.
The distinguished elements generate the four-group of (I), with right
conjugation by `y` cycling its three involutions. Postulate (III) is stated
using `j1` as the representative of the centralizer's involutions other than `j`.
The value `q` is the order of `M ∩ C(j1)`, as defined on p. 119.

Points and lines are the actual conjugates of the cosets `jM` and `jMstar`,
and incidence is disjointness, exactly as on p. 118. `ConjAct` uses left
conjugation; inversion of the conjugator gives precisely Brauer's right
conjugation family. The types and their membership relation can later carry
Mathlib's `Configuration.ProjectivePlane`
structure. No projective-plane property is assumed here. In particular,
abelianness, odd order, and the formula `|M| = q²` remain conclusions to prove.

The first consequence is Brauer's (2A): all involutions are conjugate. The
cycle in (I) and the centralizer class in (III) imply local fusion, then
`isConj_of_involution_of_centralizer_fusion` gives global fusion via a central
involution of a Sylow 2-subgroup. These data belong to the standalone
recognition geometry used by Brauer II and hence by ABG's Third Main Theorem.
-/

open scoped Pointwise

namespace Theory.GroupTheory

/-- The first three postulates of Brauer I, pp. 117–118. -/
public structure BrauerPlaneSeed (G : Type*) [Group G] [Finite G] where
  j : G
  j1 : G
  y : G
  M : Subgroup G
  Mstar : Subgroup G
  j_order : orderOf j = 2
  j1_order : orderOf j1 = 2
  j_ne_j1 : j ≠ j1
  j_commute_j1 : Commute j j1
  y_conj_j : y⁻¹ * j * y = j1
  y_conj_j1 : y⁻¹ * j1 * y = j * j1
  y_conj_j2 : y⁻¹ * (j * j1) * y = j
  card_M_eq_Mstar : Nat.card M = Nat.card Mstar
  Mstar_ne_bot : Mstar ≠ ⊥
  centralizer_le_normalizer_M : Subgroup.centralizer {j} ≤ Subgroup.normalizer (M : Set G)
  centralizer_le_normalizer_Mstar : Subgroup.centralizer {j} ≤ Subgroup.normalizer (Mstar : Set G)
  disjoint_M_Mstar : Disjoint M Mstar
  disjoint_M_centralizer : Disjoint M (Subgroup.centralizer {j})
  disjoint_Mstar_centralizer : Disjoint Mstar (Subgroup.centralizer {j})
  centralizer_involutions_conjugate : ∀ x : G, orderOf x = 2 → Commute x j →
    x ≠ j → ∃ c : Subgroup.centralizer {j}, (c : G)⁻¹ * x * c = j1

namespace BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)

/-- The third involution in the distinguished four-group. -/
public abbrev j2 : G := S.j * S.j1

/-- Brauer's centralizer `C(J)`. -/
public abbrev centralizer : Subgroup G := Subgroup.centralizer {S.j}

/-- Brauer's subgroup `M₁`, equation (2.3). -/
public abbrev M1 : Subgroup G := S.M ⊓ Subgroup.centralizer {S.j1}

/-- Brauer's subgroup `M₂`, equation (2.3). -/
public abbrev M2 : Subgroup G := S.M ⊓ Subgroup.centralizer {S.j2}

/-- Brauer's subgroup `M₁*`, equation (2.3). -/
public abbrev Mstar1 : Subgroup G := S.Mstar ⊓ Subgroup.centralizer {S.j1}

/-- Brauer's subgroup `M₂*`, equation (2.3). -/
public abbrev Mstar2 : Subgroup G := S.Mstar ⊓ Subgroup.centralizer {S.j2}

/-- The parameter introduced on p. 119 is a derived subgroup order. -/
@[expose] public noncomputable def q : ℕ := Nat.card S.M1

/-- The distinguished point is the coset `jM`. -/
@[expose] public def basePoint : Set G := S.j • (S.M : Set G)

/-- The distinguished line is the coset `jMstar`. -/
@[expose] public def baseLine : Set G := S.j • (S.Mstar : Set G)

/-- A point is a conjugate of the subset `jM`. -/
public abbrev Point := ↥(MulAction.orbit (ConjAct G) S.basePoint)

/-- A line is a conjugate of the subset `jMstar`. -/
public abbrev Line := ↥(MulAction.orbit (ConjAct G) S.baseLine)

/-- Brauer's incidence is disjointness of the two involution subsets. -/
public instance : Membership S.Point S.Line :=
  ⟨fun l p => Disjoint (p : Set G) (l : Set G)⟩

/-- Incidence is disjointness, as in the source definition on p. 118. -/
public theorem mem_iff_disjoint (p : S.Point) (l : S.Line) :
    p ∈ l ↔ Disjoint (p : Set G) (l : Set G) := Iff.rfl

/-- Brauer I (2A): the finite group has a single class of involutions. -/
public theorem involutions_isConj (S : BrauerPlaneSeed G) {x z : G} (hx : orderOf x = 2)
    (hz : orderOf z = 2) : IsConj x z := by
  have hlocal : ∀ t : G, orderOf t = 2 → Commute t S.j → IsConj t S.j := by
    intro t ht hcomm
    by_cases h : t = S.j
    · exact h ▸ IsConj.refl S.j
    obtain ⟨c, hc⟩ := S.centralizer_involutions_conjugate t ht hcomm h
    have htj1 : IsConj t S.j1 :=
      isConj_iff.mpr ⟨(c : G)⁻¹, by simpa only [inv_inv] using hc⟩
    have hjj1 : IsConj S.j S.j1 :=
      isConj_iff.mpr ⟨S.y⁻¹, by simpa only [inv_inv] using S.y_conj_j⟩
    exact htj1.trans hjj1.symm
  exact (isConj_of_involution_of_centralizer_fusion S.j_order hlocal hx).trans
    (isConj_of_involution_of_centralizer_fusion S.j_order hlocal hz).symm

end BrauerPlaneSeed

/-- All five original postulates of Brauer I. The index bound uses the join:
postulate (II) makes this join equal to the subgroup product `M C(j)`. -/
public structure BrauerPlaneData (G : Type*) [Group G] [Finite G]
    extends BrauerPlaneSeed G where
  index_le : (M ⊔ Subgroup.centralizer {j}).index ≤
    toBrauerPlaneSeed.q ^ 2 + toBrauerPlaneSeed.q + 1
  orbit_meets_M1 : ∀ m : M, ∃ c : Subgroup.centralizer {j},
    (c : G)⁻¹ * (m : G) * c ∈ toBrauerPlaneSeed.M1

end Theory.GroupTheory
