module
public import Theory.GroupTheory.Recognition.Brauer.IncidentPoints
public import Theory.GroupTheory.Recognition.Brauer.DualSeed

/-!
# Lower bounds for incident blocks in Brauer's geometry

For Brauer's first three postulates, every line has at least `q + 1`
incident points and every point has at least `q + 1` incident lines.
These are (2F)-(2G) of Richard Brauer, *On finite Desarguesian planes I*,
Math. Z. 90 (1965), pp. 120-121. The bounds are used with postulate (IV)
to obtain the exact incidence counts in the projective-plane construction.

The imported distinguished-point construction proves the bound on the
line containing `j2` by injecting `Option Mstar2` into its incident points.
Conjugation transitivity transfers this bound to every line, and the
actual dual seed gives the bound for lines through a point. The shared
construction in `IncidentPoints` also supplies the exact enumeration
used later in the elation argument.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)

private theorem distinguished_incident_lower_bound :
    ∃ l : S.Line, S.q + 1 ≤ Nat.card {p : S.Point // p ∈ l} := by
  have hj2order : orderOf S.j2 = 2 := by
    have h := (MulAut.conj S.y⁻¹).orderOf_eq S.j1
    change orderOf (S.y⁻¹ * S.j1 * (S.y⁻¹)⁻¹) = orderOf S.j1 at h
    simpa only [inv_inv, S.y_conj_j1, S.j1_order] using h
  exact ⟨S.lineOf S.j2 hj2order, S.distinguished_incident_points_lower_bound hj2order⟩

private theorem incident_points_lower_bound (l : S.Line) :
    S.q + 1 ≤ Nat.card {p : S.Point // p ∈ l} := by
  obtain ⟨l2, hbound⟩ := S.distinguished_incident_lower_bound
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ConjAct G) l2 l
  let f : {p : S.Point // p ∈ l2} → {p : S.Point // p ∈ l} := fun p =>
    ⟨g • p.val, by
      rw [← hg, S.mem_iff_disjoint]
      exact (Set.disjoint_smul_set (a := g)).mpr ((S.mem_iff_disjoint _ _).mp p.property)⟩
  exact hbound.trans (Nat.card_le_card_of_injective f (by
    intro p q hpq
    apply Subtype.ext
    exact (MulAction.injective g) (congrArg Subtype.val hpq)))

/-- Brauer I (2G): at least `q + 1` incident blocks through each dual block. -/
public theorem incident_lower_bounds :
    (∀ l : S.Line, S.q + 1 ≤ Nat.card {p : S.Point // p ∈ l}) ∧
    (∀ p : S.Point, S.q + 1 ≤ Nat.card {l : S.Line // p ∈ l}) := by
  constructor
  · exact S.incident_points_lower_bound
  · intro p
    have hcard : Nat.card {l : S.Line // p ∈ l} =
        Nat.card {l : S.dual.Point // l ∈ (show S.dual.Line from p)} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun l => (S.dual_incidence_iff p l).symm)
    rw [hcard]
    simpa only [S.dual_q] using S.dual.incident_points_lower_bound p

end Theory.GroupTheory.BrauerPlaneSeed
