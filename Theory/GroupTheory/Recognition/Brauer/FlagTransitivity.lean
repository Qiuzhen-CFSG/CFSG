module
public import Theory.GroupTheory.Recognition.Brauer.PlaneCounts

/-!
# Flag transitivity of Brauer's conjugation action

Brauer, *On finite Desarguesian planes I*, (3C), p. 122, first normalizes
an arbitrary incident point-line pair to `((j1), [j2])`. This module proves
that normalization for the actual involution blocks and conjugation action.
The exact counts from (3A) make the distinguished enumeration exhaustive.

First move the line to `[j2]` by orbit transitivity. Its point is either
`(j1)` already or contains `j*m` for `m` in `Mstar2`. An odd-order square
root of `m`, still in `Mstar2`, conjugates `j*m` to `j` and fixes `j2`.
Postulate (III) supplies an element `c` of `C(j)` taking `j2` to `j1`
under right conjugation. Right conjugation by `c*y` then takes `j` to
`j1` and fixes `j2`. Uniqueness of containing blocks transfers both
element calculations to the same flag action.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem exists_smul_root_eq_j
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) (m : S.Mstar2) :
    ∃ g : ConjAct G, g • (S.j * (m : G)) = S.j ∧ g • S.j2 = S.j2 := by
  have ho : Odd (orderOf (m : G)) :=
    S.inverted_subgroups.2.1.of_dvd_nat (S.Mstar.orderOf_dvd_natCard m.property.1)
  obtain ⟨k, hk⟩ := ho
  let a : S.Mstar2 := m ^ (k + 1)
  have ha : (a : G) ^ 2 = (m : G) := by
    change ((m : G) ^ (k + 1)) ^ 2 = (m : G)
    rw [← pow_mul, show (k + 1) * 2 = orderOf (m : G) + 1 by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  have hi : S.j⁻¹ * (a : G) * S.j = (a : G)⁻¹ :=
    S.inverted_subgroups.2.2.2 ⟨a, a.property.1⟩
  have hac : (a : G) * S.j = S.j * (a : G)⁻¹ := by
    rw [← hi, ← mul_assoc, mul_inv_cancel_left]
  refine ⟨ConjAct.toConjAct (a : G), ?_, ?_⟩
  · change (a : G) * (S.j * (m : G)) * (a : G)⁻¹ = S.j
    rw [← mul_assoc, hac, ← ha, pow_two]
    group
  · change (a : G) * S.j2 * (a : G)⁻¹ = S.j2
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp a.property.2)

private theorem exists_smul_j_eq_j1_fix_j2
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (h2 : orderOf S.j2 = 2) :
    ∃ g : ConjAct G, g • S.j = S.j1 ∧ g • S.j2 = S.j2 := by
  have hj1ne : S.j1 ≠ 1 := by
    intro h
    have ho := S.j1_order
    simp [h] at ho
  have hj2ne : S.j2 ≠ S.j := by
    intro h
    exact hj1ne (mul_left_cancel (show S.j * S.j1 = S.j * 1 by simpa using h))
  have hj2c : Commute S.j2 S.j := (Commute.refl S.j).mul_left S.j_commute_j1.symm
  obtain ⟨c, hc⟩ := S.centralizer_involutions_conjugate S.j2 h2 hj2c hj2ne
  have hcj : (c : G)⁻¹ * S.j * c = S.j := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp c.property
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  refine ⟨ConjAct.toConjAct ((c : G) * S.y)⁻¹, ?_, ?_⟩
  · change ((c : G) * S.y)⁻¹ * S.j * (((c : G) * S.y)⁻¹)⁻¹ = S.j1
    calc
      _ = S.y⁻¹ * ((c : G)⁻¹ * S.j * c) * S.y := by group
      _ = S.j1 := by rw [hcj, S.y_conj_j]
  · change ((c : G) * S.y)⁻¹ * S.j2 * (((c : G) * S.y)⁻¹)⁻¹ = S.j2
    calc
      _ = S.y⁻¹ * ((c : G)⁻¹ * S.j2 * c) * S.y := by group
      _ = S.j2 := by rw [hc, S.y_conj_j1]

end Theory.GroupTheory.BrauerPlaneSeed

namespace Theory.GroupTheory.BrauerPlaneData

/-- Brauer I (3C): conjugation takes any incident flag to `((j1), [j2])`. -/
public theorem exists_smul_flag_eq_base
    {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G)
    (p : D.toBrauerPlaneSeed.Point) (l : D.toBrauerPlaneSeed.Line) (hp : p ∈ l)
    (h2 : orderOf D.toBrauerPlaneSeed.j2 = 2) :
    ∃ g : ConjAct G,
      g • p = D.toBrauerPlaneSeed.pointOf D.toBrauerPlaneSeed.j1 D.toBrauerPlaneSeed.j1_order ∧
      g • l = D.toBrauerPlaneSeed.lineOf D.toBrauerPlaneSeed.j2 h2 := by
  let S := D.toBrauerPlaneSeed
  let l2 := S.lineOf S.j2 h2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ConjAct G) l l2
  have hgp : g • p ∈ l2 := by
    rw [← hg]
    exact (Set.disjoint_smul_set (a := g)).mpr hp
  rcases (S.incident_iff_distinguished_point h2 (D.plane_counts.2.2.2.1 l2) (g • p)).mp hgp with
    hpoint | ⟨m, hm⟩
  · exact ⟨g, hpoint, hg⟩
  obtain ⟨a, ha, ha2⟩ := S.exists_smul_root_eq_j m
  obtain ⟨b, hb, hb2⟩ := S.exists_smul_j_eq_j1_fix_j2 h2
  have hab : (b * a) • (S.j * (m : G)) = S.j1 := by rw [mul_smul, ha, hb]
  have hab2 : (b * a) • S.j2 = S.j2 := by rw [mul_smul, ha2, hb2]
  refine ⟨(b * a) * g, ?_, ?_⟩
  · rw [mul_smul]
    exact (S.pointOf_eq_iff _ _ _).mpr
      (hab ▸ Set.smul_mem_smul_set hm) |>.symm
  · rw [mul_smul, hg]
    exact (S.lineOf_eq_iff _ _ _).mpr
      (hab2 ▸ Set.smul_mem_smul_set (S.mem_lineOf S.j2 h2)) |>.symm

end Theory.GroupTheory.BrauerPlaneData
