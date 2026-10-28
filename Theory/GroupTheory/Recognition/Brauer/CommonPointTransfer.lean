module
public import Theory.GroupTheory.Recognition.Brauer.CommutingIncidence
public import Theory.GroupTheory.Recognition.Brauer.ContainingBlocks
public import Theory.GroupTheory.Recognition.Brauer.BlockIntersection

/-!
# A common point from a common nonincident point

Under Brauer's full postulates, two lines with a common nonincident point
have a common incident point. This is the algebraic transfer in Brauer,
*On finite Desarguesian planes I*, Theorem (3B)(a), article p. 121.
The separate counting argument supplies the initial nonincident point;
this result needs no total-cardinality formula or distinctness of the lines.

Choose the involution shared by the nonincident point and the first line,
and conjugate it to `j`. Uniqueness of containing blocks identifies their
images with `jM` and `jMstar`. The second line contains `j*m` for some
`m` in `M`. Postulate (V) conjugates `m` into `M1` by an element of `C(j)`,
which fixes the base line. Now `j1` commutes with the two line involutions
and differs from both: equality with the second would put `j*j1` in
`M` intersected with `C(j)`. The commuting-incidence theorem (2D) supplies
their common point, and the two inverse conjugations transport it back.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneData

private theorem incident_smul_iff {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) (g : ConjAct G) (p : S.Point) (l : S.Line) :
    g • p ∈ g • l ↔ p ∈ l := by
  exact Set.disjoint_smul_set

/-- The transfer in Brauer I (3B)(a), before its counting input. -/
public theorem exists_common_point_of_nonincident
    {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G)
    (p : D.toBrauerPlaneSeed.Point) (l1 l2 : D.toBrauerPlaneSeed.Line)
    (h1 : p ∉ l1) (h2 : p ∉ l2) :
    ∃ p' : D.toBrauerPlaneSeed.Point, p' ∈ l1 ∧ p' ∈ l2 := by
  let S := D.toBrauerPlaneSeed
  obtain ⟨x, hxp, hxl⟩ := Set.not_disjoint_iff_nonempty_inter.mp h1
  obtain ⟨a, ha⟩ := isConj_iff.mp
    (S.involutions_isConj (S.orderOf_mem_point p hxp) S.j_order)
  let g : ConjAct G := ConjAct.toConjAct a
  have hg : g • x = S.j := ha
  let p0 : S.Point := ⟨S.basePoint, MulAction.mem_orbit_self _⟩
  let l0 : S.Line := ⟨S.baseLine, MulAction.mem_orbit_self _⟩
  have hjp0 : S.j ∈ (p0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩
  have hjl0 : S.j ∈ (l0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩
  have hp : g • p = p0 := (S.existsUnique_blocks_of_involution S.j_order).1.unique
    (hg ▸ Set.smul_mem_smul_set hxp) hjp0
  have hl : g • l1 = l0 := (S.existsUnique_blocks_of_involution S.j_order).2.unique
    (hg ▸ Set.smul_mem_smul_set hxl) hjl0
  have h2' : p0 ∉ g • l2 := by
    rw [← hp]
    exact fun h => h2 ((incident_smul_iff S g p l2).mp h)
  obtain ⟨z, hzp, hzl⟩ := Set.not_disjoint_iff_nonempty_inter.mp h2'
  obtain ⟨m, hm, hmz⟩ := Set.mem_smul_set.mp hzp
  change S.j * m = z at hmz
  obtain ⟨c, hc⟩ := D.orbit_meets_M1 ⟨m, hm⟩
  let k : ConjAct G := ConjAct.toConjAct (c : G)⁻¹
  have hk : k • S.j = S.j := by
    change (c : G)⁻¹ * S.j * ((c : G)⁻¹)⁻¹ = S.j
    have heq := Subgroup.mem_centralizer_singleton_iff.mp c.property
    rw [inv_inv, mul_assoc, ← heq, inv_mul_cancel_left]
  have hkl : k • l0 = l0 := (S.existsUnique_blocks_of_involution S.j_order).2.unique
    (hk ▸ Set.smul_mem_smul_set hjl0) hjl0
  let m' : G := (c : G)⁻¹ * m * c
  have hm' : m' ∈ S.M1 := hc
  have hkz : k • z = S.j * m' := by
    rw [← hmz, smul_mul', hk]
    change S.j * ((c : G)⁻¹ * m * ((c : G)⁻¹)⁻¹) = S.j * m'
    rw [inv_inv]
  have hmem : S.j * m' ∈ ((k • (g • l2) : S.Line) : Set G) :=
    hkz ▸ Set.smul_mem_smul_set hzl
  have hcomm : Commute S.j1 (S.j * m') := S.j_commute_j1.symm.mul_right
    (show Commute S.j1 m' from
      (Subgroup.mem_centralizer_singleton_iff.mp hm'.2).symm)
  have hne : S.j1 ≠ S.j * m' := by
    intro heq
    have hjj : S.j * S.j = 1 := by
      simpa only [S.j_order, pow_two] using pow_orderOf_eq_one S.j
    have heqm : S.j * S.j1 = m' := by
      rw [heq, ← mul_assoc, hjj, one_mul]
    have hj2M : S.j * S.j1 ∈ S.M := heqm.symm ▸ hm'.1
    have hj2C : S.j * S.j1 ∈ Subgroup.centralizer {S.j} := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact ((Commute.refl S.j).mul_left S.j_commute_j1.symm).eq
    have hj2one : S.j * S.j1 = 1 := by
      have hmem : S.j * S.j1 ∈ S.M ⊓ Subgroup.centralizer {S.j} := ⟨hj2M, hj2C⟩
      simpa only [S.disjoint_M_centralizer.eq_bot, Subgroup.mem_bot] using hmem
    have hji : S.j⁻¹ = S.j := inv_eq_iff_mul_eq_one.mpr hjj
    exact S.j_ne_j1 (by simpa only [hji] using inv_eq_iff_mul_eq_one.mpr hj2one)
  let p' := S.pointOf S.j1 S.j1_order
  have hi0 : p' ∈ l0 := S.incident_of_distinct_commuting p' l0 S.j1_order
    S.j_order S.j_ne_j1.symm S.j_commute_j1.symm (S.mem_pointOf _ _) hjl0
  have hi2 : p' ∈ k • (g • l2) := S.incident_of_distinct_commuting p' _ S.j1_order
    (S.orderOf_mem_line _ hmem) hne hcomm (S.mem_pointOf _ _) hmem
  refine ⟨g⁻¹ • (k⁻¹ • p'), ?_, ?_⟩
  · apply (incident_smul_iff S g _ l1).mp
    simp only [smul_inv_smul, hl]
    apply (incident_smul_iff S k _ l0).mp
    simpa only [smul_inv_smul, hkl] using hi0
  · apply (incident_smul_iff S g _ l2).mp
    simp only [smul_inv_smul]
    apply (incident_smul_iff S k _ (g • l2)).mp
    simpa only [smul_inv_smul] using hi2

end Theory.GroupTheory.BrauerPlaneData
