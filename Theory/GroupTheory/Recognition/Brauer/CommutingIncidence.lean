module
public import Theory.GroupTheory.Recognition.Brauer.BaseIncidence
public import Theory.GroupTheory.Recognition.Brauer.InvolutionBlocks
public import Mathlib.Tactic.Group

/-!
# Commuting involutions determine incident blocks

For Brauer's first three postulates, a point containing an involution `x`
is incident with a line containing a distinct commuting involution `z`.
Incidence is the original disjointness of involution subsets. This is
Brauer, *On finite Desarguesian planes I*, (2D), article p. 120, and supplies
the incident blocks used by the subsequent incidence counts.

Global involution fusion first sends `x` to `j`. The remaining involution
lies in `C(j)` and differs from `j`, so postulate (III) sends it to `j1`
while fixing `j`. Uniqueness of the point and line through each involution
identifies their transported blocks with the distinguished blocks.
`disjoint_basePoint_conj_baseLine` proves their disjointness, which is then
transported back by the same conjugation.
-/

namespace Theory.GroupTheory.BrauerPlaneSeed
private theorem normalize_commuting {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) {x z : G} (hx : orderOf x = 2) (hz : orderOf z = 2)
    (hne : x ≠ z) (hc : Commute x z) :
    ∃ g : ConjAct G, g • x = S.j ∧ g • z = S.j1 := by
  obtain ⟨a, ha⟩ := isConj_iff.mp (S.involutions_isConj hx S.j_order)
  let t : G := a * z * a⁻¹
  have htorder : orderOf t = 2 := ((MulAut.conj a).orderOf_eq z).trans hz
  have htcomm : Commute t S.j := by
    have ht := hc.symm.map (MulAut.conj a)
    change Commute t (a * x * a⁻¹) at ht
    rwa [ha] at ht
  have htne : t ≠ S.j := by
    intro ht
    have : (MulAut.conj a) z = (MulAut.conj a) x := ht.trans ha.symm
    exact hne ((MulAut.conj a).injective this).symm
  obtain ⟨c, hc⟩ := S.centralizer_involutions_conjugate t htorder htcomm htne
  refine ⟨ConjAct.toConjAct ((c : G)⁻¹ * a), ?_, ?_⟩
  · change ((c : G)⁻¹ * a) * x * ((c : G)⁻¹ * a)⁻¹ = S.j
    have hfix : (c : G)⁻¹ * S.j * c = S.j := by
      have heq := Subgroup.mem_centralizer_singleton_iff.mp c.property
      rw [mul_assoc, ← heq, inv_mul_cancel_left]
    calc
      _ = (c : G)⁻¹ * (a * x * a⁻¹) * c := by group
      _ = S.j := by rw [ha, hfix]
  · change ((c : G)⁻¹ * a) * z * ((c : G)⁻¹ * a)⁻¹ = S.j1
    calc
      _ = (c : G)⁻¹ * t * c := by dsimp only [t]; group
      _ = S.j1 := hc


open scoped Pointwise
/-- Brauer I (2D), for the actual point and line containing the involutions. -/
public theorem incident_of_distinct_commuting
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (p : S.Point) (l : S.Line) {x z : G} (hx : orderOf x = 2) (hz : orderOf z = 2)
    (hne : x ≠ z) (hc : Commute x z) (hxp : x ∈ (p : Set G))
    (hzl : z ∈ (l : Set G)) : p ∈ l := by
  obtain ⟨g, hgx, hgz⟩ := normalize_commuting S hx hz hne hc
  let p0 : S.Point := ⟨S.basePoint, MulAction.mem_orbit_self _⟩
  let l1 : S.Line := ⟨(ConjAct.toConjAct S.y⁻¹) • S.baseLine,
    MulAction.mem_orbit _ _⟩
  have hjp0 : S.j ∈ (p0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩
  have hj1l1 : S.j1 ∈ (l1 : Set G) := by
    have hjl0 : S.j ∈ S.baseLine :=
      Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩
    have hj1 : (ConjAct.toConjAct S.y⁻¹) • S.j = S.j1 := by
      change S.y⁻¹ * S.j * (S.y⁻¹)⁻¹ = S.j1
      simpa only [inv_inv] using S.y_conj_j
    exact hj1 ▸ Set.smul_mem_smul_set hjl0
  have hjgp : S.j ∈ ((g • p : S.Point) : Set G) := hgx ▸ Set.smul_mem_smul_set hxp
  have hj1gl : S.j1 ∈ ((g • l : S.Line) : Set G) := hgz ▸ Set.smul_mem_smul_set hzl
  have hpEq : g • p = p0 := (S.existsUnique_blocks_of_involution S.j_order).1.unique hjgp hjp0
  have hlEq : g • l = l1 := (S.existsUnique_blocks_of_involution S.j1_order).2.unique hj1gl hj1l1
  change Disjoint (p : Set G) (l : Set G)
  apply (Set.disjoint_smul_set (a := g)).mp
  change Disjoint ((g • p : S.Point) : Set G) ((g • l : S.Line) : Set G)
  rw [hpEq, hlEq]
  exact S.disjoint_basePoint_conj_baseLine
end Theory.GroupTheory.BrauerPlaneSeed
