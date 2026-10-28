module
public import Theory.GroupTheory.Recognition.Brauer.InvertedSubgroups
public import Theory.GroupTheory.Recognition.Brauer.InvolutionBlocks

/-!
# Point-line intersections in Brauer's geometry

Every member of a point or line is an involution. Moreover, the intersection
of a point and line contains at most one element. This is the uniqueness
argument in Brauer, *On finite Desarguesian planes I*, (2C), p. 120.

Inversion by `j` makes each element of `jM` or `jMstar` square to one.
Disjointness of the root subgroup from `C(j)` excludes the identity, and
conjugation preserves order. For the intersection statement, conjugate a
common involution to `j`. Uniqueness of its containing blocks identifies
both transported sets with the base cosets. Their intersection is `{j}`,
since `M` and `Mstar` intersect trivially. These statements precede and do
not require the final projective-plane postulates.
-/

open scoped Pointwise

namespace Theory.GroupTheory

private theorem orderOf_mem_inverted_coset {G : Type*} [Group G]
    (H : Subgroup G) (j : G) (hj : orderOf j = 2)
    (hd : Disjoint H (Subgroup.centralizer {j}))
    (hi : ∀ m : H, j⁻¹ * (m : G) * j = (m : G)⁻¹)
    {x : G} (hx : x ∈ j • (H : Set G)) : orderOf x = 2 := by
  obtain ⟨m, hm, rfl⟩ := Set.mem_smul_set.mp hx
  have hsq : j * j = 1 := by simpa only [hj, pow_two] using pow_orderOf_eq_one j
  have hji : j⁻¹ = j := inv_eq_iff_mul_eq_one.mpr hsq
  have hmInv : j * m * j = m⁻¹ := by simpa only [hji] using hi ⟨m, hm⟩
  apply orderOf_eq_prime
  · change (j * m) ^ 2 = 1
    calc
      _ = (j * m * j) * m := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hmInv, inv_mul_cancel]
  · intro heq
    have hjH : j ∈ H := by
      have h : j = m⁻¹ := mul_eq_one_iff_eq_inv.mp heq
      rw [h]
      exact H.inv_mem hm
    have hj1 : j = 1 := by
      have hmem : j ∈ H ⊓ Subgroup.centralizer {j} :=
        ⟨hjH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      simpa only [hd.eq_bot, Subgroup.mem_bot] using hmem
    simp [hj1] at hj

private theorem orderOf_mem_conjugate_coset {G : Type*} [Group G]
    (H : Subgroup G) (j : G) (hj : orderOf j = 2)
    (hd : Disjoint H (Subgroup.centralizer {j}))
    (hi : ∀ m : H, j⁻¹ * (m : G) * j = (m : G)⁻¹)
    (p : ↥(MulAction.orbit (ConjAct G) (j • (H : Set G))))
    {x : G} (hx : x ∈ (p : Set G)) : orderOf x = 2 := by
  obtain ⟨g, hg⟩ := p.property
  rw [← hg] at hx
  obtain ⟨m, hm, rfl⟩ := Set.mem_smul_set.mp hx
  exact ((MulAut.conj (ConjAct.ofConjAct g)).orderOf_eq m).trans
    (orderOf_mem_inverted_coset H j hj hd hi hm)

namespace BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)

/-- Every member of a point is an involution, as on Brauer I, p. 119. -/
public theorem orderOf_mem_point (p : S.Point) {x : G} (hx : x ∈ (p : Set G)) :
    orderOf x = 2 :=
  orderOf_mem_conjugate_coset S.M S.j S.j_order S.disjoint_M_centralizer
    S.inverted_subgroups.1.2.2 p hx

/-- Every member of a line is an involution, by the dual source argument. -/
public theorem orderOf_mem_line (l : S.Line) {x : G} (hx : x ∈ (l : Set G)) :
    orderOf x = 2 :=
  orderOf_mem_conjugate_coset S.Mstar S.j S.j_order S.disjoint_Mstar_centralizer
    S.inverted_subgroups.2.2.2 l hx

private theorem eq_j_of_mem_base_intersection {x : G}
    (hx : x ∈ S.basePoint ∩ S.baseLine) : x = S.j := by
  obtain ⟨m, hm, hmx⟩ := Set.mem_smul_set.mp hx.1
  obtain ⟨n, hn, hnx⟩ := Set.mem_smul_set.mp hx.2
  have hmn : m = n := mul_left_cancel (hmx.trans hnx.symm)
  have hm1 : m = 1 := by
    have hmem : m ∈ S.M ⊓ S.Mstar := ⟨hm, hmn.symm ▸ hn⟩
    simpa only [S.disjoint_M_Mstar.eq_bot, Subgroup.mem_bot] using hmem
  simpa only [smul_eq_mul, hm1, mul_one] using hmx.symm

/-- Brauer I (2C): a point and line share at most one involution. -/
public theorem point_line_intersection_subsingleton (p : S.Point) (l : S.Line) :
    Set.Subsingleton ((p : Set G) ∩ (l : Set G)) := by
  intro x hx z hz
  obtain ⟨a, ha⟩ := isConj_iff.mp
    (S.involutions_isConj (S.orderOf_mem_point p hx.1) S.j_order)
  let g : ConjAct G := ConjAct.toConjAct a
  have hg : g • x = S.j := ha
  let p0 : S.Point := ⟨S.basePoint, MulAction.mem_orbit_self _⟩
  let l0 : S.Line := ⟨S.baseLine, MulAction.mem_orbit_self _⟩
  have hjp0 : S.j ∈ (p0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩
  have hjl0 : S.j ∈ (l0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩
  have hjp : S.j ∈ ((g • p : S.Point) : Set G) := hg ▸ Set.smul_mem_smul_set hx.1
  have hjl : S.j ∈ ((g • l : S.Line) : Set G) := hg ▸ Set.smul_mem_smul_set hx.2
  have hp : g • p = p0 := (S.existsUnique_blocks_of_involution S.j_order).1.unique hjp hjp0
  have hl : g • l = l0 := (S.existsUnique_blocks_of_involution S.j_order).2.unique hjl hjl0
  have hzp : g • z ∈ ((g • p : S.Point) : Set G) := Set.smul_mem_smul_set hz.1
  have hzl : g • z ∈ ((g • l : S.Line) : Set G) := Set.smul_mem_smul_set hz.2
  rw [hp] at hzp
  rw [hl] at hzl
  have hzj : g • z = S.j := S.eq_j_of_mem_base_intersection ⟨hzp, hzl⟩
  exact (MulAction.injective g) (hg.trans hzj.symm)

end BrauerPlaneSeed
end Theory.GroupTheory
