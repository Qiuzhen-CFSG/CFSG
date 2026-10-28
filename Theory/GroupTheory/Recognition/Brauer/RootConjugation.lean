module
public import Theory.GroupTheory.Recognition.Brauer.CommutingIncidence
public import Theory.GroupTheory.Recognition.Brauer.ContainingBlocks
public import Theory.GroupTheory.Recognition.Brauer.BlockIntersection
public import Mathlib.Combinatorics.Configuration
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Conjugation of Brauer's fixed root subgroups

For Brauer's first three postulates, assume that the actual involution
incidence structure is nondegenerate. Right conjugation by `y` sends
`M1` onto `Mstar2`. This is the root-subgroup identity in the proof of
Brauer, *On finite Desarguesian planes I*, (3C), article p. 122.
The statement is at seed level so it also applies to the actual dual
geometry; the proved projective-plane structure supplies nondegeneracy.

An element of `Mstar2` fixes the lines containing `j` and `j2`.
Their unique incident point is the point containing `j1`, so this point
is fixed too. Conjugating back by `y` yields an element stabilizing `jM`
and inverted by `j`. Its square lies in `M`, hence the element itself
does by odd order. The commuting relation places it in `M1`.
This proves one subgroup containment; equal fixed-factor orders give
equality. The source's intermediate square-membership step is retained,
and no faithfulness of the conjugation action is assumed.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem square_mem_of_stabilizes_inverted_coset
    {G : Type*} [Group G] (H : Subgroup G) (j t : G)
    (hi : j * t * j⁻¹ = t⁻¹)
    (hfix : (ConjAct.toConjAct t) • (j • (H : Set G)) = j • (H : Set G)) :
    t ^ 2 ∈ H := by
  have hj : j ∈ j • (H : Set G) := Set.mem_smul_set.mpr ⟨1, H.one_mem, mul_one j⟩
  have htj : t * j * t⁻¹ ∈ j • (H : Set G) := by
    change (ConjAct.toConjAct t) • j ∈ _
    rw [← hfix]
    exact Set.smul_mem_smul_set hj
  have heq : t * j * t⁻¹ = j * (t ^ 2)⁻¹ := by
    have hc : j * t⁻¹ = t * j := by
      have h := congrArg Inv.inv hi
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using congrArg (· * j) h
    rw [← hc]
    simp only [pow_two, mul_inv_rev, mul_assoc]
  obtain ⟨m, hm, hmeq⟩ := Set.mem_smul_set.mp htj
  change j * m = t * j * t⁻¹ at hmeq
  rw [heq] at hmeq
  have hm' : m = (t ^ 2)⁻¹ := mul_left_cancel hmeq
  have hh : (t ^ 2)⁻¹ ∈ H := hm' ▸ hm
  exact (H.inv_mem_iff).mp hh

private theorem mem_of_sq_mem_of_odd_order
    {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (ho : Odd (orderOf t)) (hs : t ^ 2 ∈ H) : t ∈ H := by
  obtain ⟨k, hk⟩ := ho
  have he : 2 * (k + 1) = orderOf t + 1 := by omega
  have hpow : (t ^ 2) ^ (k + 1) = t := by
    rw [← pow_mul, he, pow_succ, pow_orderOf_eq_one, one_mul]
  exact hpow ▸ H.pow_mem hs (k + 1)

private theorem conj_mem_M1_of_mem_Mstar2
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    [Configuration.Nondegenerate S.Point S.Line] (a : S.Mstar2) :
    S.y * (a : G) * S.y⁻¹ ∈ S.M1 := by
  let g : ConjAct G := ConjAct.toConjAct (a : G)
  let y : ConjAct G := ConjAct.toConjAct S.y⁻¹
  have hj2 : orderOf S.j2 = 2 := by
    have h := (MulAut.conj S.y⁻¹).orderOf_eq S.j1
    change orderOf (S.y⁻¹ * S.j1 * (S.y⁻¹)⁻¹) = orderOf S.j1 at h
    simpa only [inv_inv, S.y_conj_j1, S.j1_order] using h
  have hjne : S.j ≠ 1 := by
    intro h
    have ho := S.j_order
    simp [h] at ho
  have hj1ne : S.j1 ≠ 1 := by
    intro h
    have ho := S.j1_order
    simp [h] at ho
  have hjj : S.j * S.j = 1 := by simpa only [S.j_order, pow_two] using pow_orderOf_eq_one S.j
  have hji : S.j⁻¹ = S.j := inv_eq_iff_mul_eq_one.mpr hjj
  have hj1j2 : S.j1 ≠ S.j2 := by
    intro heq
    exact hjne (mul_right_cancel (show S.j * S.j1 = 1 * S.j1 by simpa using heq.symm))
  have hjj2 : S.j ≠ S.j2 := by
    intro heq
    exact hj1ne (mul_left_cancel (show S.j * S.j1 = S.j * 1 by simpa using heq.symm))
  let p0 := S.pointOf S.j S.j_order
  let p1 := S.pointOf S.j1 S.j1_order
  let l0 := S.lineOf S.j S.j_order
  let l2 := S.lineOf S.j2 hj2
  have hl0 : (l0 : Set G) = S.baseLine := by
    let b : S.Line := ⟨S.baseLine, MulAction.mem_orbit_self _⟩
    have heq : l0 = b := (S.lineOf_eq_iff _ _ b).mpr
      (Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩)
    exact congrArg Subtype.val heq
  have hp0 : (p0 : Set G) = S.basePoint := by
    let b : S.Point := ⟨S.basePoint, MulAction.mem_orbit_self _⟩
    have heq : p0 = b := (S.pointOf_eq_iff _ _ b).mpr
      (Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩)
    exact congrArg Subtype.val heq
  have hgj : g • S.j ∈ (l0 : Set G) := by
    rw [hl0]
    change g • S.j ∈ S.j • (S.Mstar : Set G)
    have horbit := orbit_conjugate_eq_coset S.Mstar S.j S.centralizer_le_normalizer_Mstar
      S.disjoint_Mstar_centralizer
    rw [← horbit]
    exact ⟨⟨g, Subgroup.mem_map.mpr ⟨a, a.property.1, rfl⟩⟩, rfl⟩
  have hgl0 : g • l0 = l0 :=
    (S.existsUnique_blocks_of_involution (S.orderOf_mem_line l0 hgj)).2.unique
      (Set.smul_mem_smul_set (S.mem_lineOf S.j S.j_order)) hgj
  have hgj2 : g • S.j2 = S.j2 := by
    change (a : G) * S.j2 * (a : G)⁻¹ = S.j2
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp a.property.2)
  have hgl2 : g • l2 = l2 :=
    (S.existsUnique_blocks_of_involution hj2).2.unique
      (hgj2 ▸ Set.smul_mem_smul_set (S.mem_lineOf _ _)) (S.mem_lineOf _ _)
  have hi10 : p1 ∈ l0 := S.incident_of_distinct_commuting _ _ S.j1_order S.j_order
    S.j_ne_j1.symm S.j_commute_j1.symm (S.mem_pointOf _ _) (S.mem_lineOf _ _)
  have hi12 : p1 ∈ l2 := S.incident_of_distinct_commuting _ _ S.j1_order hj2 hj1j2
    (S.j_commute_j1.symm.mul_right (Commute.refl _)) (S.mem_pointOf _ _) (S.mem_lineOf _ _)
  have hline_ne : l0 ≠ l2 := by
    intro heq
    have hi02 : p0 ∈ l2 := S.incident_of_distinct_commuting _ _ S.j_order hj2 hjj2
      ((Commute.refl _).mul_right S.j_commute_j1) (S.mem_pointOf _ _) (S.mem_lineOf _ _)
    rw [← heq] at hi02
    exact (Set.disjoint_left.mp hi02) (S.mem_pointOf _ _) (S.mem_lineOf _ _)
  have hgp1 : g • p1 = p1 := by
    have hi0 : g • p1 ∈ l0 := by
      rw [← hgl0]
      exact (Set.disjoint_smul_set (a := g)).mpr hi10
    have hi2 : g • p1 ∈ l2 := by
      rw [← hgl2]
      exact (Set.disjoint_smul_set (a := g)).mpr hi12
    exact (Configuration.Nondegenerate.eq_or_eq hi0 hi10 hi2 hi12).resolve_right hline_ne
  have hyp : y • p0 = p1 := by
    have hyj : y • S.j = S.j1 := by
      change S.y⁻¹ * S.j * (S.y⁻¹)⁻¹ = S.j1
      simpa only [inv_inv] using S.y_conj_j
    exact (S.existsUnique_blocks_of_involution S.j1_order).1.unique
      (hyj ▸ Set.smul_mem_smul_set (S.mem_pointOf _ _)) (S.mem_pointOf _ _)
  let t : G := S.y * (a : G) * S.y⁻¹
  have htfix : (ConjAct.toConjAct t) • S.basePoint = S.basePoint := by
    have ht : (y⁻¹ * g * y) • p0 = p0 := by
      rw [mul_smul, mul_smul, hyp, hgp1, ← hyp, inv_smul_smul]
    have he : y⁻¹ * g * y = ConjAct.toConjAct t := by
      apply ConjAct.ofConjAct.injective
      change (S.y⁻¹)⁻¹ * (a : G) * S.y⁻¹ = S.y * (a : G) * S.y⁻¹
      rw [inv_inv]
    rw [he] at ht
    have hh := congrArg Subtype.val ht
    change (ConjAct.toConjAct t) • (p0 : Set G) = (p0 : Set G) at hh
    rwa [hp0] at hh
  have haj : S.j * (a : G) * S.j⁻¹ = (a : G)⁻¹ := by
    simpa only [hji] using S.inverted_subgroups.2.2.2 ⟨a, a.property.1⟩
  have haj2 : S.j2 * (a : G) * S.j2⁻¹ = (a : G) :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp a.property.2).symm
  have haj1 : S.j1 * (a : G) * S.j1⁻¹ = (a : G)⁻¹ := by
    have hj1eq : S.j1 = S.j * S.j2 := by
      change S.j1 = S.j * (S.j * S.j1)
      rw [← mul_assoc, hjj, one_mul]
    calc
      _ = S.j * (S.j2 * (a : G) * S.j2⁻¹) * S.j⁻¹ := by rw [hj1eq]; group
      _ = _ := by rw [haj2, haj]
  have htinv : S.j * t * S.j⁻¹ = t⁻¹ := by
    have hyj1 : S.y * S.j1 * S.y⁻¹ = S.j := by
      rw [← S.y_conj_j]
      group
    rw [← hyj1]
    calc
      _ = S.y * (S.j1 * (a : G) * S.j1⁻¹) * S.y⁻¹ := by dsimp only [t]; group
      _ = t⁻¹ := by rw [haj1]; dsimp only [t]; group
  have hodd : Odd (orderOf t) := by
    have ho := S.inverted_subgroups.2.1.of_dvd_nat (S.Mstar.orderOf_dvd_natCard a.property.1)
    exact ((MulAut.conj S.y).orderOf_eq (a : G)).symm ▸ ho
  have htM : t ∈ S.M := mem_of_sq_mem_of_odd_order S.M t hodd
    (square_mem_of_stabilizes_inverted_coset S.M S.j t htinv htfix)
  refine ⟨htM, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hyj2 : S.y * S.j2 * S.y⁻¹ = S.j1 := by
    change S.y * (S.j * S.j1) * S.y⁻¹ = S.j1
    rw [← S.y_conj_j1]
    group
  have hc := (show Commute (a : G) S.j2 from
    Subgroup.mem_centralizer_singleton_iff.mp a.property.2).map (MulAut.conj S.y)
  change Commute t (S.y * S.j2 * S.y⁻¹) at hc
  rwa [hyj2] at hc

/-- The fixed-root conjugation identity in Brauer I (3C). -/
public theorem map_M1_conj_y
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    [Configuration.Nondegenerate S.Point S.Line] :
    S.M1.map (MulAut.conj S.y⁻¹).toMonoidHom = S.Mstar2 := by
  have hle : S.Mstar2 ≤ S.M1.map (MulAut.conj S.y⁻¹).toMonoidHom := by
    intro a ha
    refine Subgroup.mem_map.mpr ⟨S.y * a * S.y⁻¹, S.conj_mem_M1_of_mem_Mstar2 ⟨a, ha⟩, ?_⟩
    change S.y⁻¹ * (S.y * a * S.y⁻¹) * (S.y⁻¹)⁻¹ = a
    group
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj S.y⁻¹).injective]
  exact le_of_eq S.fixed_factors.2.2.2.2.2.2.2.1.symm

end Theory.GroupTheory.BrauerPlaneSeed
