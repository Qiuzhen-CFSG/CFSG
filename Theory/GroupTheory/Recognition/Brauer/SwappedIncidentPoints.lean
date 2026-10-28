module
public import Theory.GroupTheory.Recognition.Brauer.IncidentPoints

/-!
# The other distinguished incidence list in Brauer's geometry

Brauer, *On finite Desarguesian planes I*, (2F), p. 121, gives the points
on `[j2]`. The centralizer conjugation in (2.5) swaps `j1` and `j2` and
transports this list to the points on `[j1]`: `(j2)` and the points
containing `j*m`, for `m` in `Mstar1`. The actual dual application gives
the pencil through `(j1)` used in the fixed-line argument of (3C), p. 122.

Postulate (III) supplies a conjugation fixing `j` and exchanging the other
two involutions. It normalizes `Mstar` by postulate (II), so it exchanges
the two fixed root subgroups. Equivariance and uniqueness of containing
blocks transport the established exact enumeration. Its exact-count
hypothesis remains at seed level, allowing dual reuse without a dual
postulate (V).
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem smul_mem_fixed_root
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (g : ConjAct G) (hg : ConjAct.ofConjAct g ∈ Subgroup.normalizer (S.Mstar : Set G))
    {x m : G} (hm : m ∈ S.Mstar ⊓ Subgroup.centralizer {x}) :
    g • m ∈ S.Mstar ⊓ Subgroup.centralizer {g • x} := by
  constructor
  · exact (Subgroup.mem_normalizer_iff.mp hg m).mp hm.1
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hc := congrArg (g • ·) (Subgroup.mem_centralizer_singleton_iff.mp hm.2)
    simpa only [smul_mul'] using hc

/-- The transported Brauer I (2F) list, used dually in (3C). -/
public theorem incident_iff_swapped_distinguished_point
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (h2 : orderOf S.j2 = 2)
    (hcount : Nat.card {p : S.Point // p ∈ S.lineOf S.j2 h2} = S.q + 1)
    (p : S.Point) :
    p ∈ S.lineOf S.j1 S.j1_order ↔
      p = S.pointOf S.j2 h2 ∨ ∃ a : S.Mstar1, S.j * (a : G) ∈ (p : Set G) := by
  have hjj : S.j * S.j = 1 := by
    simpa only [S.j_order, pow_two] using pow_orderOf_eq_one S.j
  have hj1ne : S.j1 ≠ 1 := by
    intro h
    have ho := S.j1_order
    simp [h] at ho
  have hj2ne : S.j2 ≠ S.j := by
    intro h
    exact hj1ne (mul_left_cancel (show S.j * S.j1 = S.j * 1 by simpa using h))
  have hj2c : Commute S.j2 S.j := (Commute.refl S.j).mul_left S.j_commute_j1.symm
  obtain ⟨c, hc⟩ := S.centralizer_involutions_conjugate S.j2 h2 hj2c hj2ne
  let g : ConjAct G := ConjAct.toConjAct (c : G)⁻¹
  have hgj : g • S.j = S.j := by
    change (c : G)⁻¹ * S.j * ((c : G)⁻¹)⁻¹ = S.j
    have h := Subgroup.mem_centralizer_singleton_iff.mp c.property
    rw [inv_inv, mul_assoc, ← h, inv_mul_cancel_left]
  have hg2 : g • S.j2 = S.j1 := by
    change (c : G)⁻¹ * S.j2 * ((c : G)⁻¹)⁻¹ = S.j1
    simpa only [inv_inv] using hc
  have hg1 : g • S.j1 = S.j2 := by
    have heq : S.j * (g • S.j1) = S.j1 := by
      simpa only [j2, smul_mul', hgj] using hg2
    have hh := congrArg (S.j * ·) heq
    simpa only [← mul_assoc, hjj, one_mul] using hh
  have hgij : g⁻¹ • S.j = S.j := by
    calc
      _ = g⁻¹ • (g • S.j) := congrArg (g⁻¹ • ·) hgj.symm
      _ = S.j := inv_smul_smul g S.j
  have hgi2 : g⁻¹ • S.j2 = S.j1 := by rw [← hg1, inv_smul_smul]
  have hgn : ConjAct.ofConjAct g ∈ Subgroup.normalizer (S.Mstar : Set G) :=
    S.centralizer_le_normalizer_Mstar ((Subgroup.centralizer {S.j}).inv_mem c.property)
  have hgin : ConjAct.ofConjAct g⁻¹ ∈ Subgroup.normalizer (S.Mstar : Set G) :=
    (Subgroup.normalizer (S.Mstar : Set G)).inv_mem hgn
  have hgl : g • S.lineOf S.j1 S.j1_order = S.lineOf S.j2 h2 := by
    exact (S.lineOf_eq_iff _ _ _).mpr
      (hg1 ▸ Set.smul_mem_smul_set (S.mem_lineOf _ _)) |>.symm
  have hgp2 : g • S.pointOf S.j2 h2 = S.pointOf S.j1 S.j1_order := by
    exact (S.pointOf_eq_iff _ _ _).mpr
      (hg2 ▸ Set.smul_mem_smul_set (S.mem_pointOf _ _)) |>.symm
  have hinc : p ∈ S.lineOf S.j1 S.j1_order ↔ g • p ∈ S.lineOf S.j2 h2 := by
    rw [← hgl]
    exact Set.disjoint_smul_set.symm
  rw [hinc, S.incident_iff_distinguished_point h2 hcount]
  constructor
  · rintro (hp | ⟨m, hm⟩)
    · exact Or.inl ((MulAction.injective g) (hp.trans hgp2.symm))
    · have hn : g⁻¹ • (m : G) ∈ S.Mstar1 := by
        have h := S.smul_mem_fixed_root g⁻¹ hgin m.property
        simpa only [hgi2] using h
      refine Or.inr ⟨⟨g⁻¹ • (m : G), hn⟩, ?_⟩
      have hh := Set.smul_mem_smul_set (a := g⁻¹) hm
      change g⁻¹ • (S.j * (m : G)) ∈ ((g⁻¹ • (g • p) : S.Point) : Set G) at hh
      simpa only [smul_mul', hgij, inv_smul_smul] using hh
  · rintro (rfl | ⟨m, hm⟩)
    · exact Or.inl hgp2
    · have hn : g • (m : G) ∈ S.Mstar2 := by
        have h := S.smul_mem_fixed_root g hgn m.property
        simpa only [hg1] using h
      refine Or.inr ⟨⟨g • (m : G), hn⟩, ?_⟩
      have hh := Set.smul_mem_smul_set (a := g) hm
      change g • (S.j * (m : G)) ∈ ((g • p : S.Point) : Set G) at hh
      simpa only [smul_mul', hgj] using hh

end Theory.GroupTheory.BrauerPlaneSeed
