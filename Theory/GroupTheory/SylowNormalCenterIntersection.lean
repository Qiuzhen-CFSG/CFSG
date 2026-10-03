module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Nontrivial normal intersections with the Sylow center

A normal subgroup whose order is divisible by p meets every Sylow p-subgroup
nontrivially. This intersection is normal in the Sylow subgroup and hence
meets its center nontrivially, by the fixed-point theorem for p-groups.

This is the general central-intersection argument used in Glauberman,
*A Characterization of the Suzuki Groups* (1968), Proposition 2.1(ii), p. 80,
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
The proof adapts the existing argument in `SylowCenterNormal` without its
hypothesis that the center has a unique nonidentity element.
-/

/-- A normal subgroup whose order is divisible by p meets the Sylow center
nontrivially. -/
public theorem Sylow.exists_ne_one_mem_center_of_normal
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal] (hdvd : p ∣ Nat.card N) :
    ∃ x : S, x ∈ Subgroup.center S ∧ x ≠ 1 ∧ (x : G) ∈ N := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal N
  have hTne : (T : Subgroup N) ≠ ⊥ := T.ne_bot_of_dvd_card hdvd
  have hSne : N.subgroupOf (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [hT]
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    have hx' : (⟨x, hx⟩ : S) ∈ N.subgroupOf (S : Subgroup G) := x.property
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext (congrArg (fun y : S => (y : G)) hx')
  let : Nontrivial (N.subgroupOf (S : Subgroup G)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  let : Fact (IsPGroup p S) := ⟨S.isPGroup'⟩
  obtain ⟨x, hx, hxc⟩ := exists_nontrivial_center_mem_normal
    (N := N.subgroupOf (S : Subgroup G)) (p := p)
  have hx' : (x : S) ≠ 1 := fun h => hx (Subtype.ext h)
  exact ⟨x, hxc, hx', x.property⟩

