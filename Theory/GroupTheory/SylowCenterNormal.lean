module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A unique nonidentity central Sylow element lies in normal subgroups

A normal subgroup whose order is divisible by `p` has a nontrivial intersection
with every Sylow `p`-subgroup. That intersection is normal in the Sylow subgroup,
so it meets its center nontrivially. If this center has a unique nonidentity
element, that element therefore belongs to the original normal subgroup.

This combines Sylow intersection theory with the fixed-point argument for
normal subgroups of finite p-groups.
-/

/-- A unique nonidentity element in the Sylow center belongs to every normal
subgroup of order divisible by the Sylow prime. -/
public theorem Sylow.center_generator_mem_normal
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (z : G)
    (hcenter : ∀ x : S, x ∈ Subgroup.center S → x ≠ 1 → (x : G) = z)
    (N : Subgroup G) [N.Normal] (hdvd : p ∣ Nat.card N) : z ∈ N := by
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
  rw [← hcenter (x : S) hxc hx']
  exact x.property
