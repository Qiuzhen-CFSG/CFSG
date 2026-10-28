module

public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The first omega subgroup of a group with a unique involution

When a group has a unique involution `z`, its first binary omega subgroup
is exactly `⟨z⟩`. Thus its elementary binary subgroups have order at most
two, and an abelian finite two-group with this property is cyclic.
Nontrivial subgroups of a finite two-group inherit the unique involution.

These are the elementary reductions in the cyclic/quaternion theorem
(Huppert, *Endliche Gruppen I*, III.8.2).
-/

namespace Subgroup

/-- With a unique involution, the first omega subgroup is its cyclic subgroup. -/
public theorem omega_one_eq_zpowers_of_unique_involution
    {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
    (hunique : ∀ x : G, orderOf x = 2 → x = z) :
    omega₁ G (p := 2) = zpowers z := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    have hx2 : x ^ 2 = 1 := hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ (zpowers z).one_mem
    · rw [hunique x (orderOf_eq_prime hx2 hx1)]
      exact mem_zpowers z
  · apply zpowers_le.mpr
    apply subset_closure
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z

/-- Every elementary binary subgroup of a group with a unique involution
has order at most two. -/
public theorem card_elementary_le_two_of_unique_involution
    {G : Type*} [Group G] [Finite G]
    (hunique : ∃! z : G, orderOf z = 2)
    (E : Subgroup G) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  obtain ⟨z, hz, hzunique⟩ := hunique
  have hE : E ≤ zpowers z := by
    rw [← omega_one_eq_zpowers_of_unique_involution hz hzunique]
    exact elementaryAbelian_le_omega₁
  simpa only [Nat.card_zpowers, hz] using card_le_of_le hE

end Subgroup

namespace IsPGroup

/-- A nontrivial subgroup inherits the involution of a finite two-group
in which involutions are unique. -/
public theorem existsUnique_involution_subgroup
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hunique : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (H : Subgroup G) (hH : H ≠ ⊥) : ∃! z : H, orderOf z = 2 := by
  obtain ⟨a, ha, hane⟩ := H.bot_or_exists_ne_one.resolve_left hH
  let z : H := ⟨a ^ (orderOf a / 2), H.pow_mem ha _⟩
  have hz : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a)) (hG.dvd_orderOf hane)
  refine ⟨z, hz, fun x hx => ?_⟩
  apply Subtype.ext
  exact hunique x z (by simpa using hx) (by simpa using hz)

/-- The abelian case of the unique-involution classification. -/
public theorem isCyclic_of_unique_involution_of_isMulCommutative
    {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (hG : IsPGroup 2 G) (hunique : ∃! z : G, orderOf z = 2) : IsCyclic G := by
  obtain ⟨z, hz, hzunique⟩ := hunique
  apply hG.isCyclic_of_card_omega_one_le_two
  rw [Subgroup.omega_one_eq_zpowers_of_unique_involution hz hzunique,
    Nat.card_zpowers, hz]

/-- Every abelian subgroup of a finite two-group with a unique involution
is cyclic, including the trivial subgroup. -/
public theorem isCyclic_abelian_subgroup_of_unique_involution
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hunique : ∃! z : G, orderOf z = 2)
    (H : Subgroup G) [IsMulCommutative H] : IsCyclic H := by
  by_cases hH : H = ⊥
  · subst H
    infer_instance
  · exact (hG.to_subgroup H).isCyclic_of_unique_involution_of_isMulCommutative
      (hG.existsUnique_involution_subgroup (fun _ _ hx hy => hunique.unique hx hy) H hH)

end IsPGroup
