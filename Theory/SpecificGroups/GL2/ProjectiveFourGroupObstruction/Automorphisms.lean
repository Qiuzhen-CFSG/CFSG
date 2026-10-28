module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.LinearAction
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.QuotientCompatibility
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Four-groups of automorphisms of natural odd extensions

Let V be a characteristic self-centralizing elementary abelian subgroup of a
finite group H, of order p² with p odd. The restriction kernel Aut(H) → Aut(V)
is a p-group, so restriction embeds every four-group into GL₂(p). Its scalar
involution inverts V and fixes H/V. Naturality gives the same obstruction on
H/W whenever W is characteristic and contains V.

We reuse the proved restriction-kernel theorem from
`CharacteristicSelfCentralizingAutomorphisms`. The action theorem also allows
nonfaithful actions on H: injectivity on the quotient would force injectivity
on V, where the linear obstruction applies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §13.1,
printed p.876. No splitting of H over V or identification of H/V is required.
-/

namespace Subgroup

/-- Restriction to a characteristic self-centralizing elementary abelian odd
subgroup is faithful on every elementary abelian two-subgroup of automorphisms. -/
public theorem four_group_restriction_injective {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (V : Subgroup H) [V.Characteristic] [IsElementaryAbelian p V]
    (hself : centralizer (V : Set H) ≤ V)
    (A : Subgroup (MulAut H)) [IsElementaryAbelian 2 A] :
    Function.Injective ((MulAut.characteristic V).comp A.subtype) := by
  have hk := isPGroup_characteristic_restriction_kernel_of_centralizer_le V
    (IsElementaryAbelian.isPGroup p V) hself
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  apply injective_comp_subtype_of_coprime_ker _ _ A (IsElementaryAbelian.isPGroup 2 A)
  rw [hn]
  exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm).pow_right n

/-- A four-group of automorphisms contains a nonidentity element inverting V
and acting trivially on H/V. -/
public theorem exists_inverting_four_group_automorphism {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (V : Subgroup H) [V.Characteristic] [IsElementaryAbelian p V]
    (hV : Nat.card V = p ^ 2) (hself : centralizer (V : Set H) ≤ V)
    (A : Subgroup (MulAut H)) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) :
    ∃ a : A, a ≠ 1 ∧ (∀ v : V, (a : MulAut H) v = (v : H)⁻¹) ∧
      quotientAut V a = 1 := by
  obtain ⟨a, ha, hinv⟩ := IsElementaryAbelian.exists_inverting_of_four_group hp hV hA
    ((MulAut.characteristic V).comp A.subtype)
    (four_group_restriction_injective hp V hself A)
  have hi (v : V) : (a : MulAut H) v = (v : H)⁻¹ := congrArg Subtype.val (hinv v)
  exact ⟨a, ha, hi, quotientAut_eq_one_of_restriction_mem_center V hself a
    (restriction_mem_center_of_inverts V a hi)⟩

/-- No action of a four-group on H induces a faithful action on H/V when V
is characteristic, self-centralizing, and elementary abelian of odd rank two. -/
public theorem four_group_quotient_action_not_injective {H E : Type*} [Group H] [Finite H]
    [Group E] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (V : Subgroup H) [V.Characteristic] [IsElementaryAbelian p V]
    (hV : Nat.card V = p ^ 2) (hself : centralizer (V : Set H) ≤ V)
    (ρ : E →* MulAut H) : ¬ Function.Injective ((quotientAut V).comp ρ) := by
  let : Finite E := Nat.finite_of_card_ne_zero (by omega)
  intro hfaith
  let r := (MulAut.characteristic V).comp ρ
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply r.ker.eq_bot_iff_forall.mpr
    intro a ha
    apply hfaith
    rw [map_one]
    apply quotientAut_eq_one_of_restriction_mem_center V hself (ρ a)
    change r a ∈ center (MulAut V)
    rw [MonoidHom.mem_ker.mp ha]
    exact (center (MulAut V)).one_mem
  obtain ⟨a, ha, hinv⟩ := IsElementaryAbelian.exists_inverting_of_four_group hp hV hE r hr
  apply ha
  apply hfaith
  rw [map_one]
  apply quotientAut_eq_one_of_restriction_mem_center V hself (ρ a)
  exact restriction_mem_center_of_inverts V (ρ a) (fun v => congrArg Subtype.val (hinv v))

/-- The four-group obstruction persists for every characteristic quotient H/W
with V ≤ W. -/
public theorem four_group_further_quotient_action_not_injective {H E : Type*}
    [Group H] [Finite H] [Group E] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (V W : Subgroup H) [V.Characteristic] [W.Characteristic] [IsElementaryAbelian p V]
    (hV : Nat.card V = p ^ 2) (hself : centralizer (V : Set H) ≤ V)
    (hVW : V ≤ W) (ρ : E →* MulAut H) :
    ¬ Function.Injective ((quotientAut W).comp ρ) := by
  intro hi
  apply four_group_quotient_action_not_injective hE hp V hV hself ρ
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply ((quotientAut V).comp ρ).ker.eq_bot_iff_forall.mpr
  intro a ha
  apply hi
  rw [map_one]
  exact quotientAut_ker_mono V W hVW ha
end Subgroup
