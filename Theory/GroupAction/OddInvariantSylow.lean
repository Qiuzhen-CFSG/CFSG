module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Preorder.Finite

/-!
# Invariant Sylow extensions in odd-order groups

If a two-group acts by automorphisms on a finite group of odd order, every
invariant p-subgroup lies in an invariant Sylow p-subgroup. Neither the actor
nor the acted-on group requires a solvability hypothesis, and the supplied
action instance is used throughout.

The number of Sylow p-subgroups divides the odd group order. The two-group
orbit congruence therefore supplies an invariant Sylow. For the stronger
extension statement, choose a maximal invariant p-subgroup above the given
one. Its normalizer is invariant and has odd order; an invariant Sylow in
that normalizer contains the original p-subgroup by normality. Maximality
makes the two equal. The normalizer condition in finite p-groups then proves
that this subgroup is Sylow in the whole group.

This is the standard invariant Sylow extension argument specialized to an
odd-order group and a two-group actor. It supplies the primewise transfer
for the Brauer--Wielandt relation used in Gorenstein--Walter, Section 2,
Lemma 3; only Mathlib's Sylow, orbit-congruence, and nilpotence results are
needed.
-/

open scoped Pointwise

private theorem invariant_sylow_exists
    {G A : Type*} [Group G] [Finite G] [Group A]
    [MulDistribMulAction A G] (hA : IsPGroup 2 A) (hodd : Odd (Nat.card G))
    (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, IsInvariant A G (P : Subgroup G) := by
  have hdiv : Nat.card (Sylow p G) ∣ Nat.card G :=
    (Sylow.card_dvd_index (Classical.choice (inferInstance : Nonempty (Sylow p G)))).trans (Subgroup.index_dvd_card _)
  have hnot : ¬ 2 ∣ Nat.card (Sylow p G) :=
    fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h.trans hdiv))
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p G) hnot
  refine ⟨P, ⟨fun a g => ?_⟩⟩
  have heq : a • (P : Subgroup G) = (P : Subgroup G) :=
    congrArg Sylow.toSubgroup (hP a)
  constructor
  · intro hg
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul g a _ hg
  · intro hg
    have heq' : a⁻¹ • (P : Subgroup G) = (P : Subgroup G) :=
      congrArg Sylow.toSubgroup (hP a⁻¹)
    have hmem := Subgroup.smul_mem_pointwise_smul (a • g) a⁻¹ (P : Subgroup G) hg
    simpa only [heq', inv_smul_smul] using hmem


private theorem sylow_of_maximal_in_normalizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    (hmax : ∀ L : Subgroup G, IsPGroup p L → P ≤ L →
      L ≤ (Subgroup.normalizer P) → L ≤ P) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  refine ⟨⟨P, hP, ?_⟩, rfl⟩
  intro K hK hPK
  let _ := hK.isNilpotent
  have hLP : (Subgroup.normalizer P) ⊓ K ≤ P :=
    hmax _ (hK.to_le inf_le_right)
      (le_inf P.le_normalizer hPK) inf_le_left
  have hself : Subgroup.normalizer (P.subgroupOf K) = P.subgroupOf K := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPK]
    ext x
    exact ⟨fun hx => hLP ⟨hx, x.property⟩, fun hx => P.le_normalizer hx⟩
  have htop : P.subgroupOf K = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := K)) _ hself
  exact (Subgroup.subgroupOf_eq_top.mp htop).antisymm hPK

/-- An invariant p-subgroup of an odd-order group extends to an invariant
Sylow p-subgroup under any two-group action. -/
public theorem exists_invariant_sylow_le_of_isPGroup
    {G A : Type*} [Group G] [Finite G] [Group A]
    [MulDistribMulAction A G] (hA : IsPGroup 2 A) (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (R : Subgroup G) (hR : IsPGroup p R)
    (hRI : IsInvariant A G R) :
    ∃ P : Sylow p G, R ≤ P ∧ IsInvariant A G (P : Subgroup G) := by
  classical
  obtain ⟨P, hRP, hPprop, hPmax⟩ :=
    Finite.exists_le_maximal (p := fun P : Subgroup G =>
      IsPGroup p P ∧ IsInvariant A G P) ⟨hR, hRI⟩
  let _ : IsInvariant A G P := hPprop.2
  let N := Subgroup.normalizer (P : Set G)
  let _ : IsInvariant A G N := isInvariant_normalizer P
  have hNodd : Odd (Nat.card N) :=
    Nat.not_even_iff_odd.mp (fun h => hodd.not_two_dvd_nat
      ((even_iff_two_dvd.mp h).trans (Subgroup.card_subgroup_dvd_card N)))
  obtain ⟨Q, hQI⟩ := invariant_sylow_exists hA hNodd p
  let _ : IsInvariant A N (Q : Subgroup N) := hQI
  let QG : Subgroup G := (Q : Subgroup N).map N.subtype
  have hQG : IsPGroup p QG := Q.isPGroup'.map N.subtype
  have hQGI : IsInvariant A G QG := isInvariant_map_subtype N (Q : Subgroup N)
  have hPQN : P.subgroupOf N ≤ Q :=
    (hPprop.1.of_equiv (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm).le_sylow_of_normal Q
  have hPQ : P ≤ QG := by
    intro x hx
    exact ⟨⟨x, P.le_normalizer hx⟩, hPQN hx, rfl⟩
  have hQP : QG ≤ P := hPmax ⟨hQG, hQGI⟩ hPQ
  obtain ⟨S, hS⟩ := sylow_of_maximal_in_normalizer P hPprop.1 (by
    intro L hL hPL hLN
    have hLQ : L.subgroupOf N ≤ Q := by
      have hQPL : (Q : Subgroup N) ≤ L.subgroupOf N := by
        intro x hx
        exact hPL (hQP ⟨x, hx, rfl⟩)
      exact (Q.is_maximal' (hL.of_equiv (Subgroup.subgroupOfEquivOfLe hLN).symm) hQPL).le
    intro x hx
    exact hQP ⟨⟨x, hLN hx⟩, hLQ hx, rfl⟩)
  exact ⟨S, hS ▸ hRP, hS ▸ hPprop.2⟩
