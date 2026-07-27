import Mathlib
import Submission.ZStar.LocalReduction
import Submission.BenderSuzuki.External.Suzuki.V.proposition_1_2

/-!
# Odd products of conjugate isolated involutions

The elementary dihedral calculation in this file extracts a useful consequence
of the isolation hypothesis: the product of an involution with any of its
conjugates has odd order.  Equivalently, every commutator with the involution
has odd order.

This is one of the standard formulations lying immediately below Glauberman's
`Z*` theorem.  The proof here is independent of the `Z*` theorem: if the product
of two distinct conjugate involutions had even order, its half-power would be a
central involution in the corresponding dihedral subgroup.  Multiplying that
half-power by the original involution gives another conjugate of the original
involution which commutes with it, contradicting isolation.
-/

namespace Submission.ZStar

open Subgroup

namespace OddCommutators

open BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

/-- Conjugating an involution preserves the involution property, stated using
the `Submission.ZStar.IsInvolution` predicate. -/
lemma isInvolution_conjugate {t : G} (ht : Submission.ZStar.IsInvolution t) (g : G) :
    Submission.ZStar.IsInvolution (g * t * g⁻¹) := by
  have ht' : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht.1, ht.2⟩
  have h := isInvolution_rightConjugateElem (g := g⁻¹) ht'
  have h' : BenderSuzuki.PFAppendixIII.IsInvolution (g * t * g⁻¹) := by
    simpa [rightConjugateElem, mul_assoc] using h
  exact ⟨h'.1, h'.2⟩

/-- Conjugation by a power of the product of two involutions gives the even
reflections in their dihedral subgroup. -/
lemma conjugate_second_by_product_pow
    {u t : G}
    (hu : BenderSuzuki.PFAppendixIII.IsInvolution u)
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (a : ℕ) :
    (u * t) ^ a * t * ((u * t) ^ a)⁻¹ = (u * t) ^ (2 * a) * t := by
  let w : G := u * t
  have hsem : SemiconjBy t w⁻¹ w := by
    change t * (u * t)⁻¹ = (u * t) * t
    rw [mul_inv_rev, ht.inv_eq_self, hu.inv_eq_self]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hpow := hsem.pow_right a
  change w ^ a * t * (w ^ a)⁻¹ = w ^ (2 * a) * t
  calc
    w ^ a * t * (w ^ a)⁻¹ = w ^ a * (t * (w⁻¹) ^ a) := by
      rw [inv_pow]
      simp only [mul_assoc]
    _ = w ^ a * (w ^ a * t) := by rw [hpow.eq]
    _ = w ^ (a + a) * t := by rw [← mul_assoc, ← pow_add]
    _ = w ^ (2 * a) * t := by congr 2 <;> omega

/-- Conjugation by a power of the product of two involutions gives the odd
reflections in their dihedral subgroup. -/
lemma conjugate_first_by_product_pow
    {u t : G}
    (hu : BenderSuzuki.PFAppendixIII.IsInvolution u)
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (a : ℕ) :
    (u * t) ^ a * u * ((u * t) ^ a)⁻¹ = (u * t) ^ (2 * a + 1) * t := by
  let w : G := u * t
  have hu_eq : u = w * t := by
    dsimp [w]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [mul_assoc, htt, mul_one]
  have hsem : SemiconjBy t w⁻¹ w := by
    change t * (u * t)⁻¹ = (u * t) * t
    rw [mul_inv_rev, ht.inv_eq_self, hu.inv_eq_self]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hpow := hsem.pow_right a
  change w ^ a * u * (w ^ a)⁻¹ = w ^ (2 * a + 1) * t
  calc
    w ^ a * u * (w ^ a)⁻¹ = w ^ a * (w * t) * (w⁻¹) ^ a := by
      rw [hu_eq, inv_pow]
    _ = (w ^ a * w) * (t * (w⁻¹) ^ a) := by simp only [mul_assoc]
    _ = (w ^ a * w) * (w ^ a * t) := by rw [hpow.eq]
    _ = w ^ (a + 1 + a) * t := by
      rw [← mul_assoc, ← pow_succ, ← pow_add]
    _ = w ^ (2 * a + 1) * t := by congr 2 <;> omega

/-- Two involutions whose product has odd order are conjugate by a power of
their product.  Moreover, the chosen conjugator commutes with every element
that commutes with both involutions.

This is the elementary dihedral calculation used repeatedly in Glauberman's
proof (Lemma 1 in the original paper). -/
theorem exists_conjugator_of_involutions_mul_odd
    {u t : G}
    (hu : Submission.ZStar.IsInvolution u)
    (ht : Submission.ZStar.IsInvolution t)
    (hodd : Odd (orderOf (u * t))) :
    ∃ y : G, y * t * y⁻¹ = u ∧
      ∀ r : G, Commute r u → Commute r t → Commute r y := by
  rcases hodd with ⟨a, ha⟩
  let w : G := u * t
  let y : G := w ^ (a + 1)
  have hu' : BenderSuzuki.PFAppendixIII.IsInvolution u := ⟨hu.1, hu.2⟩
  have ht' : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht.1, ht.2⟩
  refine ⟨y, ?_, ?_⟩
  · rw [conjugate_second_by_product_pow hu' ht' (a + 1)]
    have hexponent : 2 * (a + 1) = orderOf w + 1 := by
      dsimp [w]
      omega
    rw [hexponent, pow_succ, pow_orderOf_eq_one, one_mul]
    have htt : t * t = 1 := by simpa [pow_two] using ht.2
    rw [mul_assoc, htt, mul_one]
  · intro r hru hrt
    exact (hru.mul_right hrt).pow_right (a + 1)

end OddCommutators

open OddCommutators

/-- The product of an isolated involution with any one of its conjugates has
odd order. -/
theorem orderOf_conjugate_mul_odd
    {G : Type*} [Group G] [Finite G]
    {t : G}
    (htI : IsInvolution t)
    (hisolated : ∀ g : G,
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t)
    (g : G) :
    Odd (orderOf ((g * t * g⁻¹) * t)) := by
  classical
  let u : G := g * t * g⁻¹
  have huI : IsInvolution u := by
    simpa [u] using OddCommutators.isInvolution_conjugate htI g
  have htI' : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨htI.1, htI.2⟩
  have huI' : BenderSuzuki.PFAppendixIII.IsInvolution u := ⟨huI.1, huI.2⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  by_cases hut : u = t
  · have htt : t * t = 1 := by simpa [pow_two] using htI.2
    have horder_one : orderOf (u * t) = 1 := by simp [hut, htt]
    rw [horder_one] at heven
    exact Nat.not_even_one heven
  · rcases heven with ⟨m, hm⟩
    have hm' : orderOf (u * t) = m + m := by
      simpa [u, mul_assoc] using hm
    have horder : orderOf (u * t) = 2 * m := by omega
    obtain ⟨hcI, hcu, hct⟩ :=
      BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
        huI' htI' hut horder
    let c : G := (u * t) ^ m
    let r : G := c * t
    have hcI' : BenderSuzuki.PFAppendixIII.IsInvolution c := by simpa [c] using hcI
    have hct' : Commute c t := by simpa [c] using hct
    have hr_comm_t : r * t = t * r := by
      have htt : t * t = 1 := by simpa [pow_two] using htI.2
      dsimp [r]
      calc
        (c * t) * t = c := by rw [mul_assoc, htt, mul_one]
        _ = t * (c * t) := by
          rw [hct'.eq, ← mul_assoc, htt, one_mul]
    obtain ⟨a, ha | ha⟩ := m.even_or_odd'
    · have hr_conj : r = (u * t) ^ a * t * ((u * t) ^ a)⁻¹ := by
        dsimp [r, c]
        rw [ha]
        exact (OddCommutators.conjugate_second_by_product_pow huI' htI' a).symm
      have hr_eq_t : r = t := by
        rw [hr_conj]
        exact hisolated ((u * t) ^ a) (by simpa [hr_conj] using hr_comm_t)
      apply hcI'.ne_one
      calc
        c = r * t⁻¹ := by simp [r]
        _ = t * t⁻¹ := by rw [hr_eq_t]
        _ = 1 := mul_inv_cancel t
    · have hr_conj_u : r = (u * t) ^ a * u * ((u * t) ^ a)⁻¹ := by
        dsimp [r, c]
        rw [ha]
        exact (OddCommutators.conjugate_first_by_product_pow huI' htI' a).symm
      have hr_conj_t :
          r = ((u * t) ^ a * g) * t * ((u * t) ^ a * g)⁻¹ := by
        rw [hr_conj_u]
        dsimp [u]
        group
      have hr_eq_t : r = t := by
        rw [hr_conj_t]
        exact hisolated ((u * t) ^ a * g) (by simpa [hr_conj_t] using hr_comm_t)
      apply hcI'.ne_one
      calc
        c = r * t⁻¹ := by simp [r]
        _ = t * t⁻¹ := by rw [hr_eq_t]
        _ = 1 := mul_inv_cancel t

/-- The commutator `g t g⁻¹ t⁻¹` with an isolated involution has odd
order. -/
theorem orderOf_commutator_odd
    {G : Type*} [Group G] [Finite G]
    {t : G}
    (htI : IsInvolution t)
    (hisolated : ∀ g : G,
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t)
    (g : G) :
    Odd (orderOf (g * t * g⁻¹ * t⁻¹)) := by
  have ht_inv : t⁻¹ = t := inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  simpa [mul_assoc, ht_inv] using orderOf_conjugate_mul_odd htI hisolated g

/-- Centrality and weak closure in a Sylow `2`-subgroup imply the global
isolation property.  A commuting conjugate `u` of `t` lies in `C_G(t)`.  Inside
that centralizer, put `u` in a Sylow `2`-subgroup and conjugate that Sylow
subgroup to the given one.  Weak closure then identifies the conjugate of `u`
with `t`, and the conjugating element centralizes `t`. -/
theorem isolated_of_central_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    ∀ g : G,
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hcomm
  let u : G := g * t * g⁻¹
  have huI : IsInvolution u := by
    simpa [u] using OddCommutators.isInvolution_conjugate htI g
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hS_le_C : (S : Subgroup G) ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htCentral s hs
  let SC : Sylow 2 C := S.subtype hS_le_C
  have huC : u ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  let uC : C := ⟨u, huC⟩
  have huC_order : orderOf uC = 2 := by
    rw [← Subgroup.orderOf_coe uC]
    exact orderOf_eq_two (by simpa [pow_two] using huI.2) huI.1
  have hzp_uC : IsPGroup 2 (Subgroup.zpowers uC : Subgroup C) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, huC_order]
  obtain ⟨T, huC_T⟩ := hzp_uC.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T SC
  have huC_mem_T : uC ∈ (T : Subgroup C) :=
    huC_T (Subgroup.mem_zpowers uC)
  have hcu_mem_SC : c * uC * c⁻¹ ∈ (SC : Subgroup C) := by
    have hmem : c * uC * c⁻¹ ∈ ((c • T : Sylow 2 C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨uC, huC_mem_T, rfl⟩
    simpa [hc] using hmem
  have hcu_mem_S : (c : G) * u * (c : G)⁻¹ ∈ (S : Subgroup G) := by
    simpa [SC, Sylow.coe_subtype, Subgroup.mem_subgroupOf, uC] using hcu_mem_SC
  have hcg :
      ((c : G) * g) * t * ((c : G) * g)⁻¹ =
        (c : G) * u * (c : G)⁻¹ := by
    dsimp [u]
    group
  have hcu_eq_t : (c : G) * u * (c : G)⁻¹ = t := by
    have hmem :
        ((c : G) * g) * t * ((c : G) * g)⁻¹ ∈ (S : Subgroup G) := by
      rw [hcg]
      exact hcu_mem_S
    have hweak := htWeak.2 ((c : G) * g) hmem
    exact hcg.symm.trans hweak
  have hccomm : (c : G) * t = t * (c : G) := by
    have hcC : (c : G) ∈ C := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hcC
    exact hcC
  have hu_eq_t : u = t := by
    calc
      u = (c : G)⁻¹ * ((c : G) * u * (c : G)⁻¹) * (c : G) := by group
      _ = (c : G)⁻¹ * t * (c : G) := by rw [hcu_eq_t]
      _ = (c : G)⁻¹ * (t * (c : G)) := by rw [mul_assoc]
      _ = (c : G)⁻¹ * ((c : G) * t) := by rw [← hccomm]
      _ = t := by simp
  simpa [u] using hu_eq_t

/-- Local Z*-data already force every product of `t` with a conjugate of `t`
to have odd order. -/
theorem orderOf_conjugate_mul_odd_of_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (g : G) :
    Odd (orderOf ((g * t * g⁻¹) * t)) :=
  orderOf_conjugate_mul_odd htI
    (isolated_of_central_weaklyClosed S t htI htCentral htWeak) g

/-- Local Z*-data force every commutator with `t` to have odd order. -/
theorem orderOf_commutator_odd_of_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (g : G) :
    Odd (orderOf (g * t * g⁻¹ * t⁻¹)) :=
  orderOf_commutator_odd htI
    (isolated_of_central_weaklyClosed S t htI htCentral htWeak) g

end Submission.ZStar
