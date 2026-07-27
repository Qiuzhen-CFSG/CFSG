import Mathlib
import Submission.BrauerSuzuki
import Submission.CyclicCase
import Submission.FeitThompson.FinalTheorem
import Submission.ZStar.LocalReduction
import Submission.ZStar.OddCore

/-!
# Elementary minimal-counterexample steps for the Z*-argument

This file records the group-theoretic pieces of Glauberman's proof which do
not use modular characters.  In particular, a core-free group cannot have a
Sylow `2`-subgroup with only one involution unless the distinguished
involution is central.  The cyclic alternative uses Burnside transfer; the
generalized-quaternion alternative uses Brauer--Suzuki.
-/

namespace Submission.ZStar

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup of a core-free group has trivial odd core. -/
public theorem pPrimeCore_subgroup_eq_bot_of_normal
    (hcore : pPrimeCore 2 G = ⊥) (N : Subgroup G) (hN : N.Normal) :
    pPrimeCore 2 N = ⊥ := by
  letI : N.Normal := hN
  have hmapbot : (pPrimeCore 2 N).map N.subtype = ⊥ := by
    apply le_bot_iff.mp
    simpa [hcore] using
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal
        (G := G) (p := 2) N
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := pPrimeCore 2 N) (f := N.subtype) N.subtype_injective).mp hmapbot

omit [Finite G] in
private theorem central_of_mem_bot_commutators
    {t : G} (hcomm : ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ (⊥ : Subgroup G)) :
    t ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g * t * g⁻¹ * t⁻¹ = 1 := by
    simpa using hcomm g
  calc
    g * t = (g * t * g⁻¹ * t⁻¹) * (t * g) := by group
    _ = t * g := by rw [hg, one_mul]

/-- If the Sylow `2`-subgroup has only one involution, that involution is
central in a core-free group. -/
public theorem central_of_unique_sylow_involution_corefree
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (hunique : ∀ x : G, x ∈ (S : Subgroup G) →
      IsInvolution x → x = t) :
    t ∈ Subgroup.center G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htOrder : orderOf t = 2 := orderOf_eq_prime htI.2 htI.1
  have htwoS : 2 ∣ Nat.card (S : Subgroup G) := by
    have hdvd := (S : Subgroup G).orderOf_dvd_natCard htS
    rw [htOrder] at hdvd
    exact hdvd
  let tS : S := ⟨t, htS⟩
  let U : Subgroup S := Subgroup.zpowers tS
  have htSOrder : orderOf tS = 2 := by
    rw [← Subgroup.orderOf_coe tS]
    exact htOrder
  have hUcard : Nat.card U = 2 := by
    simp [U, Nat.card_zpowers, htSOrder]
  have huniqueU : ∀ V : Subgroup S, Nat.card V = 2 → V = U := by
    intro V hVcard
    have htwoV : 2 ∣ Nat.card V := by simp [hVcard]
    obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 htwoV
    have hvorderS : orderOf (v : S) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hvorder
    have hvI : IsInvolution (v : S) := by
      have hv := (orderOf_eq_prime_iff (x := (v : S)) (p := 2)).mp hvorderS
      exact ⟨hv.2, by simpa [pow_two] using hv.1⟩
    have hvorderG : orderOf (v : G) = 2 := by
      calc
        orderOf (v : G) = orderOf (v : S) :=
          Subgroup.orderOf_coe (G := G) (H := (S : Subgroup G)) (v : S)
        _ = 2 := hvorderS
    have hvIG : IsInvolution (v : G) := by
      have hv := (orderOf_eq_prime_iff (x := (v : G)) (p := 2)).mp hvorderG
      exact ⟨hv.2, by simpa [pow_two] using hv.1⟩
    have hv_eq_t : (v : G) = t := hunique (v : G) (v : S).2 hvIG
    have hv_eq_tS : v = tS := by
      apply Subtype.ext
      exact hv_eq_t
    have hzp_le : Subgroup.zpowers (v : S) ≤ V :=
      Subgroup.zpowers_le.mpr v.property
    rw [hv_eq_tS] at hzp_le
    exact (Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hUcard, hVcard])).symm
  have hclass :=
    BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      (G := S) (p := 2) Nat.prime_two S.isPGroup' ⟨U, hUcard, huniqueU⟩
  rcases hclass.2 rfl with hcyclic | hquaternion
  · rcases Submission.CyclicCase.cyclic_case t S hcyclic with
      ⟨N, hNnormal, hNodd, hcomm⟩
    have hNle : N ≤ pPrimeCore 2 G := by
      exact le_sSup ⟨hNnormal, (Nat.coprime_two_left.mpr hNodd)⟩
    rw [hcore] at hNle
    apply central_of_mem_bot_commutators
    intro g
    exact hNle (hcomm g)
  · rcases hquaternion with ⟨n, hn, hquat⟩
    have hcenter := Submission.BrauerSuzuki.brauer_suzuki
      n hn S hquat t htS htOrder
    have hoddCore_bot : Submission.BrauerSuzuki.oddCore G = ⊥ := by
      rw [Submission.BrauerSuzuki.oddCore_eq_pPrimeCore_two, hcore]
    have hcomm : ∀ g : G,
        g * t * g⁻¹ * t⁻¹ ∈ Submission.BrauerSuzuki.oddCore G := by
      intro g
      -- The quotient map in Brauer--Suzuki is the standard quotient map.
      apply commutators_mem_of_mem_center_quotient
      change QuotientGroup.mk' (Submission.BrauerSuzuki.oddCore G) t ∈
        Subgroup.center (G ⧸ Submission.BrauerSuzuki.oddCore G) at hcenter
      exact hcenter
    apply central_of_mem_bot_commutators
    intro g
    simpa [hoddCore_bot] using hcomm g

/-- In a core-free group, a noncentral isolated involution has a second
involution in its Sylow `2`-subgroup. -/
public theorem exists_second_involution_of_not_central_corefree
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htNotCentral : t ∉ Subgroup.center G) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧ IsInvolution s ∧ s ≠ t := by
  by_contra hno
  push Not at hno
  exact htNotCentral (central_of_unique_sylow_involution_corefree
    hcore S t htI htS hno)

end Submission.ZStar
