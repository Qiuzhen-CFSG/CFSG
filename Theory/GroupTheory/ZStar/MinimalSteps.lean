module

public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.QuaternionSylowCentrality
public import Theory.GroupTheory.ZStar.CyclicCase
public import Theory.GroupTheory.ZStar.OddCore

/-!
# The unique Sylow involution reduction for Z-star

A finite two-group with a unique involution is cyclic or generalized quaternion.
Burnside transfer settles the cyclic case. In the quaternion case, even order
of the center modulo the odd core implies quotient centrality of the involution.
Triviality of the odd core then implies centrality in the original group.

This extracts the group-theoretic reduction from
`Glauberman/ZStar/MinimalSteps.lean`, using Huppert III.8.2 and the elementary
Peterfalvi Appendix II quotient bridge. Brauer–Suzuki supplies the even-center
conclusion in the quaternion case. The unconditional endpoints are re-exported
by the historical module; the conditional reduction also remains available.
-/

namespace Glauberman.ZStar

open Subgroup BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

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
public theorem central_of_unique_sylow_involution_corefree_of_quaternion_center_even
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (hunique : ∀ x : G, x ∈ (S : Subgroup G) →
      IsInvolution x → x = t)
    (hquaternionCenter : ∀ n : ℕ, 3 ≤ n →
      Nonempty (S ≃* QuaternionGroup (2 ^ (n - 2))) →
      2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G))) :
    t ∈ Subgroup.center G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htOrder : orderOf t = 2 := orderOf_eq_prime htI.2 htI.1
  let tS : S := ⟨t, htS⟩
  have htSOrder : orderOf tS = 2 := by
    rw [← Subgroup.orderOf_coe tS]
    exact htOrder
  have huniqueS : ∃! x : S, orderOf x = 2 := by
    refine ⟨tS, htSOrder, ?_⟩
    intro x hx
    apply Subtype.ext
    apply hunique x x.property
    have hxG : orderOf (x : G) = 2 := by
      simpa only [Subgroup.orderOf_coe] using hx
    exact ⟨(orderOf_eq_prime_iff.mp hxG).2, (orderOf_eq_prime_iff.mp hxG).1⟩
  rcases S.isPGroup'.isCyclic_or_quaternion_of_unique_involution huniqueS with
    hcyclic | hquaternion
  · rcases cyclic_case t S hcyclic with
      ⟨N, hNnormal, hNodd, hcomm⟩
    have hNle : N ≤ pPrimeCore 2 G := by
      exact le_sSup ⟨hNnormal, (Nat.coprime_two_left.mpr hNodd)⟩
    rw [hcore] at hNle
    apply central_of_mem_bot_commutators
    intro g
    exact hNle (hcomm g)
  · rcases hquaternion with ⟨n, hn, hquat⟩
    have hcenter := BenderSuzuki.PFAppendixII.quotient_involution_central_of_even_center
      S hquat (hquaternionCenter n hn hquat) t htI
    apply central_of_mem_bot_commutators
    intro g
    have hg := commutators_mem_of_mem_center_quotient hcenter g
    simpa only [hcore] using hg

/-- If the Sylow `2`-subgroup has only one involution, that involution is
central in a core-free group. -/
public theorem central_of_unique_sylow_involution_corefree
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (hunique : ∀ x : G, x ∈ (S : Subgroup G) →
      IsInvolution x → x = t) :
    t ∈ Subgroup.center G := by
  exact central_of_unique_sylow_involution_corefree_of_quaternion_center_even
    hcore S t htI htS hunique
    (fun _ hn hS => even_card_center_quotient_pPrimeCore_of_quaternion_sylow S hn hS)

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


end Glauberman.ZStar
