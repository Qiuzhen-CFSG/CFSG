import Submission.ZStar.OddCore
import Submission.ZStar.PrincipalBlock

/-!
# Strong-induction assembly for the core-free Z*-argument

This file turns the minimal-counterexample theorem
`central_of_principalTwoBlockData_and_induction` into an unconditional
strong-induction adapter, conditional only on the existence of the narrow
principal-`2`-block package for every finite group.

No modular character theory is developed here.
-/

namespace Submission.ZStar

open Subgroup

universe u

/-- Odd order of every commutator with an involution implies that the
involution is isolated among its commuting conjugates. -/
theorem isolated_of_odd_commutators
    {G : Type u} [Group G] [Finite G]
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    ∀ g : G,
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
        g * t * g⁻¹ = t := by
  intro g hcomm
  let s : G := g * t * g⁻¹
  have hsI : IsInvolution s := by
    simpa [s] using OddCommutators.isInvolution_conjugate htI g
  have htInv : t⁻¹ = t :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  have hsSq : s * s = 1 := by simpa [pow_two] using hsI.2
  have htSq : t * t = 1 := by simpa [pow_two] using htI.2
  have hstSq : (s * t) * (s * t) = 1 := by
    calc
      (s * t) * (s * t) = s * (t * s) * t := by simp only [mul_assoc]
      _ = s * (s * t) * t := by rw [← hcomm]
      _ = (s * s) * (t * t) := by simp only [mul_assoc]
      _ = 1 := by rw [hsSq, htSq, one_mul]
  have hstOdd : Odd (orderOf (s * t)) := by
    simpa [s, htInv, mul_assoc] using hodd g
  have hstOne : s * t = 1 :=
    CharacterArgument.eq_one_of_sq_eq_one_of_orderOf_odd hstSq hstOdd
  calc
    g * t * g⁻¹ = s := rfl
    _ = (s * t) * t⁻¹ := by simp
    _ = t⁻¹ := by rw [hstOne, one_mul]
    _ = t := htInv

/-- The quotient by the odd core satisfies the Z* conclusion once block data
is available there and the conclusion is known for all groups smaller than
the original group.

The use of the original group's induction hypothesis is legitimate because
the odd-core quotient has cardinality at most that of the original group.
-/
theorem oddOrderZStarConclusion_of_quotientBlockData_and_induction
    {G : Type u} [Group G] [Finite G]
    (hblock : PrincipalTwoBlockData (G ⧸ oddCore G))
    (hIH : OddOrderZStarInductionHypothesis G)
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    OddOrderZStarConclusion G t := by
  classical
  let N : Subgroup G := oddCore G
  letI : N.Normal := oddCore_normal G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hNodd : Odd (Nat.card N) := by
    simpa [N] using oddCore_odd G
  have hqtI : IsInvolution (q t) := by
    constructor
    · intro hqtOne
      have htN : t ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x := t)).mp hqtOne
      have htOrder : orderOf t = 2 := orderOf_eq_prime htI.2 htI.1
      have htwoDvd : 2 ∣ Nat.card N := by
        simpa [htOrder] using N.orderOf_dvd_natCard htN
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr htwoDvd)
    · simpa [q, map_pow] using congrArg q htI.2
  have hoddQ : ∀ x : G ⧸ N,
      Odd (orderOf (x * q t * x⁻¹ * (q t)⁻¹)) := by
    intro x
    rcases QuotientGroup.mk'_surjective N x with ⟨g, rfl⟩
    change Odd (orderOf (q g * q t * (q g)⁻¹ * (q t)⁻¹))
    have hdvd :
        orderOf (q (g * t * g⁻¹ * t⁻¹)) ∣
          orderOf (g * t * g⁻¹ * t⁻¹) :=
      orderOf_map_dvd q (g * t * g⁻¹ * t⁻¹)
    simpa [map_mul] using Odd.of_dvd_nat (hodd g) hdvd
  have hisolatedQ : ∀ x : G ⧸ N,
      (x * q t * x⁻¹) * q t = q t * (x * q t * x⁻¹) →
        x * q t * x⁻¹ = q t :=
    isolated_of_odd_commutators (q t) hqtI hoddQ
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  obtain ⟨S, hqtS, hqtCentral, hqtWeak⟩ :=
    isolated_involution_local_data (q t)
      (by simpa [pow_two] using hqtI.2) hqtI.1 hisolatedQ
  have hQle : Nat.card (G ⧸ N) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective q (QuotientGroup.mk'_surjective N)
  have hIHQ : OddOrderZStarInductionHypothesis (G ⧸ N) := by
    intro H _ _ hHlt s hsI hsOdd
    exact hIH H (lt_of_lt_of_le hHlt hQle) s hsI hsOdd
  have hcoreQ : pPrimeCore 2 (G ⧸ N) = ⊥ := by
    simpa [N, oddCore] using
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := 2))
  have hcenter : q t ∈ Subgroup.center (G ⧸ N) :=
    central_of_principalTwoBlockData_and_induction
      (by simpa [N, oddCore] using hblock) hIHQ hcoreQ S (q t)
      hqtI hqtS hqtCentral hqtWeak
  simpa [OddOrderZStarConclusion, q, N, oddCore] using
    (conclusion_of_mem_center_oddCore (G := G) (t := t)
      (by simpa [q, N, oddCore] using hcenter))

/-- A family of principal-`2`-block packages for all finite groups proves the
odd-order-commutator form of Z* by strong induction on group cardinality. -/
theorem oddOrderZStarConclusion_of_principalTwoBlockDataFactory
    (hblock : ∀ (H : Type u) [Group H] [Finite H], PrincipalTwoBlockData H)
    {G : Type u} [Group G] [Finite G]
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    OddOrderZStarConclusion G t := by
  let P : ℕ → Prop := fun n ↦
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n →
      ∀ s : H, IsInvolution s →
        (∀ h : H, Odd (orderOf (h * s * h⁻¹ * s⁻¹))) →
          OddOrderZStarConclusion H s
  have hP : ∀ n : ℕ, (∀ m < n, P m) → P n := by
    intro n ih H _ _ hcard s hsI hsOdd
    have hIH : OddOrderZStarInductionHypothesis H := by
      intro K _ _ hKlt k hkI hkOdd
      exact ih (Nat.card K) (by simpa [hcard] using hKlt)
        K rfl k hkI hkOdd
    exact oddOrderZStarConclusion_of_quotientBlockData_and_induction
      (hblock (H ⧸ oddCore H)) hIH s hsI hsOdd
  have hmain : P (Nat.card G) := Nat.strong_induction_on (Nat.card G) hP
  exact hmain G rfl t htI hodd

/-- Existence, rather than a chosen family, of the principal block packages
is enough for the strong-induction assembly. -/
theorem oddOrderZStarConclusion_of_exists_principalTwoBlockData
    (hblock : ∀ (H : Type u) [Group H] [Finite H],
      Nonempty (PrincipalTwoBlockData H))
    {G : Type u} [Group G] [Finite G]
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    OddOrderZStarConclusion G t := by
  classical
  apply oddOrderZStarConclusion_of_principalTwoBlockDataFactory
    (fun H _ _ ↦ Classical.choice (hblock H)) t htI hodd

/-- Factory-based core-free Z*: this has exactly the conclusion and local
hypotheses of `glauberman_zstar_corefree`, with the modular construction
isolated in the single existence hypothesis `hblock`. -/
theorem glauberman_zstar_corefree_of_exists_principalTwoBlockData
    (hblock : ∀ (H : Type u) [Group H] [Finite H],
      Nonempty (PrincipalTwoBlockData H))
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    t ∈ Subgroup.center G := by
  classical
  let blockFactory : ∀ (H : Type u) [Group H] [Finite H],
      PrincipalTwoBlockData H :=
    fun H _ _ ↦ Classical.choice (hblock H)
  have hIH : OddOrderZStarInductionHypothesis G := by
    intro H _ _ _ s hsI hsOdd
    exact oddOrderZStarConclusion_of_principalTwoBlockDataFactory
      blockFactory s hsI hsOdd
  exact central_of_principalTwoBlockData_and_induction
    (blockFactory G) hIH hcore S t htI htS htCentral htWeak

end Submission.ZStar
