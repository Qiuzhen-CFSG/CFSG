module

public import Theory.GroupTheory.Commutator.CentralFourSurjectivity
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PGroup.CoprimeFrattiniFixedIndex
public import Theory.Representation.ExtraspecialThirtyTwoFixedIndex
public import Theory.Frattini.PGroup

/-!
# Central four-group actions and extraspecial quotients

Let T have order 64, center of order four, central commutators and central
squares. Assume every noncentral element has centralizer of order sixteen.
The commutator with any such element maps onto the center. Consequently,
quotienting by a central subgroup of order two introduces no new central
elements, and the quotient is extraspecial of order 32.

If a nonidentity element of the elementary abelian center acts trivially,
any action factors through one of these extraspecial quotients. The factor
action has exactly the same common central fixed points; a nontrivial
central action remains nontrivial. For an action on a finite odd-prime
`p`-group, coprime Frattini reduction preserves this nontriviality. The
extraspecial constituent bound on the elementary abelian Frattini quotient
then gives `p ^ 4` dividing the center-fixed index, and index divisibility
lifts this bound to the original group. The final intrinsic wrapper derives
central commutators and squares from the equality of Frattini and center.

The centralizer hypothesis is essential: the intrinsic special-group
identities alone also hold in the direct product of two quaternion groups,
whose central quotients need not be extraspecial.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p.386.
-/

open Subgroup
open scoped commutatorElement

namespace CentralFourCoprimeIndex

variable {T : Type*} [Group T] [Finite T]

/-- Every noncentral commutator row fills the center. -/
public theorem commutator_surjective
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hclass : commutator T ≤ center T)
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    (t : T) (ht : t ∉ center T) :
    Function.Surjective (centerCommutatorHom hclass t) := by
  let f := centerCommutatorHom hclass t
  have hker : Nat.card f.ker = 16 := by
    rw [centerCommutatorHom_ker]
    exact hcentralizer t ht
  have hcount := f.ker.index_mul_card
  rw [index_ker, hker, hcard] at hcount
  have hrange : Nat.card f.range = Nat.card (center T) := by omega
  exact f.range_eq_top.mp (f.range.eq_top_of_card_eq hrange)

/-- Quotienting by a central subgroup of order two introduces no new center. -/
public theorem quotient_center_eq_map
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hclass : commutator T ≤ center T)
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    (N : Subgroup T) [N.Normal] (hNcard : Nat.card N = 2) :
    center (T ⧸ N) = (center T).map (QuotientGroup.mk' N) := by
  let q := QuotientGroup.mk' N
  apply le_antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
    have ht : t ∈ center T := by
      by_contra ht
      have hsurj := commutator_surjective hcard hcenter hclass hcentralizer t ht
      have hle : center T ≤ N := by
        intro z hz
        obtain ⟨y, hy⟩ := hsurj ⟨z, hz⟩
        have hcomm : q ⁅t,y⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact (mem_center_iff.mp hx (q y)).symm
        have hmem : ⁅t,y⁆ ∈ N := (QuotientGroup.eq_one_iff _).mp hcomm
        have heq : ⁅t,y⁆ = z := congrArg Subtype.val hy
        exact heq ▸ hmem
      have hbound := card_le_of_le hle
      omega
    exact mem_map_of_mem q ht
  · rintro _ ⟨t, ht, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact (map_mul q s t).symm.trans
      ((congrArg q (mem_center_iff.mp ht s)).trans (map_mul q t s))

/-- Each quotient by a central subgroup of order two is extraspecial of order 32. -/
public theorem quotient_extraspecial
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hclass : commutator T ≤ center T)
    (hsquares : ∀ t : T, t ^ 2 ∈ center T)
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    (N : Subgroup T) [N.Normal] (hN : N ≤ center T) (hNcard : Nat.card N = 2) :
    IsExtraspecial 2 (T ⧸ N) ∧ Nat.card (T ⧸ N) = 32 := by
  let q := QuotientGroup.mk' N
  have hZ := quotient_center_eq_map hcard hcenter hclass hcentralizer N hNcard
  have hqcard : Nat.card (T ⧸ N) = 32 := by
    have hh := N.index_mul_card
    rw [hNcard, hcard] at hh
    change Nat.card (T ⧸ N) * 2 = 64 at hh
    omega
  have hZcard : Nat.card (center (T ⧸ N)) = 2 := by
    have hkcard : Nat.card (N.subgroupOf (center T)) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv).trans hNcard
    have hh := (N.subgroupOf (center T)).index_mul_card
    change N.relIndex (center T) * Nat.card (N.subgroupOf (center T)) = _ at hh
    have hrel : N.relIndex (center T) = Nat.card ((center T).map q) := by
      simpa only [q, QuotientGroup.ker_mk'] using relIndex_ker (center T) q
    rw [hkcard, hrel, hcenter, ← hZ] at hh
    omega
  have hquot : IsElementaryAbelian 2 ((T ⧸ N) ⧸ center (T ⧸ N)) := by
    refine {
      toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr ?_
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
    · have hmap : (commutator T).map q = commutator (T ⧸ N) := by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
        rfl
      rw [← hmap, hZ]
      exact map_mono hclass
    · intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction x using QuotientGroup.induction_on with
        | H t =>
          apply (QuotientGroup.eq_one_iff _).mpr
          rw [hZ]
          exact mem_map_of_mem q (hsquares t)
  refine ⟨{
    center_order_p := hZcard
    quotient_elementary_abelian := hquot
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }, hqcard⟩
  intro heq
  have hh : Nat.card (center (T ⧸ N)) = Nat.card (T ⧸ N) := by rw [heq, card_top]
  omega

/-- A central involution in the action kernel yields the extraspecial actor,
with the same common central fixed points and a nontrivial central action. -/
public theorem exists_extraspecial_action
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hclass : commutator T ≤ center T)
    (hsquares : ∀ t : T, t ^ 2 ∈ center T)
    [IsElementaryAbelian 2 (center T)]
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    {P : Type*} [Group P] (ρ : T →* MulAut P)
    (hkernel : ∃ z : T, z ∈ center T ∧ z ≠ 1 ∧ ρ z = 1)
    (hnontrivial : ¬ center T ≤ ρ.ker) :
    ∃ N : Subgroup T, ∃ hnormal : N.Normal,
      let := hnormal
      IsExtraspecial 2 (T ⧸ N) ∧ Nat.card (T ⧸ N) = 32 ∧
      ∃ σ : (T ⧸ N) →* MulAut P,
        σ.comp (QuotientGroup.mk' N) = ρ ∧
        ¬ center (T ⧸ N) ≤ σ.ker ∧
        ∀ x : P, (∀ t ∈ center T, ρ t x = x) ↔
          (∀ t ∈ center (T ⧸ N), σ t x = x) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hz1, hzker⟩ := hkernel
  let N := zpowers z
  have hN : N ≤ center T := zpowers_le.mpr hz
  have hnormal : N.Normal := ⟨by
    intro n hn t
    simpa only [mem_center_iff.mp (hN hn) t, mul_inv_cancel_right] using hn⟩
  let := hnormal
  have hNcard : Nat.card N = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hz1
  obtain ⟨hspecial, hquotcard⟩ :=
    quotient_extraspecial hcard hcenter hclass hsquares hcentralizer N hN hNcard
  have hNker : N ≤ ρ.ker := zpowers_le.mpr hzker
  let σ := QuotientGroup.lift N ρ hNker
  have hZ := quotient_center_eq_map hcard hcenter hclass hcentralizer N hNcard
  refine ⟨N, hnormal, hspecial, hquotcard, σ, ?_, ?_, ?_⟩
  · ext t x
    rfl
  · intro htrivial
    apply hnontrivial
    intro t ht
    have hh := htrivial (hZ ▸ mem_map_of_mem (QuotientGroup.mk' N) ht)
    exact hh
  · intro x
    constructor
    · intro hx t ht
      rw [hZ] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact hx s hs
    · intro hx t ht
      exact hx _ (hZ ▸ mem_map_of_mem (QuotientGroup.mk' N) ht)

/-- The extraspecial center-fixed index bound extends from elementary abelian
groups to arbitrary finite odd-prime groups by Frattini reduction. -/
public theorem extraspecial_fourth_pow_dvd_center_fixed_index
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K P : Type*} [Group K] [Finite K] [IsExtraspecial 2 K]
    [Group P] [Finite P] (hP : IsPGroup p P)
    (hcardK : Nat.card K = 32) (ρ : K →* MulAut P)
    (hnontrivial : ¬ center K ≤ ρ.ker) :
    letI : MulDistribMulAction K P := MulDistribMulAction.compHom P ρ
    p ^ 4 ∣ (FixedPoints.subgroup (center K) P).index := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini
  have hcop : Nat.Coprime (Nat.card K) p := by
    rw [hcardK]
    have h2p : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two
        (Fact.out : p.Prime)).mp hd).symm)
    exact h2p.pow_left 5
  have hnot := ρ.not_le_ker_frattini_action_of_coprime hP hcop (center K) hnontrivial
  exact (Representation.extraspecialThirtyTwo_fourth_pow_dvd_center_fixed_index_of_hom
    hp2 hcardK ((Subgroup.quotientAut (frattini P)).comp ρ) hnot).trans
      (ρ.fixedPointSubgroup_frattini_index_dvd (center K))

/-- The common central fixed subgroup has index divisible by `p ^ 4`.
The structural hypotheses suffice without further special-group identities. -/
public theorem fourth_pow_dvd_center_fixed_index
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hclass : commutator T ≤ center T)
    (hsquares : ∀ t : T, t ^ 2 ∈ center T)
    [IsElementaryAbelian 2 (center T)]
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : T →* MulAut P)
    (hkernel : ∃ z : T, z ∈ center T ∧ z ≠ 1 ∧ ρ z = 1)
    (hnontrivial : ¬ center T ≤ ρ.ker) :
    letI : MulDistribMulAction T P := MulDistribMulAction.compHom P ρ
    p ^ 4 ∣ (FixedPoints.subgroup (center T) P).index := by
  let : MulDistribMulAction T P := MulDistribMulAction.compHom P ρ
  obtain ⟨N, hnormal, hspecial, hquotcard, σ, _, hnot, hfixed⟩ :=
    exists_extraspecial_action hcard hcenter hclass hsquares hcentralizer ρ
      hkernel hnontrivial
  let := hnormal
  let := hspecial
  let : MulDistribMulAction (T ⧸ N) P := MulDistribMulAction.compHom P σ
  have hfixed_eq : FixedPoints.subgroup (center T) P =
      FixedPoints.subgroup (center (T ⧸ N)) P := by
    ext x
    change (∀ t : center T, ρ t x = x) ↔
      (∀ t : center (T ⧸ N), σ t x = x)
    simpa only [Subtype.forall] using hfixed x
  rw [hfixed_eq]
  exact extraspecial_fourth_pow_dvd_center_fixed_index hp2 hP hquotcard σ hnot

/-- Intrinsic Frattini-equals-center form of the fourth-power index bound.
In particular it applies when the center, commutator, Frattini, first omega
and square-generated subgroups are the same elementary abelian four-group. -/
public theorem fourth_pow_dvd_center_fixed_index_of_frattini_eq_center
    (hT : IsPGroup 2 T)
    (hcard : Nat.card T = 64) (hcenter : Nat.card (center T) = 4)
    (hfrattini : frattini T = center T)
    [IsElementaryAbelian 2 (center T)]
    (hcentralizer : ∀ t : T, t ∉ center T →
      Nat.card (centralizer ({t} : Set T)) = 16)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : T →* MulAut P)
    (hkernel : ∃ z : T, z ∈ center T ∧ z ≠ 1 ∧ ρ z = 1)
    (hnontrivial : ¬ center T ≤ ρ.ker) :
    letI : MulDistribMulAction T P := MulDistribMulAction.compHom P ρ
    p ^ 4 ∣ (FixedPoints.subgroup (center T) P).index := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  apply fourth_pow_dvd_center_fixed_index hcard hcenter
    (hfrattini ▸ commutator_le_frattini_of_isPGroup (p := 2))
    (fun t => hfrattini ▸ pth_power_mem_frattini_of_isPGroup (p := 2) t)
    hcentralizer hp2 hP ρ hkernel hnontrivial

end CentralFourCoprimeIndex
