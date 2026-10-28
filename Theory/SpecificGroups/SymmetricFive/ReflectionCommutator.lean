module
public import Theory.SpecificGroups.Symmetric.InnerAutomorphisms
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic

/-!
# A transposition acting on an element of order four in S5

The displacement has order three when the transposition moves the square
of the order-four element. For an involutory automorphism of S5, three
dividing its full fixed-subgroup order forces its unique inner actor to
be a transposition. This identifies the extra fixed-cubic source condition
needed by the original HS mixed-product argument. No original ambient
relation or fixed-subgroup divisibility is asserted here.

The only pair certificate ranges over120 permutations and25 ordered swaps.
It does not enumerate automorphisms or subgroups.
-/
public noncomputable section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricFive

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem swap_four_certificate : ∀ c : Perm (Fin 5), c^4=1 → c^2≠1 →
    ∀ i j : Fin 5, swap i j * c^2 * (swap i j)⁻¹≠c^2 →
      (swap i j*c*(swap i j)⁻¹*c⁻¹)^3=1 ∧ swap i j*c*(swap i j)⁻¹*c⁻¹≠1 := by
  decide +kernel

/-- A transposition moving the square of an actual element of order four
has displacement of order three. -/
theorem transposition_four_displacement_order
    (a c : Perm (Fin 5)) (ha : a.IsSwap) (hc : orderOf c=4)
    (hmove : a*c^2*a⁻¹≠c^2) : orderOf (a*c*a⁻¹*c⁻¹)=3 := by
  obtain ⟨i,j,_,rfl⟩ := ha
  have hc4 : c^4=1 := hc ▸ pow_orderOf_eq_one c
  have hc2 : c^2≠1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hc] at hd
    norm_num at hd
  have hh := swap_four_certificate c hc4 hc2 i j hmove
  exact orderOf_eq_prime hh.1 hh.2

private theorem conj_injective : Function.Injective
    (MulAut.conj : Perm (Fin 5)→*MulAut (Perm (Fin 5))) := by
  intro a b he
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).injective
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun he (x : Perm (Fin 5))

private theorem involution_isSwap_of_three_dvd_centralizer (a : Perm (Fin 5))
    (ha : orderOf a=2) (h3 : 3∣Nat.card (centralizer ({a} : Set (Perm (Fin 5))))) :
    a.IsSwap := by
  obtain ⟨n,hn⟩ := Perm.cycleType_prime_order (σ:=a) (by rw [ha]; decide)
  have hb := a.sum_cycleType_le
  rw [hn,ha,Multiset.sum_replicate] at hb
  have hnl : n≤1 := by
    simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
    omega
  interval_cases n
  · apply Perm.isSwap_iff_cycleType.mpr
    simpa [ha] using hn
  · rw [Perm.nat_card_centralizer,hn,ha] at h3
    norm_num at h3

/-- A nontrivial involutory automorphism of S5 with a fixed subgroup whose
order is divisible by three is conjugation by an actual transposition. -/
theorem involutive_automorphism_transposition_of_fixed_three
    (α : MulAut (Perm (Fin 5))) (hα2 : α^2=1) (hα1 : α≠1)
    (h3 : 3∣Nat.card α.fixedSubgroup) :
    ∃ a : Perm (Fin 5), a.IsSwap ∧ α=MulAut.conj a := by
  obtain ⟨a,ha⟩ := Perm.conj_surjective_of_degree (by decide : 5≤5) (by decide) α
  have ha2 : a^2=1 := conj_injective (by rw [map_pow,ha,hα2,map_one])
  have ha1 : a≠1 := by
    intro he
    apply hα1
    rw [←ha,he,map_one]
  have hfix : α.fixedSubgroup=centralizer ({a} : Set (Perm (Fin 5))) := by
    ext x
    rw [MulAut.mem_fixedSubgroup,←ha,MulAut.conj_apply,mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.trans eq_comm
  refine ⟨a,involution_isSwap_of_three_dvd_centralizer a
    (orderOf_eq_prime ha2 ha1) ?_,ha.symm⟩
  rwa [←hfix]

/-- The same actual automorphism has cubic displacement on c when its
full fixed subgroup has three-part and it moves c squared. -/
theorem involutive_four_displacement_order_of_fixed_three
    (α : MulAut (Perm (Fin 5))) (hα2 : α^2=1)
    (h3 : 3∣Nat.card α.fixedSubgroup)
    (c : Perm (Fin 5)) (hc : orderOf c=4) (hmove : α (c^2)≠c^2) :
    orderOf (α c*c⁻¹)=3 := by
  have hα1 : α≠1 := fun he => hmove (by rw [he]; rfl)
  obtain ⟨a,ha,rfl⟩ := involutive_automorphism_transposition_of_fixed_three α hα2 hα1 h3
  exact transposition_four_displacement_order a c ha hc hmove

end Theory.SpecificGroups.SymmetricFive
