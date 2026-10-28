module
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Fintype.Perm

/-!
# Inverting a specified cubic above a symmetric-three quotient

For a surjection with two-group kernel onto S₃, every subgroup of order
three is Sylow and odd Hall. Its normalizer maps onto S₃, so a transposition
lifts to an inverter of that very subgroup. Factoring the lift as a product
of an element of the prescribed Sylow two-subgroup and an element of the
cubic retains its inversion action. No splitting or involutory lift is assumed.

The binary-triality application uses the central local factor and retains
both its original cubic and Sylow. Source: Aschbacher--Smith 5.1.13,
printed p.636, together with the ordinary Sylow normalizer lifting argument.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A specified cubic above an S₃ quotient is inverted from any specified Sylow two-subgroup. -/
theorem cubic_inverted_in_sylow_of_two_kernel
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (D : Subgroup G) (hD : Nat.card D = 3)
    (S : Sylow 2 G) : ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹ = d⁻¹ := by
  classical
  obtain ⟨k,hkcard⟩ := hk.exists_card_eq
  have hcard : Nat.card G = 3 * 2 ^ (k+1) := by
    have hh := f.ker.card_mul_index
    rw [index_eq_card,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_perm,Nat.card_fin,hkcard] at hh
    rw [←hh]
    norm_num [Nat.factorial,pow_succ]
    ring
  have hi : D.index = 2 ^ (k+1) := by
    have hh := D.card_mul_index
    rw [hD,hcard] at hh
    omega
  have hhall : IsHallSubgroup OddHall.oddPrimes D := by
    constructor
    · intro p hp
      rw [hD] at hp
      have he := Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_three
        (show p.val ∣ 3 ^ 1 by simpa using hp)
      change p.val ≠ 2
      omega
    · intro p hp hp2
      rw [hi] at hp
      exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)
  have hnot : ¬ 3 ∣ D.index := by
    rw [hi]
    exact fun hh => (by decide : (3:ℕ) ≠ 2)
      (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hh)
  let P : Sylow 3 G := (IsPGroup.of_card (p:=3) (n:=1) (by simpa using hD)).toSylow hnot
  have hinj : Function.Injective (f.comp D.subtype) := by
    apply (f.comp D.subtype).ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hd : Disjoint D f.ker := by
      apply disjoint_of_coprime_natCard
      rw [hD,hkcard]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property hx)
  let E := D.map f
  have hEc : Nat.card E = 3 := by
    change Nat.card (D.map f) = 3
    rw [←range_subtype D,←MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hD
  have hEi : E.index = 2 := by
    have hh := E.card_mul_index
    rw [hEc,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let : E.Normal := E.normal_of_index_eq_two hEi
  have hN : (normalizer (D : Set G)).map f = ⊤ := by
    have hh := P.normalizer_map_surjective f hf
    change (normalizer (D : Set G)).map f = normalizer (E : Set _) at hh
    exact hh.trans (normalizer_eq_top E)
  let w : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  obtain ⟨g,hg,hfg⟩ := mem_map.mp (hN.ge (show w ∈ (⊤ : Subgroup _) from trivial))
  have hgInv : ∀ d ∈ D, g*d*g⁻¹ = d⁻¹ := by
    intro d hd
    have hc : (f d)^3 = 1 := by
      rw [←map_pow]
      have hh := pow_card_eq_one' (x := (⟨d,hd⟩ : D))
      rw [hD] at hh
      simpa using congrArg (fun x : D => f x) hh
    have hm : ∀ x : Equiv.Perm (Fin 3), x^3=1 → w*x*w⁻¹=x⁻¹ := by decide +kernel
    apply congrArg Subtype.val (hinj (a₁ := ⟨g*d*g⁻¹,mem_normalizer_iff.mp hg d |>.mp hd⟩)
      (a₂ := ⟨d⁻¹,D.inv_mem hd⟩) ?_)
    change f (g*d*g⁻¹) = f (d⁻¹)
    rw [map_mul,map_mul,map_inv,map_inv,hfg]
    exact hm _ hc
  obtain ⟨⟨t,a⟩,hta⟩ := (OddHall.sylow_complement_of_hall S hhall).2 g
  have he : g = (t:G)*(a:G) := hta.symm
  let : IsCyclic D := isCyclic_of_prime_card hD
  let : IsMulCommutative D := inferInstance
  refine ⟨t,t.property,?_⟩
  intro d hd
  have hcomm : (a:G)*d=d*(a:G) := congrArg Subtype.val (mul_comm' a (⟨d,hd⟩ : D))
  have hh := hgInv d hd
  rw [he,mul_inv_rev] at hh
  simpa only [mul_assoc,hcomm,mul_inv_cancel_left,mul_inv_cancel_right] using hh
end Subgroup
