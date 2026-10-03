module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Fixed points of a center-preserving extraspecial involution

A nonidentity involutive automorphism of an extraspecial group of order
27 which fixes its center pointwise has exactly that center as its fixed
subgroup.

The fixed subgroup is proper and has order at most nine, so it is abelian.
In the odd-order fixed/inverted factorization, a fixed point commutes with
an inverted point: their commutator is central, and the automorphism both
fixes and inverts it. Odd order makes that commutator trivial. The fixed
subgroup therefore centralizes every group element and equals the center.

This elementary automorphism argument supplies the three fixed subgroups
in the center-preserving Klein-four exclusion used at the end of
Stellmacher (9.1), Journal of Algebra190 (1997), p.48. It avoids any matrix
or symplectic-group recognition.
-/
namespace MulAut
open scoped commutatorElement
public theorem fixed_eq_center_of_extraspecial27_involution
    {F : Type*} [Group F] [Finite F] [IsExtraspecial 3 F]
    (hF : Nat.card F = 27) (a : MulAut F) (ha : Function.Involutive a)
    (hne : a ≠ 1) (hcenter : ∀ z ∈ Subgroup.center F, a z = z) :
    fixedSubgroup a = Subgroup.center F := by
  let C := fixedSubgroup a
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hCne : C ≠ ⊤ := by
    intro hc
    apply hne
    ext x
    exact (mem_fixedSubgroup a x).mp (hc.ge (Subgroup.mem_top x))
  have hCab : IsMulCommutative C := by
    have hdvd : Nat.card C ∣ 3 ^ 3 := by
      simpa [hF] using C.card_subgroup_dvd_card
    obtain ⟨n,hn,hcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdvd
    have hnlt : n < 3 := by
      by_contra hh
      have heq : n = 3 := by omega
      have hcfull : Nat.card C = Nat.card F := by rw [hcard,heq,hF]; norm_num
      exact hCne (C.eq_top_of_card_eq hcfull)
    interval_cases n
    · have hc1 : Nat.card C = 1 := by simpa using hcard
      let _ : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hc1).1
      infer_instance
    · let _ : IsCyclic C := isCyclic_of_card_dvd_prime (p := 3) (by rw [hcard]; norm_num)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
  let _ := hCab
  let _ := IsExtraspecial.quotient_elementary_abelian 3 F
  have hcommcenter (x y : F) : ⁅x,y⁆ ∈ Subgroup.center F := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center F)) ⁅x,y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)
  have hfixed_inverted (c v : F) (hc : a c = c) (hv : a v = v⁻¹) : Commute c v := by
    have hcentral := hcommcenter c v
    have hh : a ⁅c,v⁆ = ⁅c,v⁆⁻¹ := by
      rw [map_commutatorElement, hc, hv, commutatorElement_inv_right, ← commutatorElement_inv]
      rw [Subgroup.mem_center_iff.mp ((Subgroup.center F).inv_mem hcentral) v⁻¹,
        mul_assoc, inv_mul_cancel, mul_one]
    rw [hcenter _ hcentral] at hh
    have hsquare : ⁅c,v⁆ ^ 2 = 1 := by
      rw [pow_two]
      calc
        ⁅c,v⁆ * ⁅c,v⁆ = ⁅c,v⁆⁻¹ * ⁅c,v⁆ := congrArg (fun x => x * ⁅c,v⁆) hh
        _ = 1 := inv_mul_cancel _
    have hc1 : ⁅c,v⁆ = 1 := hodd.coprime_two_right.pow_left_bijective.injective
      (hsquare.trans (one_pow 2).symm)
    exact commutatorElement_eq_one_iff_commute.mp hc1
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨⟨u,v⟩, ⟨hu,hv,huv⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a ha x
    have hcu : Commute c u := setLike_mul_comm (s := C) hc ((mem_fixedSubgroup a u).mpr hu)
    have hcv : Commute c v := hfixed_inverted c v ((mem_fixedSubgroup a c).mp hc) hv
    rw [← huv]
    exact (hcu.mul_right hcv).eq.symm
  · intro z hz
    exact (mem_fixedSubgroup a z).mpr (hcenter z hz)
end MulAut
