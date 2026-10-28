module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import Theory.Alternating.Aut
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Excluding all alternating central quotients

An ordinary PSL₃(2) fixed component supplies an element of order seven.
For degree at most six, seven does not divide the whole symmetric-group
order. For degrees seven and eight, every automorphism of the alternating
group is induced by a permutation. An involutory automorphism comes from
an involution, and its centralizer order is a product of powers of two and
factorials of numbers below seven. Thus its fixed subgroup has no element
of order seven.

This eliminates the entire alternating constructor of Theorem C, including
the exceptional automorphisms in degree six without classifying them.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137; Theorem C,
p.33. The automorphism theorem is GLS3, Theorem 5.2.1, proved in
`Theory.Alternating.Aut`; the remaining argument is permutation counting.
-/

public section

open Subgroup Theory.GroupTheory Equiv.Perm
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

private theorem seven_not_dvd_centralizer {n : ℕ} (hn : n ≤ 8)
    (t : Equiv.Perm (Fin n)) (ht : orderOf t = 2) :
    ¬ 7 ∣ Nat.card (centralizer ({t} : Set (Equiv.Perm (Fin n)))) := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (ht ▸ Nat.prime_two)
  rw [ht] at hk
  have hbound := t.sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hkbound : k ≤ 3 := by omega
  rw [nat_card_centralizer, hk]
  interval_cases n <;> interval_cases k <;> norm_num at *

private theorem seven_not_dvd_fixed_alternating {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hn8 : n ≤ 8) (a : MulAut (alternatingGroup (Fin n))) (ha : orderOf a = 2) :
    ¬ 7 ∣ Nat.card a.fixedSubgroup := by
  obtain ⟨t, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).surjective a
  have ht : orderOf t = 2 := (orderOf_injective
    (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).injective t).symm.trans ha
  let f : (MulAut.conjNormal (H := alternatingGroup (Fin n)) t).fixedSubgroup →*
      centralizer ({t} : Set (Equiv.Perm (Fin n))) := {
    toFun := fun x => ⟨(x : alternatingGroup (Fin n)), by
      apply mem_centralizer_singleton_iff.mpr
      have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
      change t * (x : alternatingGroup (Fin n)) * t⁻¹ = (x : alternatingGroup (Fin n)) at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : centralizer ({t} : Set (Equiv.Perm (Fin n))) => (z : Equiv.Perm (Fin n))) h))
  exact fun h => seven_not_dvd_centralizer hn8 t ht (h.trans (card_dvd_of_injective f hi))

universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- No alternating entry of Theorem C has the required fixed component. -/
theorem SimpleInput.not_alternating {n : ℕ} (hn : n ≤ 8) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have hseven : 7 ∣ Nat.card s.involution.fixedSubgroup := by
    have hD : Nat.card s.component = 168 :=
      (Nat.card_congr s.equiv.toEquiv).trans Matrix.PSL3Two.card_PSL
    exact (by rw [hD]; norm_num : 7 ∣ Nat.card s.component).trans
      s.component.card_subgroup_dvd_card
  by_cases hsmall : n ≤ 6
  · have hs : 7 ∣ Nat.card S := hseven.trans s.involution.fixedSubgroup.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv] at hs
    have hd := (hs.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card)
    rw [Nat.card_perm, Nat.card_fin] at hd
    have h := hd.trans (Nat.factorial_dvd_factorial hsmall)
    norm_num at h
  · have ho : orderOf (MulAut.congr e s.involution) = 2 :=
      (MulEquiv.orderOf_eq _ _).trans s.involution_order
    apply seven_not_dvd_fixed_alternating (by omega) (by omega) hn _ ho
    rwa [← Nat.card_congr (MulAut.fixedSubgroupCongr e s.involution).toEquiv]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
