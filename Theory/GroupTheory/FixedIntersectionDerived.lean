module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Derived containment from a fixed-intersection count

Let r belong to I and let commutation with r carry Q into a subgroup Z
centralizing Q. If C_Q(r)=Z, the commutator homomorphism from Q∩I to Z∩I
has kernel Z∩I. The equality |Q∩I|=|Z∩I|² makes this homomorphism
surjective, so Z∩I lies in the derived subgroup of I.

Only the relative centralizer and commutator containments are required.
The group containing Q need not itself have nilpotency class two. The
application takes I=C_R(a) and Z=Z(R) inside the original ambient group.

Source: the field-involution case of Aschbacher–Smith, Lemma 2.4.21(2),
printed p.536 of the manuscript of 1 March 2004.
-/

public section

namespace Theory.GroupTheory
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

theorem fixed_intersection_le_commutator_of_card_sq
    (Q Z I : Subgroup G) (r : G) (hr : r ∈ I)
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hkernel : Q ⊓ centralizer ({r} : Set G) = Z)
    (hcomm : ∀ q ∈ Q, ⁅q,r⁆ ∈ Z)
    (hc : Nat.card (Q ⊓ I : Subgroup G) = Nat.card (Z ⊓ I : Subgroup G) ^ 2) :
    Z ⊓ I ≤ ⁅I,I⁆ := by
  let C := Q ⊓ I
  let D := Z ⊓ I
  have hZQ : Z ≤ Q := hkernel.symm.le.trans inf_le_left
  have hDC : D ≤ C := inf_le_inf_right I hZQ
  let f : C →* D := {
    toFun q := ⟨⁅q.val,r⁆, hcomm q.val q.property.1, by
      rw [commutatorElement_def]
      exact I.mul_mem (I.mul_mem (I.mul_mem q.property.2 hr) (I.inv_mem q.property.2))
        (I.inv_mem hr)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' q p := by
      apply Subtype.ext
      change ⁅q.val * p.val,r⁆ = ⁅q.val,r⁆ * ⁅p.val,r⁆
      have hpZ := hcomm p.val p.property.1
      have hqp := mem_centralizer_iff.mp (hcentral hpZ) q.val q.property.1
      rw [commutatorElement_mul_left_eq_conj_mul,hqp]
      simp only [mul_inv_cancel_right]
      exact (mem_centralizer_iff.mp (hcentral hpZ) _
        (hZQ (hcomm q.val q.property.1))).symm }
  have hk : f.ker = D.subgroupOf C := by
    ext q
    change (⟨⁅q.val,r⁆,_⟩ : D) = 1 ↔ q.val ∈ D
    rw [Subtype.ext_iff]
    change ⁅q.val,r⁆ = 1 ↔ q.val ∈ Z ⊓ I
    rw [← hkernel, mem_inf, mem_inf, mem_centralizer_singleton_iff,
      commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨⟨q.property.1,h⟩,q.property.2⟩, fun h => h.1.2⟩
  have hcount := f.ker.card_mul_index
  rw [index_ker,hk,Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv] at hcount
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hcards : Nat.card f.range = Nat.card D := by
    change Nat.card C = Nat.card D ^ 2 at hc
    nlinarith
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp
    (Subgroup.eq_top_of_card_eq _ hcards)
  intro z hz
  obtain ⟨q,hq⟩ := hsurj ⟨z,hz⟩
  have he : ⁅q.val,r⁆ = z := congrArg Subtype.val hq
  exact he ▸ commutator_mem_commutator q.property.2 hr
end Theory.GroupTheory
