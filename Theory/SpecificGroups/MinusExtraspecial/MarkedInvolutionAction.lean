module

public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerGeometry
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The marked involution action in the minus-extraspecial group

The genuine quaternion–dihedral model has ten noncentral involutions.
Each is conjugate inside the core to its product with the central involution.
Transport along a group isomorphism gives these facts for any realization;
orbit-stabilizer then computes its centralizer in an overgroup transitive
on the noncentral involutions. Only the 32-element model is enumerated.

Source: Aschbacher, *Sporadic Groups* (1994), 8.3, 8.15 and 46.1–46.3,
printed pp.26–30 and 251.
-/

@[expose] public section

open Subgroup
namespace MinusExtraspecial

private theorem count_calculation : Fintype.card {x : Model //
    x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ quaternion z} = 10 := by
  decide +kernel

private theorem conjugator_calculation : ∀ u : Model,
    u ^ 2 = 1 → u ≠ 1 → u ≠ quaternion z →
    ∃ a : Model, a * u * a⁻¹ = quaternion z * u := by
  decide +kernel

variable {K : Type*} [Group K]

/-- The ten actual noncentral involutions of a minus-extraspecial group of order 32. -/
theorem noncentral_involutions_card_of_equiv (e : K ≃* Model) :
    Nat.card {x : K // orderOf x = 2 ∧ x ∉ center K} = 10 := by
  let f := e.toEquiv.subtypeEquiv (p := fun x => orderOf x = 2 ∧ x ∉ center K)
    (q := fun x => orderOf x = 2 ∧ x ∉ center Model) (fun x => by
      change (orderOf x = 2 ∧ x ∉ center K) ↔ (orderOf (e x) = 2 ∧ e x ∉ center Model)
      rw [e.orderOf_eq]
      exact and_congr_right fun _ => not_congr (MulEquivClass.apply_mem_center_iff e).symm)
  rw [Nat.card_congr f]
  have hp (x : Model) :
      (orderOf x = 2 ∧ x ∉ center Model) ↔
      (x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ quaternion z) := by
    rw [orderOf_eq_prime_iff, MinusExtraspecial.mem_center_iff]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight hp), Nat.card_eq_fintype_card]
  exact count_calculation

/-- The two lifts in a noncentral involution coset are conjugate inside the core. -/
theorem exists_conjugator_central_mul_of_equiv (e : K ≃* Model) {c u : K}
    (hc : c ∈ center K) (hc1 : c ≠ 1)
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1) (huc : u ≠ c) :
    ∃ a : K, a * u * a⁻¹ = c * u := by
  have hec : e c = quaternion z := by
    have h := (MinusExtraspecial.mem_center_iff (e c)).mp
      ((MulEquivClass.apply_mem_center_iff e).mpr hc)
    exact h.resolve_left (by simpa using hc1)
  obtain ⟨a, ha⟩ := conjugator_calculation (e u)
    (by simpa only [map_pow, map_one] using congrArg e hu)
    (by simpa using hu1)
    (by simpa only [← hec, e.injective.ne_iff] using huc)
  refine ⟨e.symm a, e.injective ?_⟩
  simpa only [map_mul, map_inv, e.apply_symm_apply, hec] using ha

/-- Orbit-stabilizer for a group transitive on the ten core involutions. -/
theorem card_centralizer_mul_ten_of_transitive
    {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [Q.Normal]
    (e : Q ≃* Model)
    (htrans : ∀ x y : Q, orderOf x = 2 → x ∉ center Q →
      orderOf y = 2 → y ∉ center Q → IsConj (x : H) (y : H))
    (u : Q) (hu : orderOf u = 2) (huZ : u ∉ center Q) :
    Nat.card (centralizer ({(u : H)} : Set H)) * 10 = Nat.card H := by
  let T := {x : Q // orderOf x = 2 ∧ x ∉ center Q}
  let O := MulAction.orbit (ConjAct H) (u : H)
  let f : T → O := fun x => ⟨x.val, ConjAct.mem_orbit_conjAct.mpr
    (htrans x.val u x.property.1 x.property.2 hu huZ)⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun t : O => (t : H)) h))
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := isConj_iff.mp (ConjAct.mem_orbit_conjAct.mp x.property).symm
    let a : MulAut Q := MulAut.conjNormal g
    have ha : orderOf (a u) = 2 := (a.orderOf_eq u).trans hu
    have haZ : a u ∉ center Q := by
      exact fun hc => huZ ((MulEquivClass.apply_mem_center_iff a).mp hc)
    exact ⟨⟨a u, ha, haZ⟩, Subtype.ext hg⟩
  have hO : Nat.card O = 10 :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm.trans
      (noncentral_involutions_card_of_equiv e)
  have hstab : Nat.card (centralizer ({(u : H)} : Set H)) =
      Nat.card (MulAction.stabilizer (ConjAct H) (u : H)) := by
    rw [centralizer_eq_comap_stabilizer]
    rfl
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) (u : H))
  rw [Nat.card_prod, ← hstab, hO, Nat.mul_comm] at h
  exact h

end MinusExtraspecial
