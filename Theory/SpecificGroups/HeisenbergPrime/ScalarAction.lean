module
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The marked central action of a Heisenberg automorphism

Commutator coordinates identify the action on the central line with the
determinant of the rank-two action. In particular, identity and scalar
inversion both fix the center. A kernel transport retains the actual
homomorphism detecting the central quotient.

Source application: Aschbacher--Smith15.2.21(3), printed p.1114,
refs/quasithin.pdf, through SmallActionsSource.ExtraspecialAction.
The coordinate proof extends the calculation in InversionFixedPlane.
-/

public section
open Subgroup
open scoped commutatorElement
namespace HeisenbergPrime
variable {G : Type*} [Group G] {p : ℕ}

/-- The action on the central coordinate is the exterior square of the
marked rank-two action. -/
theorem center_coordinate_determinant (e : G ≃* HeisenbergPrime p) (t : MulAut G)
    (a b c d : ZMod p)
    (ha : ∀ x, (e (t x)).a = a * (e x).a + b * (e x).b)
    (hb : ∀ x, (e (t x)).b = c * (e x).a + d * (e x).b)
    (z : G) (hz : z ∈ center G) :
    (e (t z)).c = (a * d - b * c) * (e z).c := by
  let u := e.symm (⟨(e z).c, 0, 0⟩ : HeisenbergPrime p)
  let v := e.symm (⟨0, 1, 0⟩ : HeisenbergPrime p)
  have hzab := (mem_center_iff (e z)).mp (centerCongr e ⟨z,hz⟩).property
  have huv : ⁅u,v⁆ = z := by
    apply e.injective
    rw [map_commutatorElement,commutator_coordinates]
    ext <;> simp [u,v,hzab.1,hzab.2]
  calc
    (e (t z)).c = (e (t ⁅u,v⁆)).c := by rw [huv]
    _ = (e (t u)).a * (e (t v)).b - (e (t v)).a * (e (t u)).b := by
      rw [map_commutatorElement,map_commutatorElement,commutator_coordinates]
    _ = _ := by simp only [ha,hb,u,v,MulEquiv.apply_symm_apply]; ring

/-- An automorphism that is either the identity or inversion modulo the
center fixes the center, because the scalar sign has determinant one. -/
theorem fixes_center_of_scalar_mod_center (e : G ≃* HeisenbergPrime p) (t : MulAut G)
    (ht : (∀ x, t x * x⁻¹ ∈ center G) ∨ (∀ x, t x * x ∈ center G))
    (z : G) (hz : z ∈ center G) : t z = z := by
  have hzab := (mem_center_iff (e z)).mp (centerCongr e ⟨z,hz⟩).property
  have htzab := (mem_center_iff (e (t z))).mp
    (centerCongr e ((MulAut.characteristic (center G) t) ⟨z,hz⟩)).property
  apply e.injective
  apply HeisenbergPrime.ext (htzab.1.trans hzab.1.symm) (htzab.2.trans hzab.2.symm)
  rcases ht with ht | ht
  · have hab (x : G) : (e (t x)).a = (e x).a ∧ (e (t x)).b = (e x).b := by
      have h := (mem_center_iff (e (t x * x⁻¹))).mp (centerCongr e ⟨_,ht x⟩).property
      simpa only [map_mul,map_inv,mul_a,mul_b,inv_a,inv_b,add_neg_eq_zero] using h
    simpa using center_coordinate_determinant e t 1 0 0 1
      (fun x => by simpa using (hab x).1) (fun x => by simpa using (hab x).2) z hz
  · have hab (x : G) : (e (t x)).a = -(e x).a ∧ (e (t x)).b = -(e x).b := by
      have h := (mem_center_iff (e (t x * x))).mp (centerCongr e ⟨_,ht x⟩).property
      simpa only [map_mul,mul_a,mul_b,add_eq_zero_iff_eq_neg] using h
    simpa using center_coordinate_determinant e t (-1) 0 0 (-1)
      (fun x => by simpa using (hab x).1) (fun x => by simpa using (hab x).2) z hz

/-- The scalar action may be detected through any homomorphism whose
literal kernel is the center; its marking is retained in the transport. -/
theorem fixes_center_of_scalar_image {D : Type*} [Group D]
    (e : G ≃* HeisenbergPrime p) (t : MulAut G) (f : G →* D)
    (hk : f.ker = center G)
    (ht : (∀ x, f (t x) = f x) ∨ (∀ x, f (t x) = (f x)⁻¹))
    (z : G) (hz : z ∈ center G) : t z = z := by
  apply fixes_center_of_scalar_mod_center e t ?_ z hz
  rcases ht with ht | ht
  · left
    intro x
    rw [←hk]
    change f (t x * x⁻¹) = 1
    rw [map_mul,map_inv,ht,mul_inv_cancel]
  · right
    intro x
    rw [←hk]
    change f (t x * x) = 1
    rw [map_mul,ht,inv_mul_cancel]
end HeisenbergPrime
