module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.OddSubgroups
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Involutions in the concrete M23

All involutions form one conjugacy class, and their number is
3 · 5 · 11 · 23 = 3795. Exhaustive Sylow fusion and the representative's
centralizer order 2688 give the count by the class equation. The independent
odd-order subgroup obstruction shows that no odd subgroup has order divisible
by this number. All statements concern the concrete design automorphism group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.21, printed p.657 (PDF p.674).
-/

namespace Sporadic.Mathieu.M23Geometry

open Subgroup

/-- The class equation reduces the involution census to fusion and one centralizer order. -/
public theorem involution_count_of_class_data (t : M23) (ht : orderOf t = 2)
    (hclass : ∀ x : M23, orderOf x = 2 → IsConj t x)
    (hcentralizer : Nat.card (centralizer ({t} : Set M23)) = 2688) :
    Nat.card {x : M23 // orderOf x = 2} = 3795 := by
  have he : ∀ x : M23, IsConj t x ↔ orderOf x = 2 := by
    intro x
    constructor
    · intro h
      obtain ⟨g, hg⟩ := isConj_iff.mp h
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq t).trans ht
    · exact hclass x
  have hc := ConjClasses.nat_card_carrier_mul_card_centralizer t
  change Nat.card {x : M23 // IsConj t x} * _ = _ at hc
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), hcentralizer, m23_order] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2688) hc

/-- The concrete Mathieu group M23 has exactly 3795 involutions. -/
public theorem involution_count : Nat.card {x : M23 // orderOf x = 2} = 3795 := by
  obtain ⟨t, ht, hc⟩ := exists_involution_centralizer_card
  exact involution_count_of_class_data t ht (fun x hx => involutions_isConj t x ht hx) hc

end Sporadic.Mathieu.M23Geometry
