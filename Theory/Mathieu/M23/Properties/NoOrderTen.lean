module
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport

/-!
# The absence of elements of order ten in M₂₃

Every involution centralizer has the certified order 2688, which is prime to 5.
An element of order 10 would belong to the centralizer of its fifth power,
contradicting that order. This uses the actual design carrier and its exhaustive
involution fusion, rather than an assumed character table.

Source: Aschbacher–Smith 5.2.21, printed p.657; the A₈ containing-model
inspection in A.3.12, pp.47–48.
-/

public section
open Subgroup
namespace Sporadic.Mathieu

/-- No involution centralizer in M₂₃ has order divisible by five. -/
theorem m23_involution_centralizer_not_five (t : M23) (ht : orderOf t = 2) :
    ¬ 5 ∣ Nat.card (centralizer ({t} : Set M23)) := by
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
  rw [Nat.card_congr e.toEquiv, M23Geometry.involutionRepresentative_centralizer_card]
  decide

/-- The native Mathieu group M₂₃ has no element of order ten. -/
theorem m23_orderOf_ne_ten (x : M23) : orderOf x ≠ 10 := by
  intro hx
  have ht : orderOf (x ^ 5) = 2 := by rw [orderOf_pow,hx]; decide
  let y : centralizer ({x ^ 5} : Set M23) :=
    ⟨x, mem_centralizer_singleton_iff.mpr ((Commute.refl x).pow_left 5).eq⟩
  have hy : orderOf y = 10 := (orderOf_coe y).symm.trans hx
  have hd := orderOf_dvd_natCard y
  rw [hy] at hd
  exact m23_involution_centralizer_not_five (x ^ 5) ht ((by decide : 5 ∣ 10).trans hd)

end Sporadic.Mathieu
