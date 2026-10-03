module
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic

/-!
# Involutions in a faithful C₅ semidirect C₄ group

Every involution in the semidirect product of C₅ by a faithfully acting
C₄ conjugates each element of the normal C₅ to its inverse. The action
homomorphism is the supplied injective homomorphism on the actual cyclic
models; no identification with a different semidirect product is assumed.

The right projection of an involution is nontrivial, since otherwise an
odd-order C₅ would contain it. Faithfulness makes its induced automorphism
of C₅ a nontrivial involution. The automorphism group of C₅ is cyclic, so
its unique involution is inversion. The semidirect multiplication formula
gives the claimed conjugation identity.

This is the quotient-group calculation used in David Parrott,
*A characterization of the Tits' simple group* (1972), pp.674–675,
for outer involutions before Lemma 3. The concrete models here match the
original quotient-model interface used in that application.
-/

private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C4 := Multiplicative (ZMod 4)

/-- Every involution of a faithful C₅ semidirect C₄ group inverts the normal C₅. -/
public theorem faithful_five_four_involution_inverts_left
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (y : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hy : orderOf y = 2) (x : Multiplicative (ZMod 5)) :
    y * SemidirectProduct.inl x * y⁻¹ = SemidirectProduct.inl x⁻¹ := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hright : y.right ^ 2 = 1 := by
    have hh := congrArg SemidirectProduct.right (hy ▸ pow_orderOf_eq_one y)
    simpa only [pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right] using hh
  have hrightne : y.right ≠ 1 := by
    intro heq
    have hyinl : y = SemidirectProduct.inl y.left := by
      ext <;> simp [heq]
    have hleftorder : orderOf y.left = 2 := by
      rw [hyinl, orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective] at hy
      exact hy
    have hd := orderOf_dvd_natCard (x := y.left)
    norm_num [hleftorder, C5] at hd
  have hφsquare : φ y.right ^ 2 = 1 := by rw [← map_pow, hright, map_one]
  have hφne : φ y.right ≠ 1 := by
    intro heq
    exact hrightne (hφ (heq.trans (map_one φ).symm))
  let eAut : MulAut C5 ≃* (ZMod 5)ˣ := by
    have hh := IsCyclic.mulAutMulEquiv C5
    have hC5 : Nat.card C5 = 5 := by
      change Nat.card (ZMod 5) = 5
      simp
    rw [hC5] at hh
    exact hh
  let : IsCyclic (MulAut C5) := isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let inversion : MulAut C5 := {
    toFun := Inv.inv
    invFun := Inv.inv
    left_inv := inv_inv
    right_inv := inv_inv
    map_mul' := by intro a b; simp [mul_comm] }
  have hinsquare : inversion ^ 2 = 1 := by
    ext a
    change (a⁻¹)⁻¹ = a
    exact inv_inv a
  have hinne : inversion ≠ 1 := by
    intro heq
    have hh := congrArg (fun a : MulAut C5 => Multiplicative.toAdd
      (a (Multiplicative.ofAdd (1 : ZMod 5)))) heq
    norm_num [inversion] at hh
    exact (by decide : (-1 : ZMod 5) ≠ 1) hh
  have hinv : φ y.right = inversion :=
    IsCyclic.eq_of_orderOf_eq_two (orderOf_eq_prime hφsquare hφne)
      (orderOf_eq_prime hinsquare hinne)
  have haction : φ y.right x = x⁻¹ := by rw [hinv]; rfl
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_mul,
      map_inv, haction, mul_assoc]
  · simp
