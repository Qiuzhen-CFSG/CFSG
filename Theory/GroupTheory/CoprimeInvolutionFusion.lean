module

public import Theory.GroupTheory.InvolutionPairCentralInvolution
public import Mathlib.GroupTheory.Index

/-!
# Involution fusion through an odd kernel

A surjective homomorphism with odd kernel reflects conjugacy of involutions.
For two involutions with the same image, their product lies in the kernel.
If they were not conjugate, its half-order power would be an involution in
that odd kernel. Lifting a conjugator reduces the general case to this one.

This is the elementary dihedral lifting argument used when passing through
the odd-core quotient in Janko–Thompson, Math. Z. 113 (1970), §4.
-/

namespace MonoidHom

/-- Two involutions with the same image under a map with odd kernel are conjugate. -/
public theorem isConj_of_map_eq_of_involutions_of_odd_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : f x = f y) : IsConj x y := by
  by_contra hn
  have hp : x * y ∈ f.ker := by
    change f (x * y) = 1
    rw [map_mul, hxy, ← map_mul]
    have hy2 : y * y = 1 := by simpa only [pow_two, hy] using pow_orderOf_eq_one y
    rw [hy2, map_one]
  have hu := (Theory.GroupTheory.half_order_involution_of_not_isConj x y hx hy hn).2.1
  have hd := f.ker.orderOf_dvd_natCard (f.ker.pow_mem hp (orderOf (x * y) / 2))
  rw [hu] at hd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hker hd

/-- Quotient conjugacy of involutions lifts through any finite odd kernel. -/
public theorem isConj_of_map_isConj_of_involutions_of_odd_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime 2 (Nat.card f.ker))
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : IsConj (f x) (f y)) : IsConj x y := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  obtain ⟨g, rfl⟩ := hf a
  have hm : f (MulAut.conj g x) = f y := by
    simpa only [MulAut.conj_apply, map_mul, map_inv] using ha
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans
    (f.isConj_of_map_eq_of_involutions_of_odd_ker hker
      ((MulAut.conj g).orderOf_eq x |>.trans hx) hy hm)

end MonoidHom
