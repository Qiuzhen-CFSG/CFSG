module
public import Theory.GroupTheory.OddKernelInvolutionFibers
/-!
# Involution conjugacy through an odd kernel

A homomorphism with odd kernel preserves the order of an involution.
For a surjective homomorphism, conjugacy of involution images lifts to
conjugacy: lift the quotient conjugator and correct inside the kernel
using the odd dihedral product. The cubic-normalizer consumer applies
this to its literal order81 kernel and A₆ quotient.
-/
public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

omit [Finite G] in
theorem orderOf_map_involution_of_odd_kernel (f : G →* H)
    (hker : Nat.Coprime 2 (Nat.card f.ker)) {a : G} (ha : orderOf a = 2) :
    orderOf (f a) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  · intro he
    have hm : a ∈ f.ker := he
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hker)
      (ha ▸ f.ker.orderOf_dvd_natCard hm)

theorem isConj_of_map_involutions_of_odd_kernel (f : G →* H)
    (hf : Function.Surjective f) (hker : Nat.Coprime 2 (Nat.card f.ker))
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : IsConj (f a) (f b)) : IsConj a b := by
  obtain ⟨r, hr⟩ := isConj_iff.mp hab
  obtain ⟨s, rfl⟩ := hf r
  have hs : f (s*a*s⁻¹) = f b := by simpa only [map_mul, map_inv] using hr
  obtain ⟨k,hk⟩ := involutions_same_image_conj_ker f hker
    (((MulAut.conj s).orderOf_eq a).trans ha) hb hs
  apply isConj_iff.mpr
  refine ⟨(k:G)*s, ?_⟩
  calc
    _ = (k:G)*(s*a*s⁻¹)*(k:G)⁻¹ := by group
    _ = b := hk
end Subgroup
