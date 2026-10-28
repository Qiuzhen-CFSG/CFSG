module

public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Inner involutions in a faithful irreducible binary action

Let a centerless normal subgroup act irreducibly. An ambient element of
square one inducing an inner automorphism of that subgroup belongs to it.
Indeed the inner representative also has square one and commutes with the
ambient element. Their quotient is a centralizing element of square one,
which acts trivially by the binary Schur argument and is trivial by faithfulness.

This supplies the placement step before using component involution
calculations in Aschbacher–Smith, 15.3.58, printed p.1149.
-/

public section
namespace Representation.BinaryIrreducibleCentralizer
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    [IsIrreducible (ρ.comp K.subtype)]

/-- Inner conjugation places an ambient involution in the actual normal subgroup. -/
theorem inner_square_one_mem (hf : Function.Injective ρ) (hc : center K = ⊥)
    {v : G} (hv : v ^ 2 = 1)
    (hi : ∃ k : K, MulAut.conjNormal (H := K) v = MulAut.conj k) : v ∈ K := by
  obtain ⟨k, hk⟩ := hi
  have hk2 : k ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hc
    rw [map_pow, ← hk, ← map_pow, hv, map_one, map_one]
  have hvk : Commute v (k : G) := by
    have he := congrArg (fun a : MulAut K => (a k : G)) hk
    change v * k * v⁻¹ = k * k * (k : G)⁻¹ at he
    rw [mul_inv_cancel_right] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hx2 : (v * (k : G)⁻¹) ^ 2 = 1 := by
    rw [hvk.inv_right.mul_pow, hv, inv_pow]
    have hk2' : (k : G) ^ 2 = 1 := congrArg K.subtype hk2
    rw [hk2', inv_one, mul_one]
  have hxc : v * (k : G)⁻¹ ∈ centralizer (K : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    change MulAut.conjNormal (H := K) (v * (k : G)⁻¹) = 1
    rw [map_mul, map_inv, MulAut.conjNormal_val, hk, mul_inv_cancel]
  have he := centralizing_square_one_eq_one ρ K hf hx2 hxc
  exact (mul_inv_eq_one.mp he) ▸ k.property

end Representation.BinaryIrreducibleCentralizer
