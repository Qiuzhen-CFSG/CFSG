module
public import Theory.Frattini.BinarySquares
/-!
# Frattini kernels for inner pointwise fixers

If the center of P has order two, every automorphism fixing P pointwise
and induced by an element of P has square one. The squares generate the
Frattini subgroup of a finite two-group, so a pointwise-fixing action of
such a group kills its Frattini subgroup. No faithfulness or ambient Sylow
hypothesis is needed for this elementary action argument.

Source: Aschbacher–Smith, proof of 2.5.20, printed pp.563–565.
-/
open Subgroup
namespace Theory.GroupAction
public theorem pointwise_inner_pow_two_of_center_card
    {K : Type*} [Group K] (P : Subgroup K) (hc : Nat.card (center P) = 2)
    (a : MulAut K) (ha : ∀ x ∈ P, a x = x)
    (hi : ∃ z ∈ P, a = MulAut.conj z) : a ^ 2 = 1 := by
  obtain ⟨z,hz,rfl⟩ := hi
  have hzC : (⟨z,hz⟩ : P) ∈ center P := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp (ha x x.property)).symm
  have hh := pow_card_eq_one' (x := (⟨⟨z,hz⟩,hzC⟩ : center P))
  rw [hc] at hh
  have hz2 : z ^ 2 = 1 := congrArg (fun x : center P => ((x : P) : K)) hh
  rw [← map_pow,hz2,map_one]
public theorem pointwise_inner_frattini_le_ker
    {A K : Type*} [Group A] [Finite A] [Group K] (hA : IsPGroup 2 A)
    (P : Subgroup K) (hc : Nat.card (center P) = 2)
    (hi : ∀ a : MulAut K, (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z)
    (α : A →* MulAut K) (hfix : ∀ a x, x ∈ P → α a x = x) :
    frattini A ≤ α.ker := by
  rw [hA.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨a,rfl⟩
  change α (a ^ 2) = 1
  rw [map_pow]
  exact pointwise_inner_pow_two_of_center_card P hc (α a) (hfix a) (hi _ (hfix a))
end Theory.GroupAction
