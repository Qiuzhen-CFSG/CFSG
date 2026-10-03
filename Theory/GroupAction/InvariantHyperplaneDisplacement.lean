module

public import Theory.GroupAction.FourthPowerFixed
public import Mathlib.GroupTheory.Index

/-!
# Displacement onto an invariant binary hyperplane

An automorphism of fourth power one with exactly two fixed points has
its displacement image equal to every invariant subgroup of index two.
Invariance puts the displacement in the hyperplane; the kernel count
then proves equality. This is the coordinate-free hyperplane calculation
used in Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 676.
-/

open Subgroup
open scoped IsMulCommutative
namespace MulAut
/-- The displacement image is the invariant hyperplane. -/
public theorem displacement_range_eq_of_invariant_index_two
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : MulAut W) (ha4 : a ^ 4 = 1)
    (hfixed : Nat.card (FixedPoints.subgroup (zpowers a) W) = 2)
    (U : Subgroup W) (hU : U.index = 2)
    (hstable : ∀ u ∈ U, a u ∈ U) :
    ∃ s : W →* W, (∀ w, s w = a w * w) ∧ s.range = U := by
  have hself (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hinv (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (hself w)
  have hfour (w : W) : a (a (a (a w))) = w :=
    congrArg (fun f : MulAut W => f w) ha4
  let s : W →* W := {
    toFun := fun w => a w * w
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul]; ac_rfl }
  have hker : s.ker = FixedPoints.subgroup (zpowers a) W := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixed_zpowers_iff]
    change a w * w = 1 ↔ a w = w
    rw [mul_eq_one_iff_eq_inv, hinv]
  have hle : s.range ≤ U := by
    rintro _ ⟨w, rfl⟩
    apply (U.mul_mem_iff_of_index_two hU).mpr
    constructor
    · intro hw
      simpa only [hfour] using hstable _ (hstable _ (hstable _ hw))
    · exact hstable w
  refine ⟨s, fun _ => rfl, eq_of_le_of_card_ge hle ?_⟩
  have hs := s.ker.card_mul_index
  rw [index_ker, hker, hfixed] at hs
  have hu := U.card_mul_index
  rw [hU] at hu
  omega
/-- Displacements of an invariant binary hyperplane are fixed by the square
of the actor. -/
public theorem displacement_square_fixed_of_invariant_index_two
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : MulAut W) (ha4 : a ^ 4 = 1)
    (hfixed : Nat.card (FixedPoints.subgroup (zpowers a) W) = 2)
    (U : Subgroup W) (hU : U.index = 2)
    (hstable : ∀ u ∈ U, a u ∈ U) :
    ∀ u ∈ U, a (a (a u * u)) = a u * u := by
  obtain ⟨s, hs, hrange⟩ := displacement_range_eq_of_invariant_index_two
    a ha4 hfixed U hU hstable
  have hself (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hfour (w : W) : a (a (a (a w))) = w :=
    congrArg (fun f : MulAut W => f w) ha4
  intro u hu
  obtain ⟨v, rfl⟩ := hrange.symm ▸ hu
  have hd : a (s v) * s v = a (a v) * v := by
    rw [hs, map_mul]
    calc
      _ = (a (a v) * v) * (a v * a v) := by ac_rfl
      _ = _ := by rw [hself, mul_one]
  rw [hd, map_mul, map_mul, hfour]
  exact mul_comm _ _

end MulAut
